"""Full unattended pipeline: generate data -> train to plateau -> generate
more data -> repeat, until more data stops helping — climbing an Elo ladder
against Stockfish as it goes.

**On-policy self-play (`--on-policy-from-round`).** Off-policy distillation
(Stockfish playing both sides) trains the student only on positions a
flawless Stockfish would reach, never on positions the student's *own*
mistakes lead it into -- so at deployment, the first small error drifts it
onto states it never trained on, and errors compound (the classic
behavioral-cloning covariate-shift problem; see the DAgger paper referenced
in README.md). From `--on-policy-from-round` onward, the round's self-play
games are instead played by the in-memory student itself (optionally with
MCTS/value lookahead -- same `--mcts-sims`/`--c-puct`/`--no-value-lookahead`
knobs used for evaluation, `--student-play-temp`-sampled so it doesn't
replay one line every game); Stockfish still analyses and labels every
position reached, exactly as before. Round 1 always uses Stockfish self-play
regardless of this flag, since a freshly-initialized (or freshly-warm-started
but still weak) student has nothing useful to play yet -- this mirrors
DAgger's own first iteration, which is pure expert rollout. Set
`--on-policy-from-round 1` to skip the bootstrap round entirely (e.g. when
resuming `--init-from` an already-decent checkpoint).

This nests two early-stopping loops:

  - **inner, per round** (`auto_train.train_until_plateau`): train epochs on
    the current dataset, gated on validation loss. See `auto_train.py` for
    why val_loss is the right per-round signal.
  - **outer, across rounds** (this file): after each round, run a dedicated
    Stockfish strength match on the round's best checkpoint and compare it
    to previous rounds. Validation loss is *not* reused as the outer
    metric — each round's dataset is bigger and covers different positions
    than the last, so val_loss numbers aren't comparable round-to-round the
    way they are within one round's fixed dataset. Measured playing
    strength against Stockfish is what's actually comparable across rounds,
    so that's what gates the outer loop.

**Elo curriculum.** A *fixed* Stockfish opponent is a bad outer-loop signal
on its own: once the student reliably beats it, every subsequent round
reports the same near-maximum score with nothing left to distinguish
"still improving" from "plateaued" — the ceiling is the opponent, not the
model. So the opponent's target `UCI_Elo` is a moving target, starting at
`--sf-elo-start` (Stockfish's practical floor is 1320): whenever the round's
best checkpoint scores >= `--promotion-score` against the current rung, the
target Elo rises by `--sf-elo-step`, up to `--sf-elo-max` (default 2400 —
FIDE's International Master threshold). Reaching and beating `--sf-elo-max`
is treated as success. Short of that, the outer loop's patience/plateau
tracking is scoped to the *current* rung (a promotion always resets it, and
isn't itself a "stall") — otherwise a level-up would look identical to a
plateau, since score legitimately drops back down against a harder
opponent.

The *model* is kept in memory across rounds (not reloaded from disk), so each
round warm-starts training from exactly where the previous round's best
checkpoint left off — this is the automated version of the "generate more
data, resume with --init-from" loop described in the README.

The *optimizer*, by contrast, is rebuilt fresh at the start of every round
(with a per-round-decayed learning rate). This is deliberate: at the end of a
round we roll the model back to that round's *best* weights (step 4), but the
Adam moment estimates left in the optimizer describe the *latest*, over-fit
weights from `--patience` epochs later. Carrying that stale momentum onto the
rolled-back weights nudges the next round off the good minimum on its very
first steps, and the error compounds every round — a slow regression rather
than a plateau. A fresh optimizer each round keeps momentum matched to the
weights it is actually training. AdamW (decoupled weight decay) plus the LR
decay further damp the immediate per-round overfitting.

Data accumulates: `--data-path` is appended to every round (like
generate_data.py does on its own) and the full file is re-encoded into
`dataset.npz` each round, so later rounds train on all self-play data
generated so far, not just the newest batch.

Stops when: (a) the student beats Stockfish at `--sf-elo-max` — success; or
(b) score against the current Elo rung hasn't improved by more than
`--round-min-delta` for `--round-patience` rounds — plateaued, likely
capacity-limited (bigger `--channels`/`--blocks` may help); or (c)
`--max-rounds` as a backstop.

Usage (run in the background, tail either log to watch progress):
    python auto_pipeline.py --data-path ../data/self_play.jsonl \
        --out-dir ../checkpoints/auto &
    tail -f ../checkpoints/auto/rounds.csv   # round-level strength trend + Elo rung
    tail -f ../checkpoints/auto/log.csv      # epoch-level training detail
"""

import argparse
import csv
import json
import random
import sys
import time
from pathlib import Path

import chess.engine
import mlx.core as mx
import mlx.nn as nn
import mlx.optimizers as optim
import numpy as np

from auto_train import run_strength_eval, train_until_plateau
from build_dataset import encode_jsonl_files
from generate_data import generate_game
from model import ChessNet
from train import load_dataset, loss_fn


def main():
    ap = argparse.ArgumentParser()
    # data generation (passed straight through to generate_game each round)
    ap.add_argument("--stockfish", default="stockfish")
    ap.add_argument("--games-per-round", type=int, default=100)
    ap.add_argument("--depth", type=int, default=8)
    ap.add_argument("--multipv", type=int, default=4)
    ap.add_argument("--max-plies", type=int, default=80)
    ap.add_argument("--opening-random-plies", type=int, default=8, help="random plies before Stockfish takes over; higher = more diverse openings = more new unique positions per round (counters fixed-teacher diversity saturation)")
    ap.add_argument("--softmax-temp-cp", type=float, default=150.0)
    ap.add_argument("--play-temp", type=float, default=0.7)
    ap.add_argument("--gen-threads", type=int, default=1)
    ap.add_argument("--data-path", default="../data/self_play.jsonl", help="grows across rounds (appended to)")
    ap.add_argument("--on-policy-from-round", type=int, default=2, help="starting at this round, self-play games are played by the in-memory student (on-policy) instead of Stockfish; Stockfish still labels every position. Round 1 always uses Stockfish self-play (no trained student yet). Set to 1 to go on-policy immediately (e.g. resuming --init-from a decent checkpoint). See module docstring.")
    ap.add_argument("--student-play-temp", type=float, default=1.0, help="temperature for sampling the student's on-policy move during data generation (0 = deterministic, which would replay the same game every round)")
    # model / inner (per-round) training loop
    ap.add_argument("--out-dir", default="../checkpoints/auto")
    ap.add_argument("--batch-size", type=int, default=256)
    ap.add_argument("--lr", type=float, default=1e-3, help="round-1 learning rate; decayed by --lr-decay each subsequent round")
    ap.add_argument("--lr-decay", type=float, default=0.9, help="per-round multiplier on --lr for warm-started fine-tuning (round r uses lr * lr_decay**(r-1), floored at --min-lr)")
    ap.add_argument("--min-lr", type=float, default=2e-4, help="floor for the per-round decayed learning rate")
    ap.add_argument("--weight-decay", type=float, default=1e-4, help="AdamW decoupled weight decay (regularization against the immediate per-round overfitting)")
    ap.add_argument("--channels", type=int, default=64)
    ap.add_argument("--blocks", type=int, default=4)
    ap.add_argument("--value-weight", type=float, default=1.0)
    ap.add_argument("--val-fraction", type=float, default=0.1)
    ap.add_argument("--seed", type=int, default=-1, help="self-play RNG seed; <0 (default) = system entropy so restarts don't replay identical games. A fixed seed is reproducible but offset by existing data on resume (see note in code).")
    ap.add_argument("--init-from", default=None, help="warm-start round 1 from an existing checkpoint")
    ap.add_argument("--max-epochs-per-round", type=int, default=100_000)
    ap.add_argument("--patience", type=int, default=10, help="epochs without a --min-delta val_loss gain before ending a round; the best checkpoint is reached in the first few warm-started epochs, so a large value just burns epochs overfitting")
    ap.add_argument("--min-delta", type=float, default=5e-4)
    ap.add_argument("--eval-every", type=int, default=25, help="epochs between in-round Stockfish checks (0=off)")
    ap.add_argument("--eval-games", type=int, default=12)
    ap.add_argument("--sf-movetime-ms", type=int, default=100)
    ap.add_argument("--no-value-lookahead", action="store_true")
    ap.add_argument("--mcts-sims", type=int, default=0, help="PUCT simulations per move during Stockfish eval (0=off; used for both in-round and end-of-round checks)")
    ap.add_argument("--c-puct", type=float, default=1.5, help="MCTS exploration constant")
    # outer (across-rounds) loop + Elo curriculum
    ap.add_argument("--max-rounds", type=int, default=1000, help="hard backstop, not the expected stop condition")
    ap.add_argument("--round-patience", type=int, default=5, help="rounds without progress at the current Elo rung before stopping")
    ap.add_argument("--round-min-delta", type=float, default=15.0, help="min Elo-gap improvement (within a rung) to reset round patience")
    ap.add_argument("--round-eval-games", type=int, default=20)
    ap.add_argument("--sf-elo-start", type=int, default=1350, help="starting Stockfish UCI_Elo target (floor is ~1320)")
    ap.add_argument("--sf-elo-step", type=int, default=100, help="Elo increase per level-up")
    ap.add_argument("--sf-elo-max", type=int, default=2400, help="top rung; beating this = success (2400 ~= FIDE IM)")
    ap.add_argument("--promotion-score", type=float, default=0.5, help="round score (win rate) needed to level up a rung")
    args = ap.parse_args()

    out_dir = Path(args.out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)
    data_path = Path(args.data_path)
    data_path.parent.mkdir(parents=True, exist_ok=True)
    dataset_path = out_dir / "dataset.npz"
    best_path = out_dir / "best.npz"
    latest_path = out_dir / "latest.npz"
    epoch_log_path = out_dir / "log.csv"
    round_log_path = out_dir / "rounds.csv"

    model = ChessNet(channels=args.channels, num_blocks=args.blocks)
    if args.init_from:
        model.load_weights(args.init_from)
    mx.eval(model.parameters())
    # The optimizer is (re)built per round inside the loop; see the module
    # docstring for why it must not persist across rounds. loss_and_grad only
    # closes over the model, so it is built once here.
    loss_and_grad = nn.value_and_grad(model, loss_fn)

    epoch_log_is_new = not epoch_log_path.exists()
    epoch_log = epoch_log_path.open("a", newline="")
    epoch_writer = csv.writer(epoch_log)
    if epoch_log_is_new:
        epoch_writer.writerow(
            ["round", "epoch", "train_loss", "val_loss", "val_policy_loss", "val_value_loss", "eval_score", "eval_elo_gap", "seconds"]
        )
        epoch_log.flush()

    round_log_is_new = not round_log_path.exists()
    round_log = round_log_path.open("a", newline="")
    round_writer = csv.writer(round_log)
    if round_log_is_new:
        round_writer.writerow(
            ["round", "sf_elo_target", "total_positions", "epochs_run", "best_val_loss", "round_eval_score", "round_eval_elo_gap", "leveled_up", "seconds"]
        )
        round_log.flush()

    gen_engine = chess.engine.SimpleEngine.popen_uci(args.stockfish)
    gen_engine.configure({"Threads": args.gen_threads})

    # Seed the self-play RNG so we never regenerate games we've already saved.
    # A *fixed* seed across runs is a trap: generate_game is deterministic given
    # this RNG (same random opening plies -> same fixed-depth Stockfish replies
    # -> same positions -> even the same game_id), so a resumed/restarted run
    # with the same seed replays byte-identical games. build_dataset then
    # de-duplicates them away, freezing the dataset round after round and
    # starving training. So: default to system entropy (--seed < 0), and even
    # when an explicit seed is given for reproducibility, offset it by how much
    # data is already on disk so a resume *continues* the sequence instead of
    # repeating it.
    if args.seed is not None and args.seed >= 0:
        existing_records = sum(1 for _ in data_path.open()) if data_path.exists() else 0
        rng = random.Random(f"{args.seed}-{existing_records}")
        print(f"== self-play RNG: deterministic seed={args.seed}, offset by {existing_records} existing records", flush=True)
    else:
        rng = random.Random()
        print("== self-play RNG: system entropy (non-deterministic; avoids replaying prior games)", flush=True)

    current_sf_elo = args.sf_elo_start
    best_gap_at_rung = float("-inf")
    rounds_since_improve = 0
    next_epoch = 1

    try:
        for round_idx in range(1, args.max_rounds + 1):
            round_t0 = time.time()

            # 1. generate more self-play data, appended to the same growing file.
            # From --on-policy-from-round onward the student itself plays both
            # sides (on-policy); Stockfish still labels every position either
            # way. See module docstring.
            on_policy = round_idx >= args.on_policy_from_round
            if on_policy:
                model.eval()
            print(
                f"== round {round_idx}: self-play mode = {'on-policy (student plays)' if on_policy else 'off-policy (Stockfish plays)'}",
                flush=True,
            )
            positions_added = 0
            with data_path.open("a") as f:
                for _ in range(args.games_per_round):
                    records = generate_game(
                        gen_engine,
                        multipv=args.multipv,
                        depth=args.depth,
                        max_plies=args.max_plies,
                        opening_random_plies=args.opening_random_plies,
                        softmax_temp_cp=args.softmax_temp_cp,
                        play_temp=args.play_temp,
                        rng=rng,
                        game_id=rng.getrandbits(63),  # unique per game -> whole-game train/val holdout
                        student_model=model if on_policy else None,
                        student_temp=args.student_play_temp,
                        mcts_sims=args.mcts_sims,
                        c_puct=args.c_puct,
                        use_value_lookahead=not args.no_value_lookahead,
                    )
                    for r in records:
                        f.write(json.dumps(r) + "\n")
                    positions_added += len(records)
                f.flush()

            # 2. rebuild the full dataset from all accumulated data so far
            # (de-duplicated by position; G groups positions by game so the
            # split below can hold out whole games — see build_dataset.py).
            X, P, V, G = encode_jsonl_files([str(data_path)])
            # Guardrail: the policy loss is a soft-target cross-entropy, which
            # is only bounded (>= 0) when every target row sums to 1. An
            # un-normalized row lets training drive the logits to +/-inf and
            # the loss to -inf -- silently, over many rounds. Fail loudly here
            # instead. (encode_jsonl_files normalizes and drops empty rows, so
            # this should always hold; it's a regression tripwire.)
            row_sums = P.sum(axis=1)
            n_bad = int((np.abs(row_sums - 1.0) > 1e-3).sum())
            if n_bad:
                raise ValueError(
                    f"{n_bad}/{len(row_sums)} policy target rows are not normalized "
                    f"(sum != 1; range [{row_sums.min():.4f}, {row_sums.max():.4f}]). "
                    "Un-normalized soft targets make the policy loss diverge -- "
                    "check build_dataset.encode_jsonl_files."
                )
            np.savez_compressed(dataset_path, X=X, P=P, V=V, G=G)
            (Xtr, Ptr, Vtr), (Xval, Pval, Vval) = load_dataset(str(dataset_path), args.val_fraction, args.seed)
            print(
                f"== round {round_idx}: +{positions_added} positions "
                f"(total {len(V)} unique, {len(np.unique(G))} game-groups) "
                f"train={Xtr.shape[0]} val={Xval.shape[0]}",
                flush=True,
            )

            # 3. train to plateau on this dataset, warm-started from the running
            # model but with a FRESH optimizer (see module docstring) whose
            # learning rate is decayed for later, fine-tuning rounds.
            round_lr = max(args.min_lr, args.lr * (args.lr_decay ** (round_idx - 1)))
            optimizer = optim.AdamW(learning_rate=round_lr, weight_decay=args.weight_decay)
            print(f"== round {round_idx}: lr={round_lr:.2e} weight_decay={args.weight_decay:g}", flush=True)
            result = train_until_plateau(
                model,
                optimizer,
                loss_and_grad,
                Xtr,
                Ptr,
                Vtr,
                Xval,
                Pval,
                Vval,
                batch_size=args.batch_size,
                value_weight=args.value_weight,
                max_epochs=args.max_epochs_per_round,
                patience=args.patience,
                min_delta=args.min_delta,
                eval_every=args.eval_every,
                eval_games=args.eval_games,
                stockfish=args.stockfish,
                sf_elo=current_sf_elo,
                sf_movetime_ms=args.sf_movetime_ms,
                use_value_lookahead=not args.no_value_lookahead,
                best_path=best_path,
                latest_path=latest_path,
                writer=epoch_writer,
                log_file=epoch_log,
                start_epoch=next_epoch,
                round_label=round_idx,
                mcts_sims=args.mcts_sims,
                c_puct=args.c_puct,
            )
            next_epoch = result["next_epoch"]

            # 4. dedicated end-of-round strength check on the round's *best*
            # checkpoint - this also resets the in-memory model to those
            # weights, which is what carries forward as next round's warm
            # start (dropping whatever extra, non-improving epochs training
            # ran through before patience triggered).
            elo_used = current_sf_elo  # rung this round was actually evaluated against
            model.load_weights(str(best_path))
            model.eval()
            round_score, round_elo_gap, round_results = run_strength_eval(
                model, args.stockfish, elo_used, args.sf_movetime_ms, args.round_eval_games,
                not args.no_value_lookahead, args.mcts_sims, args.c_puct,
            )

            round_dt = time.time() - round_t0
            beat_current_rung = round_score >= args.promotion_score
            at_top_rung = elo_used >= args.sf_elo_max

            # Elo curriculum: level up the opponent once the student beats
            # the current rung; a level-up always counts as progress (it
            # isn't a "stall" even though score/elo_gap will legitimately
            # drop back down against the harder opponent that follows).
            success = beat_current_rung and at_top_rung
            leveled_up = beat_current_rung and not at_top_rung
            if leveled_up:
                current_sf_elo = min(elo_used + args.sf_elo_step, args.sf_elo_max)
                best_gap_at_rung = float("-inf")
                rounds_since_improve = 0
            elif round_elo_gap > best_gap_at_rung + args.round_min_delta:
                best_gap_at_rung = round_elo_gap
                rounds_since_improve = 0
            else:
                rounds_since_improve += 1

            round_writer.writerow(
                [
                    round_idx,
                    f"{elo_used}->{current_sf_elo}" if leveled_up else elo_used,
                    len(V),
                    result["epochs_run"],
                    f"{result['best_val_loss']:.5f}",
                    f"{round_score:.3f}",
                    f"{round_elo_gap:.0f}",
                    leveled_up,
                    f"{round_dt:.1f}",
                ]
            )
            round_log.flush()

            marker = "^" if leveled_up else ("*" if rounds_since_improve == 0 else " ")
            print(
                f"== round {round_idx} done: total_positions={len(V)} epochs={result['epochs_run']} "
                f"best_val_loss={result['best_val_loss']:.4f} vs SF@{elo_used}: {round_results} "
                f"score={round_score:.2f} elo_gap={round_elo_gap:+.0f}{marker} "
                f"round_stall={rounds_since_improve}/{args.round_patience} [{round_dt:.1f}s]",
                flush=True,
            )
            if leveled_up:
                print(f"== level up: beat SF@{elo_used} -> raising target to SF@{current_sf_elo}", flush=True)

            if success:
                print(
                    f"stopping: beat Stockfish@{args.sf_elo_max} (score={round_score:.2f}) - "
                    f"target reached (roughly FIDE IM strength). best checkpoint -> {best_path}",
                    flush=True,
                )
                break

            if rounds_since_improve >= args.round_patience:
                print(
                    f"stopping: no progress at SF@{current_sf_elo} for {args.round_patience} rounds "
                    f"(best elo_gap at this rung={best_gap_at_rung:+.0f}). "
                    f"Consider a bigger model (--channels/--blocks) to push past this. best checkpoint -> {best_path}",
                    flush=True,
                )
                break
        else:
            print(f"stopping: reached --max-rounds={args.max_rounds} without reaching --sf-elo-max or meeting the round-patience criterion", flush=True)
    finally:
        gen_engine.quit()
        epoch_log.close()
        round_log.close()

    print(
        f"epoch log: {epoch_log_path}\nround log: {round_log_path}\n"
        f"best checkpoint: {best_path}\nlatest checkpoint: {latest_path}\ndataset: {dataset_path}"
    )


if __name__ == "__main__":
    try:
        main()
    except KeyboardInterrupt:
        sys.exit(1)
