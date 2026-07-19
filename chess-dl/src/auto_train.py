"""Train ChessNet with early stopping: keep training epochs until the
validation loss stops meaningfully improving, so this can be kicked off in
the background and left alone for a long run.

Two metrics are tracked, deliberately for different jobs:
  - **val_loss** (every epoch, cheap) is what actually gates stopping. It's
    the standard early-stopping signal: fast to compute, deterministic, and
    a good proxy for "is the student still learning from the teacher."
  - **Stockfish match score** (every `--eval-every` epochs, expensive) is
    logged alongside it purely as a human-readable strength readout. It's
    too slow and too noisy (a handful of games has high variance) to use as
    the stopping condition itself, but it's the number you actually care
    about, so it's recorded in the log too.

Stopping rule: if val_loss hasn't improved by more than `--min-delta` for
`--patience` consecutive epochs, stop and keep the best checkpoint seen.
`--max-epochs` is a large backstop, not the expected way this ends.

The core loop lives in `train_until_plateau()` so `auto_pipeline.py` can
reuse it as the inner loop of a bigger generate-more-data-and-keep-going
orchestration; `main()` below is just a thin CLI over it for training on a
single, already-built dataset.

Usage (run in the background, tail the log to watch progress):
    python auto_train.py --data ../data/dataset.npz --out-dir ../checkpoints/auto &
    tail -f ../checkpoints/auto/log.csv
"""

import argparse
import csv
import sys
import time
from pathlib import Path

import chess.engine
import mlx.core as mx
import mlx.nn as nn
import mlx.optimizers as optim

from evaluate import play_game, score_to_elo_diff
from model import ChessNet
from train import iterate_batches, load_dataset, loss_fn


def run_strength_eval(model, stockfish_path, sf_elo, sf_movetime_ms, games, use_value):
    engine = chess.engine.SimpleEngine.popen_uci(stockfish_path)
    engine.configure({"UCI_LimitStrength": True, "UCI_Elo": sf_elo})
    limit = chess.engine.Limit(time=sf_movetime_ms / 1000.0)
    results = {"win": 0, "draw": 0, "loss": 0}
    try:
        for g in range(games):
            student_is_white = g % 2 == 0
            outcome = play_game(model, engine, student_is_white, limit, use_value)
            results[outcome] += 1
    finally:
        engine.quit()
    score = (results["win"] + 0.5 * results["draw"]) / games
    return score, score_to_elo_diff(score), results


def train_until_plateau(
    model,
    optimizer,
    loss_and_grad,
    Xtr,
    Ptr,
    Vtr,
    Xval,
    Pval,
    Vval,
    *,
    batch_size,
    value_weight,
    max_epochs,
    patience,
    min_delta,
    eval_every,
    eval_games,
    stockfish,
    sf_elo,
    sf_movetime_ms,
    use_value_lookahead,
    best_path,
    latest_path,
    writer,
    log_file,
    start_epoch=1,
    round_label="-",
):
    """Train `model` in place until val_loss plateaus.

    `model`/`optimizer` are trained in place and not reset here, so a caller
    (e.g. `auto_pipeline.py`) can call this repeatedly across growing
    datasets to warm-start each round from where the last one left off.
    `writer`/`log_file` are an open `csv.writer` and its underlying file, so
    a multi-round caller can share one running log across calls.

    Returns a dict with `best_val_loss`, `epochs_run`, and `next_epoch`.
    """
    best_val = float("inf")
    epochs_since_improve = 0
    epoch = start_epoch

    for i in range(max_epochs):
        epoch = start_epoch + i
        t0 = time.time()

        model.train()
        epoch_loss, nbatches = 0.0, 0
        for xb, pb, vb in iterate_batches(Xtr, Ptr, Vtr, batch_size, rng_key=epoch):
            (loss, _components), grads = loss_and_grad(model, xb, pb, vb, value_weight)
            optimizer.update(model, grads)
            mx.eval(model.parameters(), optimizer.state)
            epoch_loss += loss.item()
            nbatches += 1
        train_loss = epoch_loss / nbatches

        model.eval()
        val_loss, (val_ploss, val_vloss) = loss_fn(model, Xval, Pval, Vval, value_weight)
        val_loss, val_ploss, val_vloss = val_loss.item(), val_ploss.item(), val_vloss.item()

        improved = val_loss < best_val - min_delta
        if improved:
            best_val = val_loss
            epochs_since_improve = 0
            model.save_weights(str(best_path))
        else:
            epochs_since_improve += 1
        model.save_weights(str(latest_path))

        eval_score = eval_elo_gap = ""
        eval_note = ""
        if eval_every > 0 and epoch % eval_every == 0:
            score, elo_gap, results = run_strength_eval(
                model, stockfish, sf_elo, sf_movetime_ms, eval_games, use_value_lookahead
            )
            eval_score, eval_elo_gap = f"{score:.3f}", f"{elo_gap:.0f}"
            eval_note = f" | vs SF@{sf_elo}: {results} score={score:.2f} elo_gap={elo_gap:+.0f}"

        dt = time.time() - t0
        writer.writerow(
            [round_label, epoch, f"{train_loss:.5f}", f"{val_loss:.5f}", f"{val_ploss:.5f}", f"{val_vloss:.5f}", eval_score, eval_elo_gap, f"{dt:.1f}"]
        )
        log_file.flush()

        marker = "*" if improved else " "
        print(
            f"[round {round_label}] epoch {epoch} train={train_loss:.4f} val={val_loss:.4f}{marker} "
            f"best={best_val:.4f} stall={epochs_since_improve}/{patience} [{dt:.1f}s]{eval_note}",
            flush=True,
        )

        if epochs_since_improve >= patience:
            print(
                f"[round {round_label}] stopping: val_loss hasn't improved by >{min_delta} in {patience} epochs. "
                f"best val_loss={best_val:.4f} -> {best_path}",
                flush=True,
            )
            break
    else:
        print(f"[round {round_label}] stopping: reached --max-epochs={max_epochs} without meeting the patience criterion", flush=True)

    return {"best_val_loss": best_val, "epochs_run": epoch - start_epoch + 1, "next_epoch": epoch + 1}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--data", default="../data/dataset.npz")
    ap.add_argument("--out-dir", default="../checkpoints/auto")
    ap.add_argument("--batch-size", type=int, default=256)
    ap.add_argument("--lr", type=float, default=1e-3)
    ap.add_argument("--channels", type=int, default=64)
    ap.add_argument("--blocks", type=int, default=4)
    ap.add_argument("--value-weight", type=float, default=1.0)
    ap.add_argument("--val-fraction", type=float, default=0.1)
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--init-from", default=None, help="resume/fine-tune from an existing checkpoint")
    ap.add_argument("--max-epochs", type=int, default=100_000, help="hard backstop, not the expected stop condition")
    ap.add_argument("--patience", type=int, default=40, help="epochs without improvement before stopping")
    ap.add_argument("--min-delta", type=float, default=5e-4, help="minimum val_loss improvement to reset patience")
    ap.add_argument("--eval-every", type=int, default=25, help="epochs between Stockfish strength checks (0=off)")
    ap.add_argument("--eval-games", type=int, default=12)
    ap.add_argument("--stockfish", default="stockfish")
    ap.add_argument("--sf-elo", type=int, default=1350)
    ap.add_argument("--sf-movetime-ms", type=int, default=100)
    ap.add_argument("--no-value-lookahead", action="store_true")
    args = ap.parse_args()

    out_dir = Path(args.out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)
    best_path = out_dir / "best.npz"
    latest_path = out_dir / "latest.npz"
    log_path = out_dir / "log.csv"

    (Xtr, Ptr, Vtr), (Xval, Pval, Vval) = load_dataset(args.data, args.val_fraction, args.seed)
    print(f"train={Xtr.shape[0]} val={Xval.shape[0]}", flush=True)

    model = ChessNet(channels=args.channels, num_blocks=args.blocks)
    if args.init_from:
        model.load_weights(args.init_from)
    mx.eval(model.parameters())

    optimizer = optim.Adam(learning_rate=args.lr)
    loss_and_grad = nn.value_and_grad(model, loss_fn)

    log_is_new = not log_path.exists()
    log_file = log_path.open("a", newline="")
    writer = csv.writer(log_file)
    if log_is_new:
        writer.writerow(
            ["round", "epoch", "train_loss", "val_loss", "val_policy_loss", "val_value_loss", "eval_score", "eval_elo_gap", "seconds"]
        )
        log_file.flush()

    train_until_plateau(
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
        max_epochs=args.max_epochs,
        patience=args.patience,
        min_delta=args.min_delta,
        eval_every=args.eval_every,
        eval_games=args.eval_games,
        stockfish=args.stockfish,
        sf_elo=args.sf_elo,
        sf_movetime_ms=args.sf_movetime_ms,
        use_value_lookahead=not args.no_value_lookahead,
        best_path=best_path,
        latest_path=latest_path,
        writer=writer,
        log_file=log_file,
    )

    log_file.close()
    print(f"log: {log_path}\nbest checkpoint: {best_path}\nlatest checkpoint: {latest_path}")


if __name__ == "__main__":
    try:
        main()
    except KeyboardInterrupt:
        sys.exit(1)
