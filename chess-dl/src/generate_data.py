"""Generate distillation data from a Stockfish teacher.

For each sampled position we ask Stockfish for its top-K moves (MultiPV) at a
fixed depth and record:
  - fen: the position
  - moves_uci / probs: a soft policy target over the top-K moves, built by
    softmax-ing the moves' centipawn scores
  - value: the best move's centipawn score converted to [-1, 1]

Stockfish always supplies the label at every position. Who *picks the move
that gets played next* is a separate, configurable choice:

  - **Off-policy (default, no `--student-checkpoint`)**: Stockfish plays both
    sides (with a few random opening plies for diversity, then
    temperature-based sampling over its own top-K afterwards). This is plain
    distillation: the student never influences which positions it trains on.
  - **On-policy (`--student-checkpoint`)**: the student model plays both
    sides instead (optionally with MCTS/value-lookahead, same knobs as
    `evaluate.py`), while Stockfish still analyses and labels every position
    reached. This closes the train/play distribution gap -- see the DAgger
    discussion in README.md -- so the dataset covers the positions the
    student actually reaches (including its own mistakes), not just the
    positions a flawless Stockfish would reach.

Usage:
    python generate_data.py --games 20 --depth 8 --out ../data/games_001.jsonl

    # on-policy: student plays, Stockfish still labels
    python generate_data.py --games 20 --depth 8 --out ../data/games_002.jsonl \
        --student-checkpoint ../checkpoints/auto/best.npz --mcts-sims 400
"""

import argparse
import json
import math
import random
import sys
from pathlib import Path

import chess
import chess.engine

sys.path.insert(0, str(Path(__file__).parent))
from encoding import cp_to_value  # noqa: E402
from play import select_move  # noqa: E402


def pov_score_cp(score: chess.engine.PovScore, pov_color: chess.Color) -> float:
    return score.pov(pov_color).score(mate_score=100_000)


def softmax(xs: list[float], temperature: float) -> list[float]:
    scaled = [x / temperature for x in xs]
    m = max(scaled)
    exps = [math.exp(x - m) for x in scaled]
    total = sum(exps)
    return [e / total for e in exps]


def generate_game(
    engine: chess.engine.SimpleEngine,
    multipv: int,
    depth: int,
    max_plies: int,
    opening_random_plies: int,
    softmax_temp_cp: float,
    play_temp: float,
    rng: random.Random,
    game_id: int | None = None,
    student_model=None,
    student_temp: float = 1.0,
    mcts_sims: int = 0,
    c_puct: float = 1.5,
    use_value_lookahead: bool = True,
) -> list[dict]:
    """Play one game, always labeling every non-opening position with
    Stockfish's analysis. `student_model`, when given, switches move
    *selection* (not labeling) to on-policy: the student itself (optionally
    via MCTS/value lookahead, `student_temp`-sampled so it doesn't replay the
    same line every game) picks which move actually gets played, instead of
    Stockfish. See the module docstring for why this matters.
    """
    board = chess.Board()
    records = []
    # Tag every position with the game it came from so the training split can
    # hold out *whole games* rather than individual positions. Consecutive
    # positions in one game are one move apart and highly correlated, so a
    # per-position split leaks near-duplicates across train/val and makes
    # val_loss look better than it is. A random per-game id (unique within a
    # data file) lets build_dataset/load_dataset group by game.
    if game_id is None:
        game_id = rng.getrandbits(63)

    for ply in range(max_plies):
        if board.is_game_over(claim_draw=True):
            break

        if ply < opening_random_plies:
            move = rng.choice(list(board.legal_moves))
            board.push(move)
            continue

        limit = chess.engine.Limit(depth=depth)
        infos = engine.analyse(board, limit, multipv=min(multipv, board.legal_moves.count()))
        if isinstance(infos, dict):
            infos = [infos]

        moves, cps = [], []
        for entry in infos:
            pv = entry.get("pv")
            if not pv:
                continue
            moves.append(pv[0])
            cps.append(pov_score_cp(entry["score"], board.turn))
        if not moves:
            break

        probs = softmax(cps, softmax_temp_cp)
        records.append(
            {
                "fen": board.fen(),
                "moves_uci": [m.uci() for m in moves],
                "probs": probs,
                "value": cp_to_value(cps[0]),
                "game_id": game_id,
            }
        )

        if student_model is not None:
            move = select_move(
                student_model,
                board,
                use_value=use_value_lookahead,
                mcts_sims=mcts_sims,
                c_puct=c_puct,
                temperature=student_temp,
                rng=rng,
            )
        elif play_temp > 0 and len(moves) > 1:
            play_probs = softmax(cps, softmax_temp_cp * max(play_temp, 1e-3))
            move = rng.choices(moves, weights=play_probs)[0]
        else:
            move = moves[0]
        board.push(move)

    return records


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--stockfish", default="stockfish")
    ap.add_argument("--games", type=int, default=10)
    ap.add_argument("--depth", type=int, default=8)
    ap.add_argument("--multipv", type=int, default=4)
    ap.add_argument("--max-plies", type=int, default=80)
    ap.add_argument("--opening-random-plies", type=int, default=6)
    ap.add_argument("--softmax-temp-cp", type=float, default=150.0, help="centipawn scale for policy softmax")
    ap.add_argument("--play-temp", type=float, default=0.7, help="0 = always play best move; >0 = sample")
    ap.add_argument("--seed", type=int, default=-1, help="RNG seed; <0 (default) = system entropy so re-runs don't replay identical games that de-duplicate away. A fixed seed is reproducible but offset by existing records in --out on append.")
    ap.add_argument("--threads", type=int, default=1)
    ap.add_argument("--out", default="../data/games.jsonl")
    ap.add_argument("--student-checkpoint", default=None, help="if set, the student model plays both sides (on-policy) instead of Stockfish; Stockfish still analyses and labels every position. See module docstring.")
    ap.add_argument("--channels", type=int, default=64, help="student model size (must match --student-checkpoint)")
    ap.add_argument("--blocks", type=int, default=4, help="student model size (must match --student-checkpoint)")
    ap.add_argument("--student-temp", type=float, default=1.0, help="temperature for sampling the student's on-policy move (0 = deterministic; only used with --student-checkpoint)")
    ap.add_argument("--mcts-sims", type=int, default=0, help="PUCT sims for the student's move selection (0=off, use policy+value lookahead instead); only used with --student-checkpoint")
    ap.add_argument("--c-puct", type=float, default=1.5, help="MCTS exploration constant")
    ap.add_argument("--no-value-lookahead", action="store_true", help="student plays greedy policy instead of 1-ply value lookahead when --mcts-sims is 0")
    args = ap.parse_args()

    student_model = None
    if args.student_checkpoint:
        from model import ChessNet

        student_model = ChessNet(channels=args.channels, num_blocks=args.blocks)
        student_model.load_weights(args.student_checkpoint)
        student_model.eval()

    out_path = Path(args.out)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    # See auto_pipeline.py for why a fixed seed replays identical games. Default
    # to entropy; a given seed is offset by existing records so appends continue
    # the sequence instead of repeating it.
    if args.seed is not None and args.seed >= 0:
        existing_records = sum(1 for _ in out_path.open()) if out_path.exists() else 0
        rng = random.Random(f"{args.seed}-{existing_records}")
    else:
        rng = random.Random()

    engine = chess.engine.SimpleEngine.popen_uci(args.stockfish)
    engine.configure({"Threads": args.threads})

    total_positions = 0
    try:
        with out_path.open("a") as f:
            for g in range(args.games):
                records = generate_game(
                    engine,
                    multipv=args.multipv,
                    depth=args.depth,
                    max_plies=args.max_plies,
                    opening_random_plies=args.opening_random_plies,
                    softmax_temp_cp=args.softmax_temp_cp,
                    play_temp=args.play_temp,
                    rng=rng,
                    student_model=student_model,
                    student_temp=args.student_temp,
                    mcts_sims=args.mcts_sims,
                    c_puct=args.c_puct,
                    use_value_lookahead=not args.no_value_lookahead,
                )
                for r in records:
                    f.write(json.dumps(r) + "\n")
                f.flush()
                total_positions += len(records)
                print(f"game {g + 1}/{args.games}: {len(records)} positions (total {total_positions})")
    finally:
        engine.quit()


if __name__ == "__main__":
    main()
