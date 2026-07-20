"""Generate distillation data from a Stockfish teacher.

For each sampled position we ask Stockfish for its top-K moves (MultiPV) at a
fixed depth and record:
  - fen: the position
  - moves_uci / probs: a soft policy target over the top-K moves, built by
    softmax-ing the moves' centipawn scores
  - value: the best move's centipawn score converted to [-1, 1]

Games are self-play: Stockfish plays both sides, with a few random opening
plies for diversity and temperature-based sampling afterwards so we don't
just replay the same principal variation every game.

Usage:
    python generate_data.py --games 20 --depth 8 --out ../data/games_001.jsonl
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
) -> list[dict]:
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

        if play_temp > 0 and len(moves) > 1:
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
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--threads", type=int, default=1)
    ap.add_argument("--out", default="../data/games.jsonl")
    args = ap.parse_args()

    rng = random.Random(args.seed)
    out_path = Path(args.out)
    out_path.parent.mkdir(parents=True, exist_ok=True)

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
