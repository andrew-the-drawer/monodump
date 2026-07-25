"""Play the student model against Stockfish (at a limited strength) to get a
rough win/draw/loss score and an approximate Elo gap.

Usage:
    python evaluate.py --checkpoint ../checkpoints/chessnet.npz --games 10 --sf-elo 1350
"""

import argparse
import math

import chess
import chess.engine

from model import ChessNet
from play import select_move


def score_to_elo_diff(score: float) -> float:
    score = min(max(score, 1e-4), 1 - 1e-4)
    return -400.0 * math.log10(1.0 / score - 1.0)


def play_game(
    model,
    engine: chess.engine.SimpleEngine,
    student_is_white: bool,
    sf_limit,
    use_value: bool,
    mcts_sims: int = 0,
    c_puct: float = 1.5,
) -> str:
    board = chess.Board()
    while not board.is_game_over(claim_draw=True):
        student_to_move = (board.turn == chess.WHITE) == student_is_white
        if student_to_move:
            move = select_move(model, board, use_value=use_value, mcts_sims=mcts_sims, c_puct=c_puct)
        else:
            result = engine.play(board, sf_limit)
            move = result.move
        board.push(move)
    outcome = board.outcome(claim_draw=True)
    if outcome.winner is None:
        return "draw"
    student_won = (outcome.winner == chess.WHITE) == student_is_white
    return "win" if student_won else "loss"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--checkpoint", default="../checkpoints/chessnet.npz")
    ap.add_argument("--channels", type=int, default=64)
    ap.add_argument("--blocks", type=int, default=4)
    ap.add_argument("--games", type=int, default=10)
    ap.add_argument("--stockfish", default="stockfish")
    ap.add_argument("--sf-elo", type=int, default=1350, help="Stockfish UCI_Elo target (min ~1320)")
    ap.add_argument("--sf-movetime-ms", type=int, default=100)
    ap.add_argument("--no-value-lookahead", action="store_true")
    ap.add_argument("--mcts-sims", type=int, default=0, help="PUCT simulations per move (0=off, use policy+1-ply value lookahead instead)")
    ap.add_argument("--c-puct", type=float, default=1.5, help="MCTS exploration constant (higher=more exploration)")
    args = ap.parse_args()

    model = ChessNet(channels=args.channels, num_blocks=args.blocks)
    model.load_weights(args.checkpoint)
    model.eval()

    engine = chess.engine.SimpleEngine.popen_uci(args.stockfish)
    engine.configure({"UCI_LimitStrength": True, "UCI_Elo": args.sf_elo})
    sf_limit = chess.engine.Limit(time=args.sf_movetime_ms / 1000.0)

    results = {"win": 0, "draw": 0, "loss": 0}
    try:
        for g in range(args.games):
            student_is_white = g % 2 == 0
            outcome = play_game(
                model, engine, student_is_white, sf_limit,
                use_value=not args.no_value_lookahead, mcts_sims=args.mcts_sims, c_puct=args.c_puct,
            )
            results[outcome] += 1
            print(f"game {g + 1}/{args.games}: student={'white' if student_is_white else 'black'} -> {outcome}")
    finally:
        engine.quit()

    n = args.games
    score = (results["win"] + 0.5 * results["draw"]) / n
    print(f"\nresults vs Stockfish (Elo {args.sf_elo}): {results}  score={score:.2f}")
    print(f"approx Elo gap: {score_to_elo_diff(score):+.0f} (student relative to Stockfish@{args.sf_elo})")


if __name__ == "__main__":
    main()
