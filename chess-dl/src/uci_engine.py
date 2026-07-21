#!/usr/bin/env python3
"""Minimal UCI engine wrapper around the trained student model.

Speaks just enough UCI to work as an engine backend for lichess-bot (or any
other UCI-driving arena/GUI). Run it with the venv's Python, e.g.:

    /path/to/monodump/venv/bin/python uci_engine.py \
        --checkpoint ../checkpoints/chessnet.npz --channels 64 --blocks 4

See ../README.md for how to plug this into lichess-bot for real Lichess play.
"""

import argparse
import sys

import chess

from model import ChessNet
from play import select_move

ENGINE_NAME = "chess-dl-student"
ENGINE_AUTHOR = "chess-dl"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--checkpoint", default="../checkpoints/chessnet.npz")
    ap.add_argument("--channels", type=int, default=64)
    ap.add_argument("--blocks", type=int, default=4)
    ap.add_argument("--no-value-lookahead", action="store_true")
    ap.add_argument("--mcts-sims", type=int, default=0, help="PUCT simulations per move (0=off; recommended for real play, e.g. 200-800)")
    ap.add_argument("--c-puct", type=float, default=1.5, help="MCTS exploration constant")
    args = ap.parse_args()

    model = ChessNet(channels=args.channels, num_blocks=args.blocks)
    model.load_weights(args.checkpoint)
    model.eval()
    use_value = not args.no_value_lookahead

    board = chess.Board()

    def send(msg: str) -> None:
        sys.stdout.write(msg + "\n")
        sys.stdout.flush()

    for line in sys.stdin:
        tokens = line.strip().split()
        if not tokens:
            continue
        cmd = tokens[0]

        if cmd == "uci":
            send(f"id name {ENGINE_NAME}")
            send(f"id author {ENGINE_AUTHOR}")
            send("uciok")
        elif cmd == "isready":
            send("readyok")
        elif cmd == "ucinewgame":
            board = chess.Board()
        elif cmd == "position":
            board = chess.Board()
            rest = tokens[1:]
            if rest and rest[0] == "startpos":
                rest = rest[1:]
            elif rest and rest[0] == "fen":
                fen_tokens = []
                rest = rest[1:]
                while rest and rest[0] != "moves":
                    fen_tokens.append(rest.pop(0))
                board = chess.Board(" ".join(fen_tokens))
            if rest and rest[0] == "moves":
                for uci_move in rest[1:]:
                    board.push_uci(uci_move)
        elif cmd == "go":
            move = select_move(model, board, use_value=use_value, mcts_sims=args.mcts_sims, c_puct=args.c_puct)
            send(f"bestmove {move.uci()}")
        elif cmd in ("quit", "stop"):
            if cmd == "quit":
                break
        elif cmd == "setoption":
            pass  # no configurable options yet
        # unknown commands are silently ignored, per UCI convention


if __name__ == "__main__":
    main()
