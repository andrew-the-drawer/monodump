"""Encode JSONL records from generate_data.py into a dense .npz training set."""

import argparse
import json
import sys
from pathlib import Path

import chess
import numpy as np

sys.path.insert(0, str(Path(__file__).parent))
from encoding import POLICY_SIZE, encode_board, move_to_index  # noqa: E402


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("inputs", nargs="+", help="one or more .jsonl files from generate_data.py")
    ap.add_argument("--out", default="../data/dataset.npz")
    args = ap.parse_args()

    boards, policies, values = [], [], []

    for path in args.inputs:
        with open(path) as f:
            for line in f:
                line = line.strip()
                if not line:
                    continue
                rec = json.loads(line)
                board = chess.Board(rec["fen"])
                boards.append(encode_board(board))

                policy = np.zeros(POLICY_SIZE, dtype=np.float32)
                for uci, prob in zip(rec["moves_uci"], rec["probs"]):
                    idx = move_to_index(chess.Move.from_uci(uci), board)
                    policy[idx] = prob
                policies.append(policy)

                values.append(rec["value"])

    X = np.stack(boards).astype(np.float32)
    P = np.stack(policies).astype(np.float32)
    V = np.array(values, dtype=np.float32)

    out_path = Path(args.out)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    np.savez_compressed(out_path, X=X, P=P, V=V)
    print(f"wrote {len(values)} positions to {out_path} (X={X.shape}, P={P.shape}, V={V.shape})")


if __name__ == "__main__":
    main()
