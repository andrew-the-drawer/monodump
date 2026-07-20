"""Encode JSONL records from generate_data.py into a dense .npz training set."""

import argparse
import json
import sys
from pathlib import Path

import chess
import numpy as np

sys.path.insert(0, str(Path(__file__).parent))
from encoding import POLICY_SIZE, encode_board, move_to_index  # noqa: E402


def encode_jsonl_files(paths: list[str]) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    """Encode one or more generate_data.py JSONL files into (X, P, V) arrays."""
    boards, policies, values = [], [], []

    for path in paths:
        with open(path) as f:
            for line in f:
                line = line.strip()
                if not line:
                    continue
                rec = json.loads(line)
                board = chess.Board(rec["fen"])

                policy = np.zeros(POLICY_SIZE, dtype=np.float32)
                for uci, prob in zip(rec["moves_uci"], rec["probs"]):
                    idx = move_to_index(chess.Move.from_uci(uci), board)
                    # `+=`, not `=`: distinct top-K moves can collapse to the
                    # same 4096 (from, to) index (e.g. under-promotions), and
                    # overwriting would silently drop that probability mass,
                    # leaving the row un-normalized. See the renormalize below.
                    policy[idx] += prob
                total = policy.sum()
                if total <= 0:
                    # no usable policy target for this record; skip it so we
                    # never emit an all-zero row into the training set.
                    continue
                # Renormalize to a proper distribution (sum == 1). The policy
                # loss (cross-entropy over a soft target) is only well-behaved
                # for normalized targets; an un-normalized row makes the MLX
                # cross-entropy unbounded and lets training diverge.
                policy /= total
                policies.append(policy)

                boards.append(encode_board(board))
                values.append(rec["value"])

    X = np.stack(boards).astype(np.float32)
    P = np.stack(policies).astype(np.float32)
    V = np.array(values, dtype=np.float32)
    return X, P, V


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("inputs", nargs="+", help="one or more .jsonl files from generate_data.py")
    ap.add_argument("--out", default="../data/dataset.npz")
    args = ap.parse_args()

    X, P, V = encode_jsonl_files(args.inputs)

    out_path = Path(args.out)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    np.savez_compressed(out_path, X=X, P=P, V=V)
    print(f"wrote {len(V)} positions to {out_path} (X={X.shape}, P={P.shape}, V={V.shape})")


if __name__ == "__main__":
    main()
