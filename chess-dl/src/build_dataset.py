"""Encode JSONL records from generate_data.py into a dense .npz training set."""

import argparse
import json
import sys
from pathlib import Path

import chess
import numpy as np

sys.path.insert(0, str(Path(__file__).parent))
from encoding import POLICY_SIZE, encode_board, move_to_index  # noqa: E402


def _position_key(fen: str) -> str:
    """Identity of a position for de-duplication: piece placement, side to
    move, castling rights, en-passant square — the first four FEN fields. The
    halfmove/fullmove clocks (fields 5-6) are dropped on purpose: they don't
    change the board the network sees or the teacher's targets, so positions
    that differ only by clock are genuine duplicates for our purposes."""
    return " ".join(fen.split(" ")[:4])


def encode_jsonl_files(paths: list[str]) -> tuple[np.ndarray, np.ndarray, np.ndarray, np.ndarray]:
    """Encode one or more generate_data.py JSONL files into (X, P, V, G) arrays.

    Positions are **de-duplicated** by `_position_key` (self-play from a fixed
    teacher revisits the same openings/positions across games — measured ~1.6x
    duplication), keeping the first occurrence. Duplicates carry identical
    targets (the teacher is deterministic at a fixed depth), so dropping them
    loses no signal but removes exact-position leakage across the train/val
    split.

    `G` is a per-position game-group id (from each record's `game_id`, written
    by generate_data.py) so `load_dataset` can hold out whole games. Records
    without a `game_id` (data generated before that field existed) each get a
    unique negative id, i.e. they fall back to being their own group — after
    de-duplication that is equivalent to a per-position split with no exact
    leakage.
    """
    boards, policies, values, groups = [], [], [], []
    seen: set[str] = set()
    fallback_gid = -1

    for path in paths:
        with open(path) as f:
            for line in f:
                line = line.strip()
                if not line:
                    continue
                rec = json.loads(line)
                key = _position_key(rec["fen"])
                if key in seen:
                    continue
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
                    # never emit an all-zero row into the training set. Don't
                    # add to `seen`, so a later usable copy could still be kept.
                    continue
                # Renormalize to a proper distribution (sum == 1). The policy
                # loss (cross-entropy over a soft target) is only well-behaved
                # for normalized targets; an un-normalized row makes the MLX
                # cross-entropy unbounded and lets training diverge.
                policy /= total

                seen.add(key)
                policies.append(policy)
                boards.append(encode_board(board))
                values.append(rec["value"])
                gid = rec.get("game_id")
                if gid is None:
                    gid = fallback_gid
                    fallback_gid -= 1
                groups.append(int(gid))

    X = np.stack(boards).astype(np.float32)
    P = np.stack(policies).astype(np.float32)
    V = np.array(values, dtype=np.float32)
    G = np.array(groups, dtype=np.int64)
    return X, P, V, G


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("inputs", nargs="+", help="one or more .jsonl files from generate_data.py")
    ap.add_argument("--out", default="../data/dataset.npz")
    args = ap.parse_args()

    X, P, V, G = encode_jsonl_files(args.inputs)

    out_path = Path(args.out)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    np.savez_compressed(out_path, X=X, P=P, V=V, G=G)
    n_games = len(np.unique(G))
    print(f"wrote {len(V)} unique positions ({n_games} game-groups) to {out_path} "
          f"(X={X.shape}, P={P.shape}, V={V.shape}, G={G.shape})")


if __name__ == "__main__":
    main()
