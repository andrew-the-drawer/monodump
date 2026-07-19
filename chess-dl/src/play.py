"""Move selection for the trained student model.

Greedy policy-net move choice, optionally refined with a 1-ply value-head
lookahead over the policy's top candidates (cheap "policy+value" hybrid,
similar in spirit to AlphaZero's search but with zero tree search cost).
"""

from __future__ import annotations

import chess
import mlx.core as mx
import numpy as np

from encoding import encode_board, index_to_move, legal_move_indices


def policy_probs(model, board: chess.Board) -> tuple[np.ndarray, list[int], list[chess.Move]]:
    x = mx.array(encode_board(board)[None, ...])
    logits, _value = model(x)
    logits = np.array(logits[0])

    legal_moves = list(board.legal_moves)
    legal_idx = legal_move_indices(board)

    mask = np.full(logits.shape, -np.inf, dtype=np.float32)
    mask[legal_idx] = logits[legal_idx]
    mask -= mask.max()
    probs = np.exp(mask)
    probs /= probs.sum()
    return probs, legal_idx, legal_moves


def select_move(model, board: chess.Board, use_value: bool = True, top_k: int = 8) -> chess.Move:
    probs, legal_idx, legal_moves = policy_probs(model, board)

    if not use_value or len(legal_moves) == 1:
        best_idx = legal_idx[int(np.argmax(probs[legal_idx]))]
        move = index_to_move(best_idx, board)
        return move if move is not None else legal_moves[0]

    order = np.argsort(-probs[legal_idx])[: min(top_k, len(legal_idx))]
    candidates = [legal_moves[i] for i in order]

    children = []
    for mv in candidates:
        board.push(mv)
        children.append(encode_board(board))
        board.pop()

    x = mx.array(np.stack(children))
    _logits, values = model(x)
    values = np.array(values)  # value of resulting position, from the *opponent's* POV

    best = candidates[int(np.argmin(values))]
    return best
