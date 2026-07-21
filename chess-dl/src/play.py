"""Move selection for the trained student model.

Three strengths of move selection, cheapest first:

  1. **Greedy policy** (`use_value=False`): play the policy head's argmax legal
     move. One net call, zero lookahead.
  2. **1-ply value lookahead** (`use_value=True`, the default): take the
     policy's top-K candidates, evaluate the resulting positions with the
     value head, and keep the one the opponent likes least. A cheap
     "policy+value" hybrid with no tree — one extra batched net call.
  3. **PUCT search** (`mcts_sims > 0`): AlphaZero-style Monte-Carlo tree
     search guided by the policy head (priors) and evaluated by the value
     head (leaf values, no rollouts). This is the strong option — it looks
     several plies deep along the lines that matter and picks the move that
     survives that scrutiny (the most-visited root child), which fixes the
     compounding tactical blunders that one-shot policy play makes. Costs one
     net call per simulation, so `mcts_sims` is a direct speed/strength knob.

`select_move` dispatches to whichever of these is requested; MCTS wins if
`mcts_sims > 0`, otherwise the `use_value` flag chooses between 1 and 2.

Why PUCT and not plain UCT/alpha-beta: the policy prior ("Predictor") lets
search spend its simulations on the handful of moves the net thinks are
plausible instead of expanding all ~35 legal moves uniformly, and the value
head replaces the random rollout to game end with a single learned
evaluation. Both are exactly the ingredients this net already produces, so
the search is almost free to bolt on. See `run_mcts` for the formula.
"""

from __future__ import annotations

import math

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


def policy_value(model, board: chess.Board) -> tuple[float, list[chess.Move], np.ndarray]:
    """One forward pass -> (value, legal_moves, priors).

    `value` is the value head's scalar for `board`, from the side-to-move POV
    (the same [-1, 1] frame as `encoding.cp_to_value`). `priors` is a
    legal-move-masked softmax of the policy head, aligned to `legal_moves`.
    Used by `run_mcts`, which needs both heads from a single evaluation.
    """
    x = mx.array(encode_board(board)[None, ...])
    logits, value = model(x)
    logits = np.array(logits[0])
    v = float(np.array(value)[0])

    legal_moves = list(board.legal_moves)
    legal_idx = legal_move_indices(board)
    masked = logits[legal_idx]
    masked -= masked.max()
    priors = np.exp(masked)
    priors /= priors.sum()
    return v, legal_moves, priors


class _Node:
    """One position in the search tree.

    Values are stored in *negamax* convention: `value_sum`/`Q` are from the
    POV of the player to move *at this node*, so a child's value is the
    negation of what it contributes to its parent's decision (see `run_mcts`).
    """

    __slots__ = ("prior", "children", "visit_count", "value_sum", "is_expanded")

    def __init__(self, prior: float):
        self.prior = prior
        self.children: dict[chess.Move, _Node] = {}
        self.visit_count = 0
        self.value_sum = 0.0
        self.is_expanded = False

    def q(self) -> float:
        return self.value_sum / self.visit_count if self.visit_count else 0.0


def _expand(node: _Node, legal_moves: list[chess.Move], priors: np.ndarray) -> None:
    for mv, p in zip(legal_moves, priors):
        node.children[mv] = _Node(float(p))
    node.is_expanded = True


def _select_child(node: _Node, c_puct: float) -> tuple[chess.Move, _Node]:
    """Pick the child maximizing PUCT = Q + U (see `run_mcts` for the formula)."""
    sqrt_total = math.sqrt(node.visit_count)
    best_score, best_move, best_child = -float("inf"), None, None
    for move, child in node.children.items():
        # child.q() is from the child's POV; negate to score it from this
        # node's POV (the player choosing the move).
        q = -child.q()
        u = c_puct * child.prior * sqrt_total / (1 + child.visit_count)
        score = q + u
        if score > best_score:
            best_score, best_move, best_child = score, move, child
    return best_move, best_child


def _terminal_value(board: chess.Board) -> float:
    """Value of a game-over `board` from the side-to-move POV: a side to move
    with no reply is either checkmated (-1) or in a draw (0). It can never be
    a win, since the mating side has already moved."""
    outcome = board.outcome(claim_draw=True)
    return 0.0 if outcome.winner is None else -1.0


def run_mcts(
    model,
    board: chess.Board,
    sims: int,
    c_puct: float = 1.5,
) -> chess.Move:
    """PUCT Monte-Carlo tree search over the policy+value net.

    Runs `sims` simulations, each of which:

      1. **Select** — from the root, descend by repeatedly picking the child
         that maximizes
             PUCT(s,a) = Q(s,a) + c_puct * P(s,a) * sqrt(sum_b N(s,b)) / (1 + N(s,a))
         where Q is the mean value seen through move `a` (from `s`'s POV), P is
         the policy prior, and N is the visit count. The Q term exploits moves
         that have evaluated well; the U term explores moves with high prior
         and few visits, and decays as they get visited.
      2. **Expand + evaluate** — at the first unvisited node, run the net once:
         the value head gives the leaf value, the policy head fills the child
         priors. Terminal positions skip the net and use the true game result.
      3. **Backup** — propagate the leaf value up the descended path, negating
         it each ply (a position good for one side is bad for the other).

    Returns the most-visited root move — the one search kept coming back to,
    which is more robust than the single-highest-Q move. `c_puct` trades
    exploration (higher) against exploitation (lower).
    """
    root = _Node(prior=1.0)
    _, legal_moves, priors = policy_value(model, board)
    _expand(root, legal_moves, priors)

    for _ in range(sims):
        node = root
        path = [node]

        # 1. selection: walk down until we hit a not-yet-expanded node
        while node.is_expanded and node.children:
            move, node = _select_child(node, c_puct)
            board.push(move)
            path.append(node)

        # 2. evaluation of the leaf (terminal result or net value + expand)
        if board.is_game_over(claim_draw=True):
            leaf_value = _terminal_value(board)
        else:
            leaf_value, leaf_moves, leaf_priors = policy_value(model, board)
            _expand(node, leaf_moves, leaf_priors)

        # 3. backup: leaf_value is from the leaf's POV; flip each level up
        value = leaf_value
        for n in reversed(path):
            n.visit_count += 1
            n.value_sum += value
            value = -value

        # restore the board to the root position
        for _ in range(len(path) - 1):
            board.pop()

    return max(root.children.items(), key=lambda kv: kv[1].visit_count)[0]


def select_move(
    model,
    board: chess.Board,
    use_value: bool = True,
    top_k: int = 8,
    mcts_sims: int = 0,
    c_puct: float = 1.5,
) -> chess.Move:
    """Choose a move for `board`. If `mcts_sims > 0`, run PUCT search;
    otherwise fall back to greedy policy (`use_value=False`) or the 1-ply
    value lookahead (`use_value=True`). See the module docstring."""
    if mcts_sims > 0:
        return run_mcts(model, board, mcts_sims, c_puct)

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
