"""Board/move encoding shared by data generation, training, and inference.

Boards are always encoded from the perspective of the side to move (vertical
flip + piece-plane swap when Black is to move), and moves are encoded in that
same oriented frame as `from_square * 64 + to_square` (4096 classes).
Underpromotions are collapsed into the same class as queen promotion.
"""

import chess
import numpy as np

NUM_PLANES = 17  # 12 piece planes + 4 castling-rights planes + 1 en-passant plane
POLICY_SIZE = 4096  # from_square (64) * to_square (64)

_PIECE_ORDER = [
    chess.PAWN,
    chess.KNIGHT,
    chess.BISHOP,
    chess.ROOK,
    chess.QUEEN,
    chess.KING,
]


def _oriented_square(square: int, flip: bool) -> int:
    return chess.square_mirror(square) if flip else square


def encode_board(board: chess.Board) -> np.ndarray:
    """Encode `board` into a (8, 8, NUM_PLANES) float32 array, NHWC-ready."""
    flip = board.turn == chess.BLACK
    planes = np.zeros((8, 8, NUM_PLANES), dtype=np.float32)

    us = board.turn
    them = not board.turn
    for plane_idx, color in enumerate((us, them)):
        for piece_offset, piece_type in enumerate(_PIECE_ORDER):
            plane = plane_idx * 6 + piece_offset
            for square in board.pieces(piece_type, color):
                osq = _oriented_square(square, flip)
                rank, file = divmod(osq, 8)
                planes[rank, file, plane] = 1.0

    castling_plane = 12
    rights = [
        board.has_kingside_castling_rights(us),
        board.has_queenside_castling_rights(us),
        board.has_kingside_castling_rights(them),
        board.has_queenside_castling_rights(them),
    ]
    for i, has_right in enumerate(rights):
        if has_right:
            planes[:, :, castling_plane + i] = 1.0

    if board.ep_square is not None:
        osq = _oriented_square(board.ep_square, flip)
        rank, file = divmod(osq, 8)
        planes[rank, file, 16] = 1.0

    return planes


def move_to_index(move: chess.Move, board: chess.Board) -> int:
    flip = board.turn == chess.BLACK
    frm = _oriented_square(move.from_square, flip)
    to = _oriented_square(move.to_square, flip)
    return frm * 64 + to


def index_to_move(index: int, board: chess.Board) -> chess.Move | None:
    """Map a policy index back to a legal move on `board`, preferring queen
    promotion when a from/to pair is ambiguous (queen vs under-promotion)."""
    flip = board.turn == chess.BLACK
    frm_o, to_o = divmod(index, 64)
    candidates = []
    for legal in board.legal_moves:
        frm = _oriented_square(legal.from_square, flip)
        to = _oriented_square(legal.to_square, flip)
        if frm == frm_o and to == to_o:
            candidates.append(legal)
    if not candidates:
        return None
    for c in candidates:
        if c.promotion in (None, chess.QUEEN):
            return c
    return candidates[0]


def legal_move_indices(board: chess.Board) -> list[int]:
    return [move_to_index(m, board) for m in board.legal_moves]


def cp_to_value(cp: float) -> float:
    """Centipawn score (from side-to-move POV) -> value in [-1, 1]."""
    return float(np.tanh(cp / 500.0))
