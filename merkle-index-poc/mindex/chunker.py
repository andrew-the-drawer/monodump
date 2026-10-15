"""Split a file into overlapping line windows.

Real systems chunk along syntax (functions, classes) with tree-sitter; fixed
line windows keep the PoC dependency-free and are good enough for search.
Chunk size matters for the inversion experiment: embedding-inversion attacks
recover short texts far better than long ones (see docs/03-inversion.md).
"""

from __future__ import annotations

import hashlib
import os
from dataclasses import dataclass

DEFAULT_LINES = int(os.environ.get("MINDEX_CHUNK_LINES", "30"))
DEFAULT_OVERLAP = int(os.environ.get("MINDEX_CHUNK_OVERLAP", "5"))


@dataclass
class Chunk:
    start_line: int  # 1-based, inclusive
    end_line: int  # 1-based, inclusive
    text: str

    @property
    def hash(self) -> str:
        return hashlib.sha256(self.text.encode()).hexdigest()


def chunk_text(text: str, lines: int = DEFAULT_LINES, overlap: int = DEFAULT_OVERLAP) -> list[Chunk]:
    all_lines = text.splitlines()
    step = max(1, lines - overlap)
    chunks = []
    for start in range(0, len(all_lines), step):
        window = all_lines[start : start + lines]
        body = "\n".join(window)
        if body.strip():
            chunks.append(Chunk(start + 1, start + len(window), body))
        if start + lines >= len(all_lines):
            break
    return chunks
