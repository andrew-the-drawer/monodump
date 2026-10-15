"""Embedding backends, selected on the server with MINDEX_EMBEDDER.

    hash   - feature-hashed bag of identifiers. No ML, instant, deterministic.
             Used by the tests; search quality is keyword-level.
    minilm - sentence-transformers/all-MiniLM-L6-v2 (384-d). Real semantic search.
    gtr    - GTR-T5-base encoder with mean pooling (768-d), computed exactly the
             way vec2text expects, so the inversion attack in
             scripts/invert_attack.py can run against what the server stored.

The embedding cache is keyed by (embedder name, chunk hash), so switching
backends never mixes vectors from different models.
"""

from __future__ import annotations

import hashlib
import os
import re
from functools import lru_cache

import numpy as np


class HashEmbedder:
    name = "hash"
    dim = 512

    _token = re.compile(r"[A-Za-z][a-z0-9]*|[A-Z]+(?![a-z])|\d+")

    def embed(self, texts: list[str]) -> np.ndarray:
        out = np.zeros((len(texts), self.dim), dtype=np.float32)
        for i, text in enumerate(texts):
            for tok in self._token.findall(text):
                h = int.from_bytes(hashlib.blake2b(tok.lower().encode(), digest_size=8).digest(), "little")
                out[i, h % self.dim] += 1.0 if (h >> 63) == 0 else -1.0
        return out


class MiniLMEmbedder:
    name = "minilm"
    dim = 384

    def __init__(self):
        from sentence_transformers import SentenceTransformer

        self._model = SentenceTransformer("sentence-transformers/all-MiniLM-L6-v2")

    def embed(self, texts: list[str]) -> np.ndarray:
        return self._model.encode(texts, batch_size=32, convert_to_numpy=True).astype(np.float32)


class GtrEmbedder:
    """Matches vec2text's `get_gtr_embeddings`: T5 encoder + mean pooling, no Dense/Normalize."""

    name = "gtr"
    dim = 768

    def __init__(self):
        import torch
        from transformers import AutoTokenizer, T5EncoderModel

        self._torch = torch
        self._tok = AutoTokenizer.from_pretrained("sentence-transformers/gtr-t5-base")
        self._enc = T5EncoderModel.from_pretrained("sentence-transformers/gtr-t5-base").eval()

    def embed(self, texts: list[str]) -> np.ndarray:
        torch = self._torch
        out = []
        for i in range(0, len(texts), 16):
            batch = self._tok(texts[i : i + 16], return_tensors="pt", max_length=128,
                              truncation=True, padding="max_length")
            with torch.no_grad():
                hidden = self._enc(**batch).last_hidden_state
            mask = batch["attention_mask"].unsqueeze(-1).float()
            out.append(((hidden * mask).sum(1) / mask.sum(1)).numpy())
        return np.concatenate(out).astype(np.float32)


_BACKENDS = {"hash": HashEmbedder, "minilm": MiniLMEmbedder, "gtr": GtrEmbedder}


@lru_cache(maxsize=None)
def get_embedder(name: str | None = None):
    name = name or os.environ.get("MINDEX_EMBEDDER", "minilm")
    if name not in _BACKENDS:
        raise ValueError(f"unknown embedder {name!r}; choose from {sorted(_BACKENDS)}")
    return _BACKENDS[name]()
