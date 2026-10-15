"""The indexing server. See docs/02-protocol.md for the wire protocol.

Endpoints (all under /ws/{workspace}):

    POST /nodes   {paths}                -> the server's node + children for each encrypted path
    POST /tree    {upserts, deletes}     -> phase A of sync: record hashes only, no content
    GET  /pending                        -> files in the tree whose content is not indexed yet
    POST /files   {files: [{path, hash, content}]}
                                         -> phase B: chunk + embed + store pointers, drop text
    POST /search  {query, k}             -> [{path, start_line, end_line, score}] (encrypted paths)
    POST /fork    {source}               -> copy another workspace's tree + chunk pointers
    GET  /stats

Run with:  MINDEX_EMBEDDER=minilm uvicorn mindex.server:app --port 8765
"""

from __future__ import annotations

import os
from pathlib import Path

import numpy as np
from fastapi import FastAPI, HTTPException
from pydantic import BaseModel

from .chunker import chunk_text
from .embed import get_embedder
from .merkle import hash_file_bytes
from .store import Store


class NodesReq(BaseModel):
    paths: list[str]


class TreeRecordIn(BaseModel):
    path: str
    hash: str
    kind: str


class TreeReq(BaseModel):
    upserts: list[TreeRecordIn] = []
    deletes: list[str] = []


class FileIn(BaseModel):
    path: str
    hash: str
    content: str


class FilesReq(BaseModel):
    files: list[FileIn]


class SearchReq(BaseModel):
    query: str
    k: int = 5


class ForkReq(BaseModel):
    source: str


def create_app(db_path: Path | None = None, embedder: str | None = None) -> FastAPI:
    db_path = db_path or Path(os.environ.get("MINDEX_DB", ".mindex-server/index.db"))
    store = Store(db_path)
    emb = get_embedder(embedder)
    app = FastAPI(title="mindex server")

    @app.post("/ws/{ws}/nodes")
    def nodes(ws: str, req: NodesReq):
        return {"nodes": store.get_nodes(ws, req.paths)}

    @app.post("/ws/{ws}/tree")
    def tree(ws: str, req: TreeReq):
        store.apply_tree(ws, [u.model_dump() for u in req.upserts], req.deletes)
        return {"upserts": len(req.upserts), "deletes": len(req.deletes)}

    @app.get("/ws/{ws}/pending")
    def pending(ws: str):
        return {"paths": store.pending_files(ws)}

    @app.post("/ws/{ws}/files")
    def files(ws: str, req: FilesReq):
        embedded = cache_hits = skipped = chunks_total = 0
        for f in req.files:
            data = f.content.encode()
            if hash_file_bytes(data) != f.hash:
                raise HTTPException(400, f"content does not match hash for {f.path}")
            if store.file_hash(ws, f.path) != f.hash:
                raise HTTPException(409, f"tree has no node {f.path} with that hash; POST /tree first")
            if store.is_ingested(ws, f.path, f.hash):
                skipped += 1  # already indexed (e.g. copied by a fork)
                continue

            chunks = chunk_text(f.content)
            hashes = [c.hash for c in chunks]
            cached = store.cached_vectors(emb.name, hashes)
            todo = {c.hash: c.text for c in chunks if c.hash not in cached}
            if todo:
                vecs = emb.embed(list(todo.values()))
                store.put_vectors(emb.name, dict(zip(todo.keys(), vecs)))
            store.replace_chunks(ws, f.path, f.hash, [(c.start_line, c.end_line, c.hash) for c in chunks])

            embedded += len(todo)
            cache_hits += len(chunks) - len(todo)
            chunks_total += len(chunks)
            # f.content goes out of scope here: the plaintext is never written anywhere.
        return {"files": len(req.files), "skipped_already_indexed": skipped, "chunks": chunks_total,
                "embedded": embedded, "cache_hits": cache_hits}

    @app.post("/ws/{ws}/search")
    def search(ws: str, req: SearchReq):
        meta, vecs = store.searchable_chunks(ws, emb.name)
        if not meta:
            return {"results": []}
        q = emb.embed([req.query])[0]
        scores = _normalize(vecs) @ _normalize(q[None, :])[0]
        top = np.argsort(-scores)[: req.k]
        return {"results": [
            {"path": meta[i][0], "start_line": meta[i][1], "end_line": meta[i][2], "score": float(scores[i])}
            for i in top
        ]}

    @app.post("/ws/{ws}/fork")
    def fork(ws: str, req: ForkReq):
        store.fork(req.source, ws)
        return store.stats(ws)

    @app.get("/ws/{ws}/stats")
    def stats(ws: str):
        return {"embedder": emb.name, **store.stats(ws)}

    return app


def _normalize(m: np.ndarray) -> np.ndarray:
    return m / np.maximum(np.linalg.norm(m, axis=1, keepdims=True), 1e-12)


def __getattr__(name: str):
    # Lazily build the module-level `app` so importing mindex.server in tests
    # doesn't open the default DB or load a model.
    if name == "app":
        return create_app()
    raise AttributeError(name)
