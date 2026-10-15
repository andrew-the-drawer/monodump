"""Server-side persistence in one SQLite file.

What the server keeps, and nothing else:

    tree_nodes  (workspace, path, parent, name, hash, kind)
        The client's Merkle tree with *encrypted* paths. This is the server's
        record of what each workspace claims to have.

    chunks      (workspace, path, file_hash, start_line, end_line, chunk_hash)
        Pointers: "lines 31-60 of encrypted path P, in the version of the file
        with hash H, embed to the vector cached under chunk_hash". No text.

    ingested    (workspace, path, file_hash)
        Which file versions have actually been chunked + embedded. The tree
        alone can't tell "server knows the hash" from "server indexed the
        content" (phase A of a sync records hashes before any upload), so
        `pending_files` compares the two and sync uploads the difference.

    embeddings  (model, chunk_hash, vector)
        Content-addressed cache shared by every workspace. Identical chunks
        (the same code in a teammate's clone, a vendored library) are embedded
        once.

Plaintext file content only ever lives in memory during ingest.
Run `sqlite3 .mindex-server/index.db .dump | grep <some identifier>` to check.
"""

from __future__ import annotations

import sqlite3
from pathlib import Path

import numpy as np

SCHEMA = """
CREATE TABLE IF NOT EXISTS tree_nodes (
    workspace TEXT NOT NULL,
    path      TEXT NOT NULL,
    parent    TEXT,            -- NULL for the root
    name      TEXT NOT NULL,   -- encrypted last segment ("" for the root)
    hash      TEXT NOT NULL,
    kind      TEXT NOT NULL,
    PRIMARY KEY (workspace, path)
);
CREATE INDEX IF NOT EXISTS tree_parent ON tree_nodes(workspace, parent);

CREATE TABLE IF NOT EXISTS chunks (
    workspace  TEXT NOT NULL,
    path       TEXT NOT NULL,
    file_hash  TEXT NOT NULL,
    start_line INTEGER NOT NULL,
    end_line   INTEGER NOT NULL,
    chunk_hash TEXT NOT NULL
);
CREATE INDEX IF NOT EXISTS chunks_path ON chunks(workspace, path);

CREATE TABLE IF NOT EXISTS ingested (
    workspace TEXT NOT NULL,
    path      TEXT NOT NULL,
    file_hash TEXT NOT NULL,
    PRIMARY KEY (workspace, path)
);

CREATE TABLE IF NOT EXISTS embeddings (
    model      TEXT NOT NULL,
    chunk_hash TEXT NOT NULL,
    vector     BLOB NOT NULL,
    PRIMARY KEY (model, chunk_hash)
);
"""


def _parent_and_name(path: str) -> tuple[str | None, str]:
    if path == "":
        return None, ""
    parent, _, name = path.rpartition("/")
    return parent, name


class Store:
    def __init__(self, db_path: Path):
        db_path.parent.mkdir(parents=True, exist_ok=True)
        self.db = sqlite3.connect(db_path, check_same_thread=False)
        self.db.executescript(SCHEMA)

    # ---------------------------------------------------------------- tree

    def get_nodes(self, ws: str, paths: list[str]) -> dict[str, dict | None]:
        out: dict[str, dict | None] = {}
        for p in paths:
            row = self.db.execute(
                "SELECT hash, kind FROM tree_nodes WHERE workspace=? AND path=?", (ws, p)
            ).fetchone()
            if row is None:
                out[p] = None
                continue
            children = self.db.execute(
                "SELECT name, hash, kind FROM tree_nodes WHERE workspace=? AND parent=?", (ws, p)
            ).fetchall()
            out[p] = {
                "hash": row[0],
                "kind": row[1],
                "children": [{"name": n, "hash": h, "kind": k} for n, h, k in children],
            }
        return out

    def apply_tree(self, ws: str, upserts: list[dict], deletes: list[str]) -> None:
        with self.db:
            for p in deletes:
                self._delete_prefix(ws, p)
            for u in upserts:
                parent, name = _parent_and_name(u["path"])
                self.db.execute(
                    "INSERT OR REPLACE INTO tree_nodes VALUES (?,?,?,?,?,?)",
                    (ws, u["path"], parent, name, u["hash"], u["kind"]),
                )

    def _delete_prefix(self, ws: str, path: str) -> None:
        like = path.replace("\\", "\\\\").replace("%", "\\%").replace("_", "\\_") + "/%"
        for table in ("tree_nodes", "chunks", "ingested"):
            self.db.execute(
                f"DELETE FROM {table} WHERE workspace=? AND (path=? OR path LIKE ? ESCAPE '\\')",
                (ws, path, like),
            )

    def file_hash(self, ws: str, path: str) -> str | None:
        row = self.db.execute(
            "SELECT hash FROM tree_nodes WHERE workspace=? AND path=? AND kind='file'", (ws, path)
        ).fetchone()
        return row[0] if row else None

    # ---------------------------------------------------------------- chunks

    def replace_chunks(self, ws: str, path: str, file_hash: str, rows: list[tuple[int, int, str]]) -> None:
        with self.db:
            self.db.execute("DELETE FROM chunks WHERE workspace=? AND path=?", (ws, path))
            self.db.executemany(
                "INSERT INTO chunks VALUES (?,?,?,?,?,?)",
                [(ws, path, file_hash, s, e, ch) for s, e, ch in rows],
            )
            self.db.execute("INSERT OR REPLACE INTO ingested VALUES (?,?,?)", (ws, path, file_hash))

    def is_ingested(self, ws: str, path: str, file_hash: str) -> bool:
        return self.db.execute(
            "SELECT 1 FROM ingested WHERE workspace=? AND path=? AND file_hash=?", (ws, path, file_hash)
        ).fetchone() is not None

    def pending_files(self, ws: str) -> list[str]:
        """Files in the tree whose current hash has not been ingested yet."""
        rows = self.db.execute(
            """
            SELECT t.path FROM tree_nodes t
            LEFT JOIN ingested i ON i.workspace=t.workspace AND i.path=t.path AND i.file_hash=t.hash
            WHERE t.workspace=? AND t.kind='file' AND i.path IS NULL
            """,
            (ws,),
        ).fetchall()
        return [r[0] for r in rows]

    def searchable_chunks(self, ws: str, model: str) -> tuple[list[tuple], np.ndarray]:
        """Chunks the workspace may see, with their vectors.

        Proof of possession: a chunk is only returned if its file_hash equals the
        hash this workspace's own tree holds for that path. After a fork, chunks
        copied from a teammate for files this client does not have (or has a
        different version of) stay invisible until the client uploads its own copy.
        """
        rows = self.db.execute(
            """
            SELECT c.path, c.start_line, c.end_line, e.vector
            FROM chunks c
            JOIN tree_nodes t ON t.workspace=c.workspace AND t.path=c.path AND t.hash=c.file_hash
            JOIN embeddings e ON e.model=? AND e.chunk_hash=c.chunk_hash
            WHERE c.workspace=?
            """,
            (model, ws),
        ).fetchall()
        if not rows:
            return [], np.zeros((0, 0), dtype=np.float32)
        meta = [r[:3] for r in rows]
        vecs = np.stack([np.frombuffer(r[3], dtype=np.float32) for r in rows])
        return meta, vecs

    # ---------------------------------------------------------------- embedding cache

    def cached_vectors(self, model: str, chunk_hashes: list[str]) -> dict[str, np.ndarray]:
        out = {}
        for ch in set(chunk_hashes):
            row = self.db.execute(
                "SELECT vector FROM embeddings WHERE model=? AND chunk_hash=?", (model, ch)
            ).fetchone()
            if row:
                out[ch] = np.frombuffer(row[0], dtype=np.float32)
        return out

    def put_vectors(self, model: str, vectors: dict[str, np.ndarray]) -> None:
        with self.db:
            self.db.executemany(
                "INSERT OR IGNORE INTO embeddings VALUES (?,?,?)",
                [(model, ch, v.astype(np.float32).tobytes()) for ch, v in vectors.items()],
            )

    # ---------------------------------------------------------------- workspaces

    def fork(self, src: str, dst: str) -> None:
        with self.db:
            for table in ("tree_nodes", "chunks", "ingested"):
                self.db.execute(f"DELETE FROM {table} WHERE workspace=?", (dst,))
            self.db.execute(
                "INSERT INTO tree_nodes SELECT ?, path, parent, name, hash, kind FROM tree_nodes WHERE workspace=?",
                (dst, src),
            )
            self.db.execute(
                "INSERT INTO chunks SELECT ?, path, file_hash, start_line, end_line, chunk_hash FROM chunks WHERE workspace=?",
                (dst, src),
            )
            self.db.execute(
                "INSERT INTO ingested SELECT ?, path, file_hash FROM ingested WHERE workspace=?", (dst, src)
            )

    def stats(self, ws: str) -> dict:
        q = lambda sql, *a: self.db.execute(sql, a).fetchone()[0]  # noqa: E731
        return {
            "tree_nodes": q("SELECT COUNT(*) FROM tree_nodes WHERE workspace=?", ws),
            "files": q("SELECT COUNT(*) FROM tree_nodes WHERE workspace=? AND kind='file'", ws),
            "chunks": q("SELECT COUNT(*) FROM chunks WHERE workspace=?", ws),
            "pending_files": len(self.pending_files(ws)),
            "embeddings_cached_all_workspaces": q("SELECT COUNT(*) FROM embeddings"),
        }
