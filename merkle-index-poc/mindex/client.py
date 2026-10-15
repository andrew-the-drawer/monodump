"""Client workflows: init, sync, search, fork.

Client state lives in <workspace>/.mindex/:
    key          64-byte AES-SIV key for path encryption. Never sent to the server.
    config.json  {"workspace": id, "server": url}
"""

from __future__ import annotations

import json
import shutil
from dataclasses import dataclass
from pathlib import Path

import httpx

from .crypto import PathCipher, load_or_create_key
from .merkle import build_tree, diff_against_remote, hash_file_bytes

STATE_DIR = ".mindex"
UPLOAD_BATCH_BYTES = 2_000_000


@dataclass
class SyncReport:
    files_in_workspace: int
    workspace_bytes: int
    round_trips: int
    nodes_compared: int
    tree_upserts: int
    tree_deletes: int
    files_uploaded: int
    bytes_uploaded: int
    chunks: int = 0
    embedded: int = 0
    cache_hits: int = 0

    def pretty(self) -> str:
        pct = 100 * self.bytes_uploaded / self.workspace_bytes if self.workspace_bytes else 0
        return "\n".join([
            f"workspace:        {self.files_in_workspace} files, {self.workspace_bytes:,} bytes",
            f"merkle descent:   {self.round_trips} round trips, {self.nodes_compared} nodes compared",
            f"tree updates:     {self.tree_upserts} upserts, {self.tree_deletes} deletes",
            f"content uploaded: {self.files_uploaded} files, {self.bytes_uploaded:,} bytes ({pct:.1f}% of workspace)",
            f"server ingest:    {self.chunks} chunks, {self.embedded} newly embedded, {self.cache_hits} cache hits",
        ])


class Workspace:
    def __init__(self, root: Path, http: httpx.Client | None = None):
        self.root = root.resolve()
        state = self.root / STATE_DIR
        cfg = json.loads((state / "config.json").read_text())
        self.ws_id: str = cfg["workspace"]
        self.cipher = PathCipher(load_or_create_key(state / "key"))
        self.http = http or httpx.Client(base_url=cfg["server"], timeout=600)

    @staticmethod
    def init(root: Path, workspace_id: str, server: str, key_from: Path | None = None) -> None:
        state = root.resolve() / STATE_DIR
        state.mkdir(parents=True, exist_ok=True)
        if key_from:
            shutil.copyfile(key_from, state / "key")
        load_or_create_key(state / "key")
        (state / "config.json").write_text(json.dumps({"workspace": workspace_id, "server": server}, indent=2))

    def _post(self, endpoint: str, body: dict) -> dict:
        r = self.http.post(f"/ws/{self.ws_id}/{endpoint}", json=body)
        r.raise_for_status()
        return r.json()

    def sync(self, tree_only: bool = False) -> SyncReport:
        local = build_tree(self.root)
        diff = diff_against_remote(local, self.cipher, lambda paths: self._post("nodes", {"paths": paths})["nodes"])

        all_files = list(local.files())
        report = SyncReport(
            files_in_workspace=len(all_files),
            workspace_bytes=sum((self.root / f.rel_path).stat().st_size for f in all_files),
            round_trips=diff.round_trips,
            nodes_compared=diff.nodes_compared,
            tree_upserts=len(diff.upserts),
            tree_deletes=len(diff.deletes),
            files_uploaded=0,
            bytes_uploaded=0,
        )
        # Phase A: hashes only. From this moment the server knows exactly which
        # file versions we hold, which is what search filtering relies on.
        if not diff.empty:
            self._post("tree", {"upserts": [u.as_json() for u in diff.upserts], "deletes": diff.deletes})
        if tree_only:
            return report

        # Phase B: upload content for every file the server has not indexed at
        # its current hash. Usually that is exactly diff.changed_files, but
        # asking the server also covers an earlier --tree-only or interrupted sync.
        r = self.http.get(f"/ws/{self.ws_id}/pending")
        r.raise_for_status()
        local_hashes = {f.rel_path: f.hash for f in all_files}
        batch, size = [], 0
        for enc_path in r.json()["paths"]:
            rel = self.cipher.decrypt_path(enc_path)
            data = (self.root / rel).read_bytes()
            if hash_file_bytes(data) != local_hashes.get(rel):
                continue  # edited since we hashed it; the next sync picks it up
            content = data.decode("utf-8")
            batch.append({"path": enc_path, "hash": local_hashes[rel], "content": content})
            size += len(content)
            if size >= UPLOAD_BATCH_BYTES:
                self._upload(batch, report)
                batch, size = [], 0
        if batch:
            self._upload(batch, report)
        return report

    def _upload(self, batch: list[dict], report: SyncReport) -> None:
        res = self._post("files", {"files": batch})
        report.files_uploaded += len(batch)
        report.bytes_uploaded += sum(len(f["content"].encode()) for f in batch)
        report.chunks += res["chunks"]
        report.embedded += res["embedded"]
        report.cache_hits += res["cache_hits"]

    def search(self, query: str, k: int = 5) -> list[dict]:
        """Server returns encrypted pointers; we decrypt and read the lines from local disk."""
        results = self._post("search", {"query": query, "k": k})["results"]
        out = []
        for r in results:
            rel = self.cipher.decrypt_path(r["path"])
            lines = (self.root / rel).read_text(errors="replace").splitlines()
            snippet = "\n".join(lines[r["start_line"] - 1 : r["end_line"]])
            out.append({**r, "path": rel, "encrypted_path": r["path"], "snippet": snippet})
        return out

    def fork_from(self, source_ws: str) -> dict:
        return self._post("fork", {"source": source_ws})

    def stats(self) -> dict:
        r = self.http.get(f"/ws/{self.ws_id}/stats")
        r.raise_for_status()
        return r.json()
