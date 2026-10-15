"""End-to-end tests, in-process (FastAPI TestClient) with the dependency-free hash embedder.

Run from merkle-index-poc/:  ../venv/bin/python -m pytest -q
"""

from __future__ import annotations

import shutil
import sqlite3
from pathlib import Path

import pytest
from fastapi.testclient import TestClient

from mindex.client import Workspace
from mindex.crypto import PathCipher
from mindex.merkle import build_tree
from mindex.server import create_app


def write(root: Path, rel: str, text: str) -> None:
    p = root / rel
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(text)


def make_repo(root: Path, n_pkgs: int = 5, files_per_pkg: int = 8) -> None:
    for i in range(n_pkgs):
        for j in range(files_per_pkg):
            body = "\n".join(f"def pkg{i}_func{j}_{k}(x):\n    return x + {k}" for k in range(20))
            write(root, f"pkg{i}/sub/mod{j}.py", body)
    write(root, "net/retry.py", "def retry_with_backoff(request):\n    # exponential backoff for flaky HTTP\n    pass\n")
    write(root, ".gitignore", "secrets.env\n")
    write(root, "secrets.env", "API_KEY=hunter2\n")


@pytest.fixture
def server(tmp_path):
    app = create_app(tmp_path / "server" / "index.db", embedder="hash")
    return TestClient(app), tmp_path / "server" / "index.db"


def open_ws(root: Path, http, name: str, key_from: Path | None = None) -> Workspace:
    Workspace.init(root, name, "http://testserver", key_from)
    return Workspace(root, http=http)


# ------------------------------------------------------------------ merkle basics


def test_hash_changes_propagate_only_up_the_spine(tmp_path):
    make_repo(tmp_path)
    before = build_tree(tmp_path)
    write(tmp_path, "pkg3/sub/mod2.py", "changed = True\n")
    after = build_tree(tmp_path)

    assert before.hash != after.hash
    assert before.children["pkg3"].hash != after.children["pkg3"].hash
    for name in ("pkg0", "pkg1", "pkg2", "pkg4", "net"):
        assert before.children[name].hash == after.children[name].hash


def test_ignored_files_never_enter_the_tree(tmp_path):
    make_repo(tmp_path)
    paths = {n.rel_path for n in build_tree(tmp_path).files()}
    assert "secrets.env" not in paths
    assert "net/retry.py" in paths


def test_path_encryption_is_deterministic_and_reversible():
    c = PathCipher(b"k" * 64)
    enc = c.encrypt_path("src/app/main.py")
    assert enc == c.encrypt_path("src/app/main.py")
    assert enc.startswith(c.encrypt_path("src/app") + "/")
    assert "main" not in enc and "src" not in enc
    assert c.decrypt_path(enc) == "src/app/main.py"


# ------------------------------------------------------------------ sync


def test_incremental_sync_uploads_only_changes(tmp_path, server):
    http, _ = server
    root = tmp_path / "repo"
    make_repo(root)
    ws = open_ws(root, http, "alice")

    first = ws.sync()
    assert first.files_uploaded == first.files_in_workspace == 42  # 40 modules + retry.py + .gitignore

    noop = ws.sync()
    assert noop.round_trips == 1 and noop.nodes_compared == 1 and noop.files_uploaded == 0

    write(root, "pkg3/sub/mod2.py", "def brand_new():\n    pass\n")
    one = ws.sync()
    assert one.files_uploaded == 1
    assert one.round_trips == 3  # root -> pkg3 -> pkg3/sub
    assert one.nodes_compared < 20  # siblings get compared by hash, never descended into


def test_deletes_and_renames(tmp_path, server):
    http, _ = server
    root = tmp_path / "repo"
    make_repo(root)
    ws = open_ws(root, http, "alice")
    ws.sync()

    shutil.rmtree(root / "pkg1")
    (root / "net/retry.py").rename(root / "net/retries.py")
    r = ws.sync()
    assert r.tree_deletes == 2  # pkg1 subtree, old retry.py
    assert r.files_uploaded == 1  # renamed file: new path, so re-ingested (cache makes it free)
    assert r.cache_hits == r.chunks and r.embedded == 0
    assert ws.stats()["files"] == 42 - 8


def test_server_tree_matches_a_fresh_full_upload(tmp_path, server):
    """After many incremental syncs, the server's root hash equals the local root hash."""
    http, _ = server
    root = tmp_path / "repo"
    make_repo(root)
    ws = open_ws(root, http, "alice")
    ws.sync()
    write(root, "pkg0/new/deep/file.py", "x = 1\n")
    shutil.rmtree(root / "pkg2")
    write(root, "pkg4/sub/mod0.py", "y = 2\n")
    ws.sync()
    remote_root = http.post("/ws/alice/nodes", json={"paths": [""]}).json()["nodes"][""]
    assert remote_root["hash"] == build_tree(root).hash


# ------------------------------------------------------------------ privacy + search


def test_server_stores_no_plaintext(tmp_path, server):
    http, db_path = server
    root = tmp_path / "repo"
    make_repo(root)
    ws = open_ws(root, http, "alice")
    ws.sync()

    dump = "\n".join(sqlite3.connect(db_path).iterdump())
    for needle in ("retry_with_backoff", "exponential", "retry.py", "pkg3", "mod2"):
        assert needle not in dump


def test_search_returns_pointers_resolved_locally(tmp_path, server):
    http, _ = server
    root = tmp_path / "repo"
    make_repo(root)
    ws = open_ws(root, http, "alice")
    ws.sync()

    raw = http.post("/ws/alice/search", json={"query": "retry with backoff", "k": 1}).json()["results"][0]
    assert "retry" not in raw["path"]  # the server only knows an opaque path

    hit = ws.search("retry with backoff", k=1)[0]
    assert hit["path"] == "net/retry.py"
    assert "exponential backoff" in hit["snippet"]


# ------------------------------------------------------------------ team reuse


def test_fork_reuses_index_and_enforces_possession(tmp_path, server):
    http, _ = server
    a_root, b_root = tmp_path / "alice", tmp_path / "bob"
    make_repo(a_root)
    write(a_root, "net/retry.py", "def retry_with_backoff(request):\n    # exponential backoff, alice's private fix\n")
    alice = open_ws(a_root, http, "alice")
    alice.sync()

    make_repo(b_root)  # bob's clone: same repo but an older retry.py
    bob = open_ws(b_root, http, "bob", key_from=a_root / ".mindex" / "key")
    bob.fork_from("alice")

    # Phase A only: bob tells the server which versions he holds.
    r = bob.sync(tree_only=True)
    assert r.files_uploaded == 0
    assert r.tree_upserts == 3  # root, net/, net/retry.py; everything else matched alice

    # Alice's version of retry.py is in the copied chunks but bob can't prove he has it.
    paths = {h["path"] for h in bob.search("retry backoff", k=50)}
    assert "net/retry.py" not in paths
    assert "pkg0/sub/mod0.py" in paths  # identical files were reused, no upload needed

    r = bob.sync()
    assert r.files_uploaded == 1
    hit = bob.search("retry with backoff", k=1)[0]
    assert hit["path"] == "net/retry.py" and "private fix" not in hit["snippet"]
