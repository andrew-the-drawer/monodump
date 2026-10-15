"""Merkle tree over a workspace, and the diff that drives incremental sync.

Hashing scheme (git-like, domain-separated so a file can never collide with a dir):

    file hash = sha256("blob\\0" + file bytes)
    dir  hash = sha256("tree\\0" + for each child sorted by name: "<kind> <name> <hash>\\n")

So any change anywhere changes the hash of every ancestor up to the root,
and an unchanged subtree keeps its hash no matter what happens elsewhere.

The diff (`diff_against_remote`) is the core of the idea: compare the root
hash first; only for directories whose hashes differ do we ask the server for
their children. Unchanged subtrees are pruned without ever being looked at,
so the cost of a sync is proportional to (changed files x depth), not repo size.
The descent is done level by level, so the number of round trips equals the
depth of the deepest change.
"""

from __future__ import annotations

import hashlib
from dataclasses import dataclass, field
from pathlib import Path
from typing import Callable, Iterator

import pathspec

from .crypto import PathCipher

FILE, DIR = "file", "dir"

# Never index these, regardless of ignore files.
ALWAYS_IGNORED = [".git/", ".mindex/", "venv/", ".venv/", "node_modules/", "__pycache__/"]
IGNORE_FILES = (".gitignore", ".mindexignore")
MAX_FILE_BYTES = 1_000_000


@dataclass
class Node:
    name: str  # plaintext segment; "" for the root
    kind: str  # FILE or DIR
    hash: str
    rel_path: str  # plaintext path relative to the workspace root
    children: dict[str, "Node"] = field(default_factory=dict)

    def walk(self) -> Iterator["Node"]:
        yield self
        for child in self.children.values():
            yield from child.walk()

    def files(self) -> Iterator["Node"]:
        return (n for n in self.walk() if n.kind == FILE)


def hash_file_bytes(data: bytes) -> str:
    return hashlib.sha256(b"blob\0" + data).hexdigest()


def hash_dir(children: dict[str, Node]) -> str:
    h = hashlib.sha256(b"tree\0")
    for name in sorted(children):
        c = children[name]
        h.update(f"{c.kind} {name} {c.hash}\n".encode())
    return h.hexdigest()


def _load_ignore(root: Path) -> pathspec.PathSpec:
    lines = list(ALWAYS_IGNORED)
    for name in IGNORE_FILES:
        f = root / name
        if f.exists():
            lines += f.read_text().splitlines()
    return pathspec.PathSpec.from_lines("gitignore", lines)


def _is_indexable(data: bytes) -> bool:
    # Only UTF-8 text under the size cap is indexed; binaries never enter the tree.
    if len(data) > MAX_FILE_BYTES or b"\0" in data[:8192]:
        return False
    try:
        data.decode("utf-8")
    except UnicodeDecodeError:
        return False
    return True


def build_tree(root: Path) -> Node:
    """Hash the whole workspace. Only the root-level ignore files are honoured."""
    root = root.resolve()
    spec = _load_ignore(root)

    def build(dir_path: Path, rel: str) -> Node:
        children: dict[str, Node] = {}
        for entry in sorted(dir_path.iterdir()):
            child_rel = f"{rel}/{entry.name}" if rel else entry.name
            if entry.is_symlink():
                continue
            if entry.is_dir():
                if spec.match_file(child_rel + "/"):
                    continue
                sub = build(entry, child_rel)
                if sub.children:  # empty dirs carry no content, skip them
                    children[entry.name] = sub
            elif entry.is_file():
                if spec.match_file(child_rel):
                    continue
                data = entry.read_bytes()
                if not _is_indexable(data):
                    continue
                children[entry.name] = Node(entry.name, FILE, hash_file_bytes(data), child_rel)
        return Node(dir_path.name if rel else "", DIR, hash_dir(children), rel, children)

    return build(root, "")


# --------------------------------------------------------------------------- diff


@dataclass
class TreeRecord:
    """One node as the server stores it: encrypted path + hash + kind."""

    path: str
    hash: str
    kind: str

    def as_json(self) -> dict:
        return {"path": self.path, "hash": self.hash, "kind": self.kind}


@dataclass
class ChangedFile:
    rel_path: str
    enc_path: str
    hash: str


@dataclass
class Diff:
    upserts: list[TreeRecord] = field(default_factory=list)  # tree nodes to write
    deletes: list[str] = field(default_factory=list)  # encrypted path prefixes to drop
    changed_files: list[ChangedFile] = field(default_factory=list)  # content to upload
    round_trips: int = 0
    nodes_compared: int = 0

    @property
    def empty(self) -> bool:
        return not (self.upserts or self.deletes)


# fetch_nodes(enc_paths) -> {enc_path: {"hash", "kind", "children": [{"name","hash","kind"}]} | None}
FetchNodes = Callable[[list[str]], dict[str, dict | None]]


def diff_against_remote(local: Node, cipher: PathCipher, fetch_nodes: FetchNodes) -> Diff:
    """Find what the server is missing, descending only into mismatched subtrees."""
    diff = Diff()

    def add_whole_subtree(node: Node, enc_path: str) -> None:
        # The server has nothing here, so there is nothing to compare: send it all.
        diff.upserts.append(TreeRecord(enc_path, node.hash, node.kind))
        if node.kind == FILE:
            diff.changed_files.append(ChangedFile(node.rel_path, enc_path, node.hash))
            return
        for name, child in node.children.items():
            add_whole_subtree(child, _join(enc_path, cipher.encrypt_segment(name)))

    diff.round_trips += 1
    remote_root = fetch_nodes([""]).get("")
    diff.nodes_compared += 1
    if remote_root and remote_root["hash"] == local.hash:
        return diff  # the whole point: one hash comparison proves nothing changed
    if remote_root is None:
        add_whole_subtree(local, "")
        return diff

    # Level-by-level descent. `frontier` holds dirs whose hash differs from the server.
    frontier: list[tuple[str, Node, dict]] = [("", local, remote_root)]
    while frontier:
        next_level: list[tuple[str, Node]] = []
        for enc_path, node, remote in frontier:
            diff.upserts.append(TreeRecord(enc_path, node.hash, DIR))
            remote_children = {c["name"]: c for c in remote["children"]}
            local_enc_names = set()
            for name, child in node.children.items():
                enc_name = cipher.encrypt_segment(name)
                local_enc_names.add(enc_name)
                child_path = _join(enc_path, enc_name)
                rc = remote_children.get(enc_name)
                diff.nodes_compared += 1
                if rc is not None and rc["kind"] == child.kind and rc["hash"] == child.hash:
                    continue  # identical subtree, pruned
                if rc is not None and rc["kind"] != child.kind:
                    diff.deletes.append(child_path)  # file became dir or vice versa
                    rc = None
                if rc is None:
                    add_whole_subtree(child, child_path)
                elif child.kind == FILE:
                    diff.upserts.append(TreeRecord(child_path, child.hash, FILE))
                    diff.changed_files.append(ChangedFile(child.rel_path, child_path, child.hash))
                else:
                    next_level.append((child_path, child))
            for enc_name in remote_children.keys() - local_enc_names:
                diff.deletes.append(_join(enc_path, enc_name))

        if next_level:
            diff.round_trips += 1
            remote_nodes = fetch_nodes([p for p, _ in next_level])
            frontier = [(p, n, remote_nodes[p]) for p, n in next_level]
        else:
            frontier = []
    return diff


def _join(parent: str, segment: str) -> str:
    return f"{parent}/{segment}" if parent else segment
