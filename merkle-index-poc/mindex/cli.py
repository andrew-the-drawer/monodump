"""Command line client.

    python -m mindex init   <dir> --workspace alice [--server URL] [--key-from FILE]
    python -m mindex sync   <dir> [--tree-only]
    python -m mindex search <dir> "where do we retry requests" [-k 5] [--show-encrypted]
    python -m mindex fork   <dir> --source alice
    python -m mindex tree   <dir> [--depth 2]      # print the local Merkle tree
    python -m mindex stats  <dir>
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path

from .client import Workspace
from .merkle import DIR, Node, build_tree


def _print_tree(node: Node, depth: int, indent: int = 0) -> None:
    label = node.name or "<root>"
    suffix = "/" if node.kind == DIR else ""
    print(f"{'  ' * indent}{node.hash[:12]}  {label}{suffix}")
    if indent < depth:
        for child in node.children.values():
            _print_tree(child, depth, indent + 1)


def main(argv: list[str] | None = None) -> None:
    p = argparse.ArgumentParser(prog="mindex")
    sub = p.add_subparsers(dest="cmd", required=True)

    s = sub.add_parser("init")
    s.add_argument("dir", type=Path)
    s.add_argument("--workspace", required=True)
    s.add_argument("--server", default="http://127.0.0.1:8765")
    s.add_argument("--key-from", type=Path, help="reuse a teammate's key file (needed for fork)")

    s = sub.add_parser("sync")
    s.add_argument("dir", type=Path)
    s.add_argument("--tree-only", action="store_true", help="phase A only: send hashes, no content")

    s = sub.add_parser("search")
    s.add_argument("dir", type=Path)
    s.add_argument("query")
    s.add_argument("-k", type=int, default=5)
    s.add_argument("--show-encrypted", action="store_true", help="also print what the server returned")

    s = sub.add_parser("fork")
    s.add_argument("dir", type=Path)
    s.add_argument("--source", required=True)

    s = sub.add_parser("tree")
    s.add_argument("dir", type=Path)
    s.add_argument("--depth", type=int, default=2)

    s = sub.add_parser("stats")
    s.add_argument("dir", type=Path)

    a = p.parse_args(argv)

    if a.cmd == "init":
        Workspace.init(a.dir, a.workspace, a.server, a.key_from)
        print(f"initialised {a.dir}/.mindex for workspace {a.workspace!r}")
    elif a.cmd == "tree":
        _print_tree(build_tree(a.dir), a.depth)
    elif a.cmd == "sync":
        print(Workspace(a.dir).sync(tree_only=a.tree_only).pretty())
    elif a.cmd == "search":
        for r in Workspace(a.dir).search(a.query, a.k):
            print(f"── {r['path']}:{r['start_line']}-{r['end_line']}  score={r['score']:.3f}")
            if a.show_encrypted:
                print(f"   server saw: {r['encrypted_path']}")
            print("\n".join("   " + line for line in r["snippet"].splitlines()[:12]))
            print()
    elif a.cmd == "fork":
        print(json.dumps(Workspace(a.dir).fork_from(a.source), indent=2))
    elif a.cmd == "stats":
        print(json.dumps(Workspace(a.dir).stats(), indent=2))


if __name__ == "__main__":
    main()
