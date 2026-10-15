# merkle-index-poc

A learning PoC of how Cursor indexes customer codebases for semantic search **without storing the code**:

- a **Merkle tree** on the client, so each sync uploads only what changed
- **encrypted file paths**, so the server stores pointers it can't read
- **content-addressed embedding caching**, so teammates' clones are almost free to index
- **proof of possession**, so reusing a teammate's index never shows you code you don't have

…and an **embedding-inversion attack** on the server's DB, to show where the privacy story ends.

```
 CLIENT (has code + key)                         SERVER (has hashes, vectors, ciphertext paths)
 ───────────────────────                         ───────────────────────────────────────────────
 build Merkle tree ──── root hash ─────────────▶ compare with stored tree
                   ◀─── children of mismatches ─  (repeat per level, only down changed paths)
 phase A ────────────── changed hashes ────────▶ tree_nodes      (what you hold)
 phase B ────────────── changed file content ──▶ chunk → embed → chunks + embeddings
                                                   plaintext dropped here ✂
 search "retry logic" ─────────────────────────▶ nearest neighbours, filtered by your hashes
 decrypt path, read lines   ◀── (enc_path, 31-60) ─
 from local disk → LLM
```

## Docs

| | |
|---|---|
| [docs/01-concepts.md](docs/01-concepts.md) | Merkle trees, why they make sync cheap, how each privacy measure works and what it does *not* protect against. Start here. |
| [docs/02-protocol.md](docs/02-protocol.md) | Wire protocol, server schema, sync algorithm step by step, design decisions. |
| [docs/03-inversion.md](docs/03-inversion.md) | Embedding-inversion attacks, how the vec2text demo works, measured results. |

## Layout

```
mindex/
  merkle.py    client: build the tree, level-by-level diff against the server
  crypto.py    client: AES-SIV per path segment (key stays in <workspace>/.mindex/key)
  client.py    client: sync (phase A hashes, phase B content), search, fork
  cli.py       python -m mindex {init,sync,search,fork,tree,stats}
  server.py    FastAPI app: /nodes /tree /pending /files /search /fork /stats
  store.py     SQLite: tree_nodes, chunks, ingested, embeddings. No plaintext.
  chunker.py   line-window chunking
  embed.py     hash | minilm | gtr embedders
scripts/
  demo.sh             end-to-end walkthrough on psf/requests
  inversion_demo.sh   index a toy repo with GTR, then invert the stored vectors
  invert_attack.py    the attacker (reads only index.db) + an evaluator (scores it)
tests/test_mindex.py  in-process tests, no model needed
```

## Setup

Uses the monodump root venv (see `../CLAUDE.md`):

```bash
cd monodump
source venv/bin/activate
pip install -r requirements.txt
cd merkle-index-poc
```

## Run it

```bash
python -m pytest -q          # 9 tests, ~1s, uses the dependency-free "hash" embedder
./scripts/demo.sh            # full walkthrough (downloads MiniLM ~90MB once)
./scripts/inversion_demo.sh  # the attack (downloads GTR + vec2text models ~2GB once)
```

Or drive it by hand:

```bash
MINDEX_EMBEDDER=minilm uvicorn mindex.server:app --port 8765 &   # server, DB in .mindex-server/
python -m mindex init   ~/code/myrepo --workspace me
python -m mindex tree   ~/code/myrepo --depth 1
python -m mindex sync   ~/code/myrepo                 # edit something, sync again, compare stats
python -m mindex search ~/code/myrepo "where do we parse config" --show-encrypted
sqlite3 .mindex-server/index.db .dump | less          # check: no code, no names
```

Server environment variables:

| var | default | |
|---|---|---|
| `MINDEX_EMBEDDER` | `minilm` | `hash` (no ML), `minilm` (semantic), `gtr` (needed for the inversion attack) |
| `MINDEX_DB` | `.mindex-server/index.db` | |
| `MINDEX_CHUNK_LINES` / `MINDEX_CHUNK_OVERLAP` | `30` / `5` | |

## What the demo shows (psf/requests, 122 files, 1.5 MB)

| step | round trips | nodes compared | uploaded |
|---|---|---|---|
| first sync | 1 | 1 | 122 files, 100% |
| re-sync, nothing changed | 1 | 1 | 0 |
| edit `src/requests/adapters.py` | 3 | 43 | 1 file, 1.8% (29 of 30 chunks were cache hits) |
| bob forks alice's index, edits 1 file | 3 | 43 | 2 files, 4.0% (66 of 67 chunks were cache hits) |

- `grep` of the server DB dump for `HTTPAdapter`, `adapters.py` and `def send` finds 0 matches.
- After bob's hashes-only sync, his searches never return alice's version of `adapters.py`. After he uploads his own copy, it is the top hit.

## Not done (on purpose)

The tree is rehashed in full on each sync. A real client caches hashes by mtime and uses file watchers. Chunks are line windows, not tree-sitter. Vector search is brute-force numpy. There is no auth: workspace ids are bearer names. Only the root `.gitignore` is honoured. See [docs/02-protocol.md § Gaps vs. production](docs/02-protocol.md#gaps-vs-production).
