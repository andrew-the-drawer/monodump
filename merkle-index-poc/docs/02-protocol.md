# 02 · Protocol and schema

All endpoints live under `/ws/{workspace}`. Every path in a request or response is **encrypted** (per-segment AES-SIV, base64url, joined with `/`). The root is the empty string `""`.

## Endpoints

| method | path | body → response | used for |
|---|---|---|---|
| POST | `/nodes` | `{paths: [p…]}` → `{nodes: {p: {hash, kind, children: [{name, hash, kind}]} \| null}}` | Merkle descent, one call per tree level |
| POST | `/tree` | `{upserts: [{path, hash, kind}], deletes: [p…]}` | phase A: record hashes; delete subtrees by prefix |
| GET | `/pending` | → `{paths: [p…]}` | files whose current hash has not been ingested |
| POST | `/files` | `{files: [{path, hash, content}]}` → counts | phase B: chunk, embed, store pointers, drop text |
| POST | `/search` | `{query, k}` → `{results: [{path, start_line, end_line, score}]}` | search, filtered by proof of possession |
| POST | `/fork` | `{source}` | copy another workspace's tree, chunks and ingest records |
| GET | `/stats` | | counts |

`/files` rejects content whose hash doesn't match (400), and files whose `(path, hash)` isn't in the tree yet (409: phase A must come first).

## Sync, step by step (`Workspace.sync`)

```
1. local = build_tree(workspace)                 # hash every file
2. diff  = diff_against_remote(local, …)         # Merkle descent
      POST /nodes [""]                            # compare root hashes
      equal? → diff is empty, skip to 4
      else for each level:
        for each child of a mismatched dir:
          same kind and hash  → prune
          missing on server   → upsert the whole subtree (no more queries)
          changed file        → upsert
          changed dir         → queue for the next level
          kind flipped        → delete the old one, upsert the new one
        server children with no local match → delete
        POST /nodes [all queued dirs]             # one round trip per level
3. POST /tree {upserts, deletes}                  # phase A
4. GET  /pending                                  # phase B
   for each pending path: decrypt, read, re-hash (skip if the file changed meanwhile)
   POST /files in ~2 MB batches
```

Why two phases? After phase A, the server knows exactly which version of every file you hold, so search filtering is correct straight away, even before the upload finishes. It also lets `--tree-only` work as a demo of proof of possession.

Why `/pending` and not just `diff.changed_files`? See "The trap the tests caught" in [01-concepts.md](01-concepts.md). Merkle state answers "what changed"; the `ingested` table answers "what's left to do". With both, an interrupted or tree-only sync recovers on the next run.

## Server schema (`mindex/store.py`)

```sql
tree_nodes (workspace, path, parent, name, hash, kind)   -- PK (workspace, path); index on parent
chunks     (workspace, path, file_hash, start_line, end_line, chunk_hash)
ingested   (workspace, path, file_hash)                  -- PK (workspace, path)
embeddings (model, chunk_hash, vector BLOB)              -- PK (model, chunk_hash); shared by all workspaces
```

Search query (proof of possession is the second `JOIN`):

```sql
SELECT c.path, c.start_line, c.end_line, e.vector
FROM chunks c
JOIN tree_nodes t ON t.workspace=c.workspace AND t.path=c.path AND t.hash=c.file_hash
JOIN embeddings e ON e.model=? AND e.chunk_hash=c.chunk_hash
WHERE c.workspace=?
```

## Design decisions

- **Hashes use plaintext names; the tree stores encrypted names.** The client is the only party that computes hashes, so the server never needs to verify them. Hashing over plaintext names keeps the hash independent of the key.
- **Domain separation** (`blob\0`, `tree\0`) means a file can never hash to the same value as a directory.
- **Empty directories and non-UTF-8 or >1 MB files are excluded** from the tree, so they can never be stuck in `pending`.
- **Embedding happens on the server**, as in Cursor. The query text is sent to the server too. A design where the client embeds would need the model on the client.
- **The embedding cache is keyed by `(model, chunk_hash)`**, so switching `MINDEX_EMBEDDER` never mixes vectors from different models.
- **Fork shares the path key.** Encrypted paths only line up between teammates who share a key (`init --key-from`). How a real product distributes that key (per team or per repo, through the account system) is outside this PoC.

## Gaps vs. production

| PoC | production |
|---|---|
| rehash the full tree on every sync | hash cache keyed by mtime/size, plus FS watchers |
| only the root `.gitignore` is honoured | nested ignore files, `.cursorignore` |
| line-window chunks | syntax-aware chunks (tree-sitter) |
| brute-force numpy cosine | ANN index (Turbopuffer, etc.) with namespaces per workspace |
| workspace id is the only credential | authentication; workspace ACLs |
| fork picks its source by name | find the closest index automatically (e.g. similarity hash of the tree) |
| SQLite, vectors stored in the clear | encryption at rest, retention policies |
