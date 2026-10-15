# 01 · Concepts

## The problem

Semantic code search ("where do we retry failed uploads?") needs embeddings of the codebase. Computing embeddings for a large repo is expensive, so it's done on a server. Two constraints pull against each other:

1. **Freshness.** Developers edit constantly. Re-uploading a 2 GB monorepo every few minutes isn't viable.
2. **Privacy.** Many customers (and Cursor's privacy mode) require that their source code not be stored on the vendor's servers.

Cursor's design, which this PoC reproduces, answers (1) with a Merkle tree and (2) with "embed, keep pointers, drop the text".

## Merkle trees in one picture

```
                         root = H(tree: dir docs H1, dir src H2, file README H3)
                        /                     |                        \
            docs  H1 = H(tree: …)     src  H2 = H(tree: …)        README.md  H3 = H(blob: bytes)
                                         /          \
                                 api.py H4        util.py H5
```

- A **file** is hashed by its bytes: `H("blob\0" + bytes)`.
- A **directory** is hashed over its children's `(kind, name, hash)`, sorted by name.

Two properties follow:

- **Change propagates upward only.** Editing `util.py` changes H5, then H2, then the root. H1, H3 and H4 stay the same.
- **Equal hash ⇒ equal subtree.** If the server's H1 matches the client's H1, everything under `docs/` is identical. There's no need to look inside.

This is the same structure git uses for its tree objects, and the same idea behind rsync-style and Dynamo/Cassandra anti-entropy repair.

## Sync = walking down mismatches

```
client: root?            server: root = R'      R ≠ R'  → ask for root's children
client: docs H1 ✓  src H2≠H2'  README H3 ✓      → descend into src only
client: api.py H4 ✓  util.py H5≠H5'             → util.py changed. Done.
```

- Cost when nothing changed: **1 comparison**.
- Cost when k files changed: about **k × depth comparisons**, plus the siblings seen along the way.
- Round trips: the **depth of the deepest change**. The PoC batches each level into one request.

In the `requests` demo, editing one file 3 levels deep cost 3 round trips and 43 hash comparisons, out of 146 tree nodes. On a 100k-file monorepo, the gap between 43 and 100k is the whole point.

### The trap the tests caught

The tree on the server records *what the client claims to have*. It does not record *what has been indexed*. If those are the same table, a sync that writes the hashes and then crashes before uploading content leaves the server believing it is up to date. The next Merkle diff is clean, so the file is never indexed.

The PoC keeps a separate `ingested(path, file_hash)` table and a `/pending` endpoint. After the hash phase, the client uploads whatever is pending. This makes sync self-healing and also makes `--tree-only` safe. Lesson: **Merkle trees tell you what differs; they don't track the progress of the work that follows.**

## What the server stores, and what it doesn't

| stored | not stored |
|---|---|
| Merkle hashes of files and dirs | file contents |
| encrypted path of each node | plaintext paths |
| per chunk: encrypted path, line range, file hash, chunk hash | chunk text |
| embedding vectors, keyed by chunk hash | |

When a search runs, the server returns `(encrypted path, lines 31-60)`. The **client** decrypts the path with its key and reads those lines from its own disk. The snippet then goes to the LLM as context for that request.

### Path encryption (AES-SIV, per segment)

`src/requests/adapters.py` becomes `ExRLXfl…/akc_C7tb…/ekiy6EVE…`.

- **Deterministic**: the same path encrypts the same way on every sync, so the server can key on it.
- **Per segment**: prefixes are preserved, so the server can still represent the tree and delete whole directories.
- **The key never leaves the client** (`<workspace>/.mindex/key`).
- **What still leaks**: segment equality (every `__init__.py` gets the same ciphertext under the same key), path depth, and approximate name lengths.

## Embedding cache and team reuse

Embeddings are cached by **chunk content hash**, globally. Your clone of a repo and a teammate's clone share almost every chunk, and vendored libraries are shared across companies. Only new chunks cost an embedding call. In the demo, editing one file re-embedded **1 of 30** chunks.

Going further: a new teammate's index is **forked** from an existing one. That means copying the tree, chunk pointers and ingest records. Then the normal Merkle sync uploads only the files where they differ. In the demo, bob uploaded 2 files out of 122.

### Proof of possession

Forking creates a hazard. Alice's index contains her **uncommitted changes**. Bob must never see search results from code he doesn't have.

The rule: a chunk is only returned if its `file_hash` equals the hash in **the requester's own tree** for that path. Bob's tree comes from his own Merkle sync. To get alice's version of `adapters.py` returned, bob would need its hash, which means having its content. The demo's step 8 shows alice's version being filtered out of bob's results.

Caveat: knowing a hash isn't strictly the same as having the file. If alice's file hash leaked some other way, bob could claim it. For this threat model, a strong content hash is a reasonable proxy.

## Where the privacy story ends

**"We don't store your code" is not the same as "your code can't be recovered from what we store."**

1. **Embeddings leak content.** Inversion attacks reconstruct text from vectors. Short chunks are recovered best; secrets and distinctive identifiers leak first. See [03-inversion.md](03-inversion.md) for the attack run against this PoC's own database.
2. **Hashes are dictionary-attackable.** The hash of a well-known file (an MIT `LICENSE`, a popular library file) reveals that you have it. The same goes for a short, guessable chunk.
3. **The plaintext still passes through the server** during ingest, and at query time the retrieved snippets go to the LLM. "Not stored" describes data at rest, not data in transit.
4. **Metadata**: file count, tree shape, how often you edit, and segment equality (above).

Production mitigations: encrypt vectors at rest with strict access control, keep the embedding model private (this raises the attack cost; it doesn't prevent the attack), add noise to embeddings, and scan for secrets before indexing.
