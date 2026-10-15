"""mindex: a learning PoC of Merkle-tree-synced, privacy-preserving code indexing.

Modules, in the order data flows through them:

    merkle   - client: hash the workspace into a Merkle tree, diff it against the server
    crypto   - client: deterministic per-segment path encryption (key never leaves client)
    chunker  - server: split an uploaded file into line-window chunks
    embed    - server: turn chunks / queries into vectors
    store    - server: SQLite persistence (tree, chunk pointers, embedding cache)
    server   - server: FastAPI app exposing the sync + search protocol
    client   - client: the sync / search / fork workflows
    cli      - command line entry point (`python -m mindex ...`)
"""
