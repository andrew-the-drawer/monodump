#!/usr/bin/env bash
# End-to-end walkthrough against a real repo. Each step maps to a section of README.md.
#
#   ./scripts/demo.sh            # MiniLM embeddings (downloads ~90MB once)
#   EMBEDDER=hash ./scripts/demo.sh   # no model, keyword-level search
set -euo pipefail

POC="$(cd "$(dirname "$0")/.." && pwd)"
PY="$POC/../venv/bin/python"
DEMO="$POC/.demo"
PORT="${PORT:-8765}"
EMBEDDER="${EMBEDDER:-minilm}"
REPO_URL="${REPO_URL:-https://github.com/psf/requests.git}"
mindex() { (cd "$POC" && "$PY" -m mindex "$@"); }
step() { printf '\n\033[1;36m== %s\033[0m\n' "$*"; }

rm -rf "$DEMO" && mkdir -p "$DEMO"
git clone --quiet --depth 1 "$REPO_URL" "$DEMO/alice"
cp -R "$DEMO/alice" "$DEMO/bob"

step "Start server (embedder=$EMBEDDER, db=$DEMO/server/index.db)"
(cd "$POC" && MINDEX_EMBEDDER="$EMBEDDER" MINDEX_DB="$DEMO/server/index.db" \
  "$PY" -m uvicorn mindex.server:app --port "$PORT" --log-level warning) &
SERVER_PID=$!
trap 'kill $SERVER_PID 2>/dev/null' EXIT
until curl -s "http://127.0.0.1:$PORT/docs" >/dev/null; do sleep 0.5; done

step "1. The local Merkle tree (top level)"
mindex init "$DEMO/alice" --workspace alice --server "http://127.0.0.1:$PORT"
mindex tree "$DEMO/alice" --depth 1

step "2. First sync: everything is new, so everything is uploaded"
mindex sync "$DEMO/alice"

step "3. Sync again with no changes: one root-hash comparison, nothing uploaded"
mindex sync "$DEMO/alice"

step "4. Edit one deep file: descend only along the changed path"
echo "# touched by demo" >> "$DEMO/alice/src/requests/adapters.py"
mindex sync "$DEMO/alice"

step "5. Search: server returns encrypted pointers, client reads lines locally"
mindex search "$DEMO/alice" "retry failed connections with backoff" -k 2 --show-encrypted

step "6. The server DB has no code and no file names"
for needle in HTTPAdapter adapters.py "def send"; do
  hits=$(sqlite3 "$DEMO/server/index.db" .dump | grep -c "$needle" || true)
  echo "occurrences of '$needle' in server DB dump: $hits"
done

step "7. Team reuse: bob forks alice's index (shared key), then sends hashes only"
mindex init "$DEMO/bob" --workspace bob --server "http://127.0.0.1:$PORT" --key-from "$DEMO/alice/.mindex/key"
mindex fork "$DEMO/bob" --source alice >/dev/null
echo "# bob's local change" >> "$DEMO/bob/src/requests/sessions.py"
mindex sync "$DEMO/bob" --tree-only
mindex stats "$DEMO/bob"

step "8. Proof of possession: alice's adapters.py differs from bob's, so it is hidden from bob"
echo "(expect no src/requests/adapters.py hits; alice's copy is indexed, bob's isn't yet)"
mindex search "$DEMO/bob" "HTTPAdapter send request through connection pool" -k 3 | grep '^──'

step "9. Bob's full sync uploads only his 2 differing files; the cache absorbs the rest"
mindex sync "$DEMO/bob"
mindex search "$DEMO/bob" "HTTPAdapter send request through connection pool" -k 3 | grep '^──'
