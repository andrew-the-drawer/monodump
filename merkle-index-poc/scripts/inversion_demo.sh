#!/usr/bin/env bash
# Index a small "victim" repo with GTR embeddings at two chunk sizes, then run
# the vec2text inversion attack on the stored vectors. See docs/03-inversion.md.
#
# First run downloads GTR-T5-base + the vec2text inverter/corrector (~2GB).
set -euo pipefail

POC="$(cd "$(dirname "$0")/.." && pwd)"
PY="$POC/../venv/bin/python"
DEMO="$POC/.demo-inv"
PORT="${PORT:-8766}"
N="${N:-6}"
STEPS="${STEPS:-20}"
step() { printf '\n\033[1;31m== %s\033[0m\n' "$*"; }

make_victim() {
  rm -rf "$DEMO" && mkdir -p "$DEMO/victim/app"
  cat > "$DEMO/victim/app/billing.py" <<'EOF'
# Charge the customer card and email a receipt.
STRIPE_KEY = "sk_live_51HfakeKEYforDEMOonly"
def charge_customer(customer_id, amount_cents):
    return stripe.Charge.create(customer=customer_id, amount=amount_cents)
# Refunds over 500 dollars need manager approval.
def refund(charge_id, reason):
    return stripe.Refund.create(charge=charge_id, reason=reason)
EOF
  cat > "$DEMO/victim/app/notes.md" <<'EOF'
The acquisition of Globex closes on March 3rd, do not tell the sales team.
Database password for staging is tangerine-falcon-42.
EOF
}

run_at_chunk_size() {
  local lines=$1
  step "Chunk size = $lines line(s): index with GTR, then attack the DB"
  rm -rf "$DEMO/server" "$DEMO/victim/.mindex"
  (cd "$POC" && MINDEX_EMBEDDER=gtr MINDEX_CHUNK_LINES=$lines MINDEX_CHUNK_OVERLAP=0 \
     MINDEX_DB="$DEMO/server/index.db" "$PY" -m uvicorn mindex.server:app --port "$PORT" --log-level warning) &
  local pid=$!
  until curl -s "http://127.0.0.1:$PORT/docs" >/dev/null; do sleep 0.5; done
  (cd "$POC" && "$PY" -m mindex init "$DEMO/victim" --workspace victim --server "http://127.0.0.1:$PORT" >/dev/null \
     && "$PY" -m mindex sync "$DEMO/victim" | tail -1)
  kill $pid; wait $pid 2>/dev/null || true
  "$PY" "$POC/scripts/invert_attack.py" --db "$DEMO/server/index.db" --workspace victim \
     --workspace-dir "$DEMO/victim" -n "$N" --steps "$STEPS"
}

make_victim
run_at_chunk_size 1    # what vec2text was trained on: short texts
run_at_chunk_size 30   # a realistic chunk: the whole file in one vector
