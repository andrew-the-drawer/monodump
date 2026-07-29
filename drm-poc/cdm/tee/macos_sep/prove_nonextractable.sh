#!/usr/bin/env bash
# Phase 6a's analogue of PLAN.md's "prove it with a memory dump": we can't
# dump the Secure Enclave's internal memory (that's the entire point), so
# instead we go after the one place the key's persisted *representation*
# exists at all -- the on-disk blob `identity` writes via
# SecureEnclave.P256.Signing.PrivateKey.dataRepresentation -- and show it is
# not usable as a P-256 private key by anything other than the SEP that
# produced it. Scoped honestly: this proves the *device identity key*
# can't be extracted, not that the *content key* never touches memory (see
# decrypt_segment.py's own docstring for that boundary, and docs/02-tee.md).
set -euo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
BIN="$HERE/.build/release/sep-helper"
LABEL="${1:-demo-device}"
BLOB="$HERE/.identities/$LABEL.sepkey"

if [[ ! -x "$BIN" ]]; then
  echo "sep-helper not built. Run: (cd $HERE && swift build -c release)" >&2
  exit 1
fi

echo "== ensuring identity '$LABEL' exists =="
IDENTITY_JSON="$("$BIN" identity "$LABEL")"
echo "$IDENTITY_JSON"

if [[ ! -f "$BLOB" ]]; then
  echo "expected blob at $BLOB but it's missing" >&2
  exit 1
fi

BLOB_SIZE=$(wc -c < "$BLOB" | tr -d ' ')
echo
echo "== on-disk representation =="
echo "file: $BLOB"
echo "size: $BLOB_SIZE bytes (a real P-256 private key is exactly 32)"
echo "first 32 bytes (hex): $(xxd -p -l 32 "$BLOB" | tr -d '\n')"

echo
echo "== attempting to use the on-disk blob as the actual private key =="
python3 - "$BLOB" "$IDENTITY_JSON" <<'PYEOF'
import base64
import json
import sys

blob_path, identity_json = sys.argv[1], sys.argv[2]
real_pubkey_jwk = json.loads(identity_json)["pubkey_jwk"]

with open(blob_path, "rb") as f:
    blob = f.read()

def b64u_decode(s):
    return base64.urlsafe_b64decode(s + "=" * (-len(s) % 4))

real_x = int.from_bytes(b64u_decode(real_pubkey_jwk["x"]), "big")
real_y = int.from_bytes(b64u_decode(real_pubkey_jwk["y"]), "big")

from cryptography.hazmat.primitives.asymmetric import ec
from cryptography.hazmat.primitives import serialization

# Attempt 1: is the blob itself a recognized private-key encoding at all
# (PKCS8 DER, SEC1 DER, PEM)? If the SEP's "opaque blob" concept were a
# thin wrapper around a real exportable key, one of these would parse.
parsed_as_real_key = False
for loader, desc in [
    (lambda b: serialization.load_der_private_key(b, password=None), "DER (PKCS8/SEC1)"),
    (lambda b: serialization.load_pem_private_key(b, password=None), "PEM"),
]:
    try:
        loader(blob)
        print(f"  UNEXPECTED: blob parses as a standard private key ({desc})")
        parsed_as_real_key = True
    except Exception as e:
        print(f"  blob does NOT parse as a standard private key ({desc}): {type(e).__name__}")

# Attempt 2: brute-force every 32-byte-aligned window of the blob as a raw
# P-256 scalar, derive the corresponding public key, and check whether it
# matches the real one. A real 32-byte private key would match by
# definition; opaque wrapper bytes should never match, whether or not any
# given window happens to be a numerically valid scalar.
found_match = False
checked = 0
for offset in range(0, len(blob) - 32 + 1):
    window = blob[offset:offset + 32]
    scalar = int.from_bytes(window, "big")
    try:
        candidate_priv = ec.derive_private_key(scalar, ec.SECP256R1())
    except ValueError:
        continue  # not a valid scalar for this curve (e.g. 0, or >= curve order)
    checked += 1
    nums = candidate_priv.public_key().public_numbers()
    if nums.x == real_x and nums.y == real_y:
        found_match = True
        print(f"  UNEXPECTED: byte offset {offset} reproduces the real public key")

print(f"  checked {checked} of {len(blob) - 31} possible 32-byte windows as raw P-256 scalars")
if not found_match and not parsed_as_real_key:
    print()
    print("RESULT: no interpretation of the on-disk blob yields the real private key.")
    print("        The identity key that signed every /provision and /license request")
    print("        in this demo cannot be reconstructed from anything on this disk --")
    print("        only the Secure Enclave that generated it can use it.")
else:
    print()
    print("RESULT: FAILED -- the blob turned out to be extractable. This would be a")
    print("        real finding; do not treat 6a as demonstrated if you see this.")
    sys.exit(1)
PYEOF
