"""Phase 6a: verifies a macOS Secure Enclave "proof-of-possession" claim from
`cdm/tee/macos_sep`.

**This is not remote attestation.** During Phase 6a implementation we went
looking for a supported way to get a real Apple-rooted attestation of a
Secure Enclave key from a plain command-line tool, the way
`docs/01-protocol.md` originally described it. What we found: the private
`SecKeyCreateAttestation` symbol exists in the Security.framework dylib but
has no public header on macOS across SDKs 11 through 26 (only consumed
indirectly by other Apple frameworks), and Apple's own public App Attest API
(`DCAppAttestService`) is documented to report `.supported == false` on
every Mac target, Apple silicon included. There is no supported path to a
third-party-verifiable device attestation from a macOS CLI. See
`docs/02-tee.md` for the full account — this is exactly the kind of gap
real DRM vendors solve with a manufacturer-provisioned root key that never
leaves silicon and that *they* control the verification chain for; we have
neither.

What we verify instead is weaker but real: a **fresh signature**, made by
the presented identity public key's corresponding Secure Enclave private
key, over a timestamped claim. This proves whoever is calling `/provision`
right now genuinely holds that private key (proof-of-possession) — a
compromised or fake `sep-helper` binary could still self-sign the same
claim using an ordinary software key, so this does NOT prove the key
actually lives in a genuine SEP. That property (non-extractability) is real
for the *actual* `cdm/tee/macos_sep` binary, but it isn't something the
wire protocol can force a claimant to prove; it's demonstrated locally by
`prove_nonextractable.sh` instead, not by anything this module checks.
"""
from __future__ import annotations

import json
import time

import crypto

POP_CLAIM_KIND = "macos_sep_v1"
POP_MAX_SKEW_SECONDS = 60  # how stale/future-dated a claim's timestamp may be


def looks_like_pop_claim(attestation: str) -> bool:
    """Cheap shape check so callers can route to this verifier instead of
    the legacy `SIMULATED_ATTESTATION_SECRET` string compare — a
    proof-of-possession claim is `<b64url payload>.<b64url signature>`,
    which the legacy shared secret never contains."""
    return attestation.count(".") == 1 and not attestation.startswith("dev-only-")


def verify_pop_claim(attestation: str, identity_pubkey_jwk: dict) -> tuple[bool, str]:
    """Returns (ok, reason). `reason` is always present for logging/demo
    output, even on success (e.g. "ok")."""
    try:
        payload_b64, signature_b64 = attestation.split(".", 1)
    except ValueError:
        return False, "malformed_claim_shape"

    try:
        payload_bytes = crypto.b64url_decode(payload_b64)
        claim = json.loads(payload_bytes)
    except Exception:  # noqa: BLE001 - any malformed input is just "no"
        return False, "malformed_claim_payload"

    if claim.get("claim") != POP_CLAIM_KIND:
        return False, "unknown_claim_kind"

    timestamp = claim.get("timestamp")
    if not isinstance(timestamp, (int, float)):
        return False, "missing_timestamp"
    if abs(time.time() - timestamp) > POP_MAX_SKEW_SECONDS:
        return False, "claim_timestamp_stale"

    if not crypto.verify_signature(identity_pubkey_jwk, payload_bytes, signature_b64):
        return False, "bad_signature"

    return True, "ok"
