"""Phase 3 request handlers for /provision and /license. See
docs/01-protocol.md for the wire spec; server/crypto.py for the primitives;
server/policy.py for Phase 4/5 enforcement.
"""
from __future__ import annotations

import json
import uuid

import attestation as attestation_mod
import crypto
import models
import policy


class ProtocolError(Exception):
    def __init__(self, status_code: int, reason: str):
        self.status_code = status_code
        self.reason = reason
        super().__init__(reason)


def handle_provision(identity_pubkey_jwk: dict, requested_security_level: str, attestation: str | None) -> dict:
    requested = requested_security_level.upper()
    if requested not in ("SW", "TEE"):
        raise ProtocolError(400, "invalid_security_level")

    # The server decides what it believes, not the client. Two paths grant
    # TEE, both explicitly labeled in the response:
    #  - "real_sep_pop": a Phase 6a `cdm/tee/macos_sep` proof-of-possession
    #    claim (see server/attestation.py for exactly what this does and
    #    does not prove — it is not remote attestation).
    #  - "simulated": the pre-Phase-6 hardcoded shared secret, kept for the
    #    Phase 2-5 in-browser demo (docs/01-protocol.md).
    granted_level = "SW"
    attestation_kind = "none"
    if requested == "TEE" and attestation:
        if attestation_mod.looks_like_pop_claim(attestation):
            ok, reason = attestation_mod.verify_pop_claim(attestation, identity_pubkey_jwk)
            if ok:
                granted_level = "TEE"
                attestation_kind = "real_sep_pop"
            else:
                attestation_kind = f"real_sep_pop_rejected:{reason}"
        elif attestation == crypto.SIMULATED_ATTESTATION_SECRET:
            granted_level = "TEE"
            attestation_kind = "simulated"

    device_id = uuid.uuid4().hex
    models.create_device(device_id, json.dumps(identity_pubkey_jwk), granted_level)
    cert = crypto.issue_device_cert(device_id, identity_pubkey_jwk, granted_level)
    master_token = crypto.issue_master_token(device_id)
    return {
        "device_id": device_id,
        "security_level": granted_level,
        "attestation_kind": attestation_kind,
        "device_cert": cert,
        "master_token": master_token,
    }


def handle_license(
    master_token: str,
    content_id: str,
    kids: list[str],
    nonce: str,
    ephemeral_pubkey_jwk: dict,
    signature: str,
    session_id: str | None,
) -> dict:
    try:
        claims = crypto.decode_master_token(master_token)
    except crypto.TokenError as e:
        raise ProtocolError(401, f"bad_master_token: {e}") from e

    device_row = models.get_device(claims["device_id"])
    if device_row is None:
        raise ProtocolError(404, "unknown_device")

    identity_pubkey_jwk = json.loads(device_row["pubkey_jwk"])
    payload = crypto.build_signing_payload(content_id, kids, nonce, ephemeral_pubkey_jwk)
    if not crypto.verify_signature(identity_pubkey_jwk, payload, signature):
        raise ProtocolError(401, "bad_signature")

    try:
        granted_session_id, expires_at, is_renewal = policy.evaluate_session(
            device_row, content_id, session_id
        )
    except policy.PolicyError as e:
        raise ProtocolError(403, e.reason) from e

    allowed_rows = policy.select_allowed_keys(device_row["security_level"], kids, content_id)

    server_priv, server_pub = crypto.generate_ephemeral_keypair()
    nonce_bytes = crypto.b64url_decode(nonce)
    session_enc_key, session_mac_key = crypto.derive_session_keys(
        server_priv, ephemeral_pubkey_jwk, nonce_bytes
    )

    response_payload = {
        "keys": {r["kid"]: r["key"] for r in allowed_rows},
        "policy": {
            "security_level": device_row["security_level"],
            "expires_at": expires_at,
            "is_renewal": is_renewal,
        },
        "session_id": granted_session_id,
    }
    iv, ciphertext = crypto.aead_encrypt(
        session_enc_key, json.dumps(response_payload).encode()
    )
    server_pubkey_jwk = crypto.ec_public_key_to_jwk(server_pub)
    mac_input = crypto.build_mac_input(server_pubkey_jwk, iv, ciphertext)
    mac = crypto.mac_bytes(session_mac_key, mac_input)

    return {
        "server_ephemeral_pubkey_jwk": server_pubkey_jwk,
        "iv": crypto.b64url_encode(iv),
        "ciphertext": crypto.b64url_encode(ciphertext),
        "mac": crypto.b64url_encode(mac),
    }
