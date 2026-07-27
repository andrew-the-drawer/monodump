#!/usr/bin/env python3
"""A Python stand-in for the browser's WebCrypto-based device, used to:

  - integration-test the server side of the Phase 3 protocol without needing
    a browser, and
  - drive the Phase 4 policy demonstrations deterministically (expiry,
    rental window, device binding, revocation, concurrency) — these are much
    easier to prove with a scriptable client than by clicking through Chrome
    repeatedly.

This mirrors exactly what player/cdm-bridge.js does with SubtleCrypto; see
docs/01-protocol.md for the wire format both implementations share.
"""
from __future__ import annotations

import base64
import json
import os
import sys

import requests
from cryptography.hazmat.primitives import hashes, serialization
from cryptography.hazmat.primitives.asymmetric import ec, utils as asym_utils
from cryptography.hazmat.primitives.ciphers.aead import AESGCM
from cryptography.hazmat.primitives.kdf.hkdf import HKDF

sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "server"))
import crypto as server_crypto  # noqa: E402  (reuse the exact same helpers; see note below)

BASE_URL = os.environ.get("DRMPOC_BASE_URL", "http://127.0.0.1:8000")


def b64url_encode(b: bytes) -> str:
    return base64.urlsafe_b64encode(b).rstrip(b"=").decode("ascii")


def b64url_decode(s: str) -> bytes:
    return base64.urlsafe_b64decode(s + "=" * (-len(s) % 4))


def pubkey_to_jwk(pub: ec.EllipticCurvePublicKey) -> dict:
    numbers = pub.public_numbers()
    return {
        "kty": "EC",
        "crv": "P-256",
        "x": b64url_encode(numbers.x.to_bytes(32, "big")),
        "y": b64url_encode(numbers.y.to_bytes(32, "big")),
    }


def jwk_to_pubkey(jwk: dict) -> ec.EllipticCurvePublicKey:
    x = int.from_bytes(b64url_decode(jwk["x"]), "big")
    y = int.from_bytes(b64url_decode(jwk["y"]), "big")
    return ec.EllipticCurvePublicNumbers(x, y, ec.SECP256R1()).public_key()


def sign_raw(private_key: ec.EllipticCurvePrivateKey, payload: bytes) -> bytes:
    """DER (what `cryptography` produces) -> raw r||s (what WebCrypto produces)."""
    der_sig = private_key.sign(payload, ec.ECDSA(hashes.SHA256()))
    r, s = asym_utils.decode_dss_signature(der_sig)
    return r.to_bytes(32, "big") + s.to_bytes(32, "big")


class Device:
    """One simulated device: a fresh identity keypair each time it's
    constructed, exactly like a fresh browser profile with no prior
    provisioning state.
    """

    def __init__(self):
        self.identity_priv = ec.generate_private_key(ec.SECP256R1())
        self.identity_pub_jwk = pubkey_to_jwk(self.identity_priv.public_key())
        self.device_id = None
        self.master_token = None
        self.security_level = None

    def provision(self, requested_level: str = "SW", attestation: str | None = None) -> dict:
        resp = requests.post(
            f"{BASE_URL}/provision",
            json={
                "identity_pubkey_jwk": self.identity_pub_jwk,
                "requested_security_level": requested_level,
                "attestation": attestation,
            },
        )
        resp.raise_for_status()
        data = resp.json()
        self.device_id = data["device_id"]
        self.master_token = data["master_token"]
        self.security_level = data["security_level"]
        return data

    def request_license(
        self,
        content_id: str,
        kids: list[str],
        session_id: str | None = None,
        tamper: dict | None = None,
    ) -> requests.Response:
        """`tamper` optionally overrides any request field post-signing, to
        prove the server rejects modified requests (Phase 3 done-when)."""
        nonce = b64url_encode(os.urandom(16))
        ephemeral_priv = ec.generate_private_key(ec.SECP256R1())
        ephemeral_pub_jwk = pubkey_to_jwk(ephemeral_priv.public_key())

        payload = server_crypto.build_signing_payload(content_id, kids, nonce, ephemeral_pub_jwk)
        signature = b64url_encode(sign_raw(self.identity_priv, payload))

        body = {
            "master_token": self.master_token,
            "content_id": content_id,
            "kids": kids,
            "nonce": nonce,
            "ephemeral_pubkey_jwk": ephemeral_pub_jwk,
            "signature": signature,
            "session_id": session_id,
        }
        if tamper:
            body.update(tamper)

        resp = requests.post(f"{BASE_URL}/license", json=body)
        if resp.status_code != 200:
            return resp

        data = resp.json()
        shared_secret = ephemeral_priv.exchange(ec.ECDH(), jwk_to_pubkey(data["server_ephemeral_pubkey_jwk"]))
        okm = HKDF(
            algorithm=hashes.SHA256(), length=64, salt=b64url_decode(nonce), info=server_crypto.HKDF_INFO
        ).derive(shared_secret)
        session_enc_key, session_mac_key = okm[:32], okm[32:]

        iv = b64url_decode(data["iv"])
        ciphertext = b64url_decode(data["ciphertext"])
        mac_input = server_crypto.build_mac_input(data["server_ephemeral_pubkey_jwk"], iv, ciphertext)
        expected_mac = server_crypto.mac_bytes(session_mac_key, mac_input)
        if not _consteq(expected_mac, b64url_decode(data["mac"])):
            resp._mac_ok = False  # type: ignore[attr-defined]
            return resp
        resp._mac_ok = True  # type: ignore[attr-defined]

        plaintext = AESGCM(session_enc_key).decrypt(iv, ciphertext, None)
        resp._decrypted = json.loads(plaintext)  # type: ignore[attr-defined]
        return resp


def _consteq(a: bytes, b: bytes) -> bool:
    import hmac as _hmac

    return _hmac.compare_digest(a, b)


if __name__ == "__main__":
    d = Device()
    print("provisioned:", d.provision(requested_level="SW"))
    print("(run tools/demo_policies.py for the full Phase 4/5 walkthrough)")
