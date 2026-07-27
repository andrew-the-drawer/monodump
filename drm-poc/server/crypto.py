"""Crypto primitives for the Phase 3 license protocol. See docs/01-protocol.md
for the wire-level spec this implements.

Everything here is P-256 (ECDSA for signing/identity, ECDH for session key
exchange) so that Phase 6 can swap the *device* side for a Secure Enclave key
without touching the protocol shape — the SEP only speaks P-256.
"""
from __future__ import annotations

import base64
import hashlib
import hmac
import json
import os
import time
from pathlib import Path

from cryptography.hazmat.primitives import hashes, serialization
from cryptography.hazmat.primitives.asymmetric import ec, utils as asym_utils
from cryptography.hazmat.primitives.ciphers.aead import AESGCM
from cryptography.hazmat.primitives.kdf.hkdf import HKDF

SERVER_DIR = Path(__file__).resolve().parent
ROOT_CA_KEY_PATH = SERVER_DIR / "root_ca_key.pem"
MASTER_KEY_PATH = SERVER_DIR / "master_key.bin"

HKDF_INFO = b"drm-poc-license-v1"
MASTER_TOKEN_TTL_SECONDS = 7 * 24 * 3600  # a provisioned device stays valid a week

# Phase 3-5 stand-in for real TEE attestation (see docs/01-protocol.md,
# "Provisioning"). NOT a security boundary — a hardcoded string anyone
# reading this file can pass. Phase 6 replaces this whole check with real
# Secure Enclave attestation verification.
SIMULATED_ATTESTATION_SECRET = "dev-only-simulated-tee-attestation-v1"


def b64url_encode(b: bytes) -> str:
    return base64.urlsafe_b64encode(b).rstrip(b"=").decode("ascii")


def b64url_decode(s: str) -> bytes:
    return base64.urlsafe_b64decode(s + "=" * (-len(s) % 4))


# --- root CA (signs device certificates at provisioning time) ---------------

def _load_or_create_root_ca() -> ec.EllipticCurvePrivateKey:
    if ROOT_CA_KEY_PATH.exists():
        return serialization.load_pem_private_key(ROOT_CA_KEY_PATH.read_bytes(), password=None)
    key = ec.generate_private_key(ec.SECP256R1())
    ROOT_CA_KEY_PATH.write_bytes(
        key.private_bytes(
            serialization.Encoding.PEM,
            serialization.PrivateFormat.PKCS8,
            serialization.NoEncryption(),
        )
    )
    ROOT_CA_KEY_PATH.chmod(0o600)
    return key


def _load_or_create_master_key() -> bytes:
    if MASTER_KEY_PATH.exists():
        return MASTER_KEY_PATH.read_bytes()
    key = AESGCM.generate_key(bit_length=256)
    MASTER_KEY_PATH.write_bytes(key)
    MASTER_KEY_PATH.chmod(0o600)
    return key


_ROOT_CA_KEY = None
_MASTER_KEY = None


def root_ca_key() -> ec.EllipticCurvePrivateKey:
    global _ROOT_CA_KEY
    if _ROOT_CA_KEY is None:
        _ROOT_CA_KEY = _load_or_create_root_ca()
    return _ROOT_CA_KEY


def master_key() -> bytes:
    global _MASTER_KEY
    if _MASTER_KEY is None:
        _MASTER_KEY = _load_or_create_master_key()
    return _MASTER_KEY


def sign_der(private_key: ec.EllipticCurvePrivateKey, payload: bytes) -> bytes:
    return private_key.sign(payload, ec.ECDSA(hashes.SHA256()))


def issue_device_cert(device_id: str, identity_pubkey_jwk: dict, security_level: str) -> dict:
    cert_body = {
        "device_id": device_id,
        "identity_pubkey_jwk": identity_pubkey_jwk,
        "security_level": security_level,
        "issued_at": time.time(),
    }
    payload = json.dumps(cert_body, sort_keys=True, separators=(",", ":")).encode()
    signature = sign_der(root_ca_key(), payload)
    return {"body": cert_body, "signature": b64url_encode(signature)}


# --- master token (opaque, replayed on /license instead of the cert chain) --

def issue_master_token(device_id: str) -> str:
    now = time.time()
    plaintext = json.dumps(
        {"device_id": device_id, "issued_at": now, "expiry": now + MASTER_TOKEN_TTL_SECONDS}
    ).encode()
    iv = os.urandom(12)
    ct = AESGCM(master_key()).encrypt(iv, plaintext, None)
    return b64url_encode(iv + ct)


class TokenError(Exception):
    pass


def decode_master_token(token: str) -> dict:
    try:
        raw = b64url_decode(token)
        iv, ct = raw[:12], raw[12:]
        plaintext = AESGCM(master_key()).decrypt(iv, ct, None)
        claims = json.loads(plaintext)
    except Exception as e:  # noqa: BLE001 - any malformed input is just a bad token
        raise TokenError(f"malformed master token: {e}") from e
    if time.time() > claims["expiry"]:
        raise TokenError("master token expired")
    return claims


# --- JWK <-> cryptography key objects -----------------------------------------

def jwk_to_ec_public_key(jwk: dict) -> ec.EllipticCurvePublicKey:
    x = int.from_bytes(b64url_decode(jwk["x"]), "big")
    y = int.from_bytes(b64url_decode(jwk["y"]), "big")
    return ec.EllipticCurvePublicNumbers(x, y, ec.SECP256R1()).public_key()


def ec_public_key_to_jwk(pub: ec.EllipticCurvePublicKey) -> dict:
    numbers = pub.public_numbers()
    size = (pub.curve.key_size + 7) // 8
    return {
        "kty": "EC",
        "crv": "P-256",
        "x": b64url_encode(numbers.x.to_bytes(size, "big")),
        "y": b64url_encode(numbers.y.to_bytes(size, "big")),
    }


def raw_ecdsa_sig_to_der(raw_sig: bytes) -> bytes:
    """WebCrypto ECDSA signatures are raw r||s (P1363); `cryptography` wants DER."""
    half = len(raw_sig) // 2
    r = int.from_bytes(raw_sig[:half], "big")
    s = int.from_bytes(raw_sig[half:], "big")
    return asym_utils.encode_dss_signature(r, s)


def verify_signature(pubkey_jwk: dict, payload: bytes, raw_signature_b64url: str) -> bool:
    pub = jwk_to_ec_public_key(pubkey_jwk)
    der_sig = raw_ecdsa_sig_to_der(b64url_decode(raw_signature_b64url))
    try:
        pub.verify(der_sig, payload, ec.ECDSA(hashes.SHA256()))
        return True
    except Exception:  # noqa: BLE001 - any verification failure is just "no"
        return False


# --- session key exchange (ECDH + HKDF) --------------------------------------

def generate_ephemeral_keypair():
    priv = ec.generate_private_key(ec.SECP256R1())
    return priv, priv.public_key()


def derive_session_keys(private_key: ec.EllipticCurvePrivateKey, peer_pubkey_jwk: dict, nonce: bytes):
    peer_pub = jwk_to_ec_public_key(peer_pubkey_jwk)
    shared_secret = private_key.exchange(ec.ECDH(), peer_pub)
    okm = HKDF(algorithm=hashes.SHA256(), length=64, salt=nonce, info=HKDF_INFO).derive(shared_secret)
    return okm[:32], okm[32:]  # (session_enc_key, session_mac_key)


def aead_encrypt(key: bytes, plaintext: bytes) -> tuple[bytes, bytes]:
    iv = os.urandom(12)
    ct = AESGCM(key).encrypt(iv, plaintext, None)
    return iv, ct


def aead_decrypt(key: bytes, iv: bytes, ciphertext: bytes) -> bytes:
    return AESGCM(key).decrypt(iv, ciphertext, None)


def mac_bytes(mac_key: bytes, data: bytes) -> bytes:
    return hmac.new(mac_key, data, hashlib.sha256).digest()


def build_mac_input(server_ephemeral_pubkey_jwk: dict, iv: bytes, ciphertext: bytes) -> bytes:
    """Canonical bytes covered by the response MAC. A plain field
    concatenation (not JSON) so it's reproduced byte-for-byte by
    cdm-bridge.js's WebCrypto implementation without relying on
    cross-language JSON serialization matching (Python's json.dumps and JS's
    JSON.stringify do not agree on separator whitespace)."""
    eph_part = f"{server_ephemeral_pubkey_jwk['x']}.{server_ephemeral_pubkey_jwk['y']}".encode()
    return eph_part + iv + ciphertext


def build_signing_payload(content_id: str, kids: list[str], nonce_b64url: str, ephemeral_pubkey_jwk: dict) -> bytes:
    """Canonical byte string signed by the client over a /license request.
    Must be built identically in cdm-bridge.js. See docs/01-protocol.md.
    """
    kids_part = ",".join(sorted(k.lower() for k in kids))
    eph_part = f"{ephemeral_pubkey_jwk['x']}.{ephemeral_pubkey_jwk['y']}"
    return f"{content_id}|{kids_part}|{nonce_b64url}|{eph_part}".encode()
