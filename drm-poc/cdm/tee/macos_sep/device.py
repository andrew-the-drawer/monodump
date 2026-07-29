#!/usr/bin/env python3
"""Phase 6a: a standalone "device" whose private-key operations are backed
by the real Secure Enclave on this Mac, via `sep-helper` (built from
`Sources/sep-helper/main.swift`), instead of in-process `cryptography` keys
(`tools/protocol_client.py`) or in-browser WebCrypto (`player/cdm-bridge.js`).

Per PLAN.md Part 5, a custom CDM can't plug into a real browser's EME, so
this path is inherently a standalone driver rather than a `cdm-bridge.js`
mode — it talks to the same running server, over the same wire protocol
(docs/01-protocol.md), with every identity-key and ephemeral-ECDH operation
shelled out to the Secure Enclave instead of done in Python. What still
lands in this process's own heap: the derived session key and the content
key, after `sep-helper` hands back the raw ECDH shared secret — see
docs/02-tee.md for why that's an honest, expected boundary for this track
(the L2-vs-L1 distinction), not an oversight.

Usage:
    cd server && uvicorn main:app --port 8000        # one terminal
    python3 cdm/tee/macos_sep/device.py                # another
"""
from __future__ import annotations

import base64
import json
import os
import re
import subprocess
import sys
import time

import requests
from cryptography.hazmat.primitives import hashes
from cryptography.hazmat.primitives.ciphers.aead import AESGCM
from cryptography.hazmat.primitives.kdf.hkdf import HKDF

SERVER_DIR = os.path.join(os.path.dirname(__file__), "..", "..", "..", "server")
sys.path.insert(0, os.path.abspath(SERVER_DIR))
import crypto as server_crypto  # noqa: E402 -- reuse the exact same wire-format helpers

HERE = os.path.dirname(os.path.abspath(__file__))
SEP_HELPER = os.path.join(HERE, ".build", "release", "sep-helper")
BASE_URL = os.environ.get("DRMPOC_BASE_URL", "http://127.0.0.1:8000")
CONTENT_ID = "demo"


def b64url_encode(b: bytes) -> str:
    return base64.urlsafe_b64encode(b).rstrip(b"=").decode("ascii")


def b64url_decode(s: str) -> bytes:
    return base64.urlsafe_b64decode(s + "=" * (-len(s) % 4))


def _check_helper_built() -> None:
    if not os.path.exists(SEP_HELPER):
        raise RuntimeError(
            f"{SEP_HELPER} not found. Build it first:\n"
            f"  cd {HERE} && swift build -c release"
        )


def _run_helper(*args: str) -> dict:
    _check_helper_built()
    proc = subprocess.run([SEP_HELPER, *args], capture_output=True, text=True)
    if proc.returncode != 0:
        raise RuntimeError(f"sep-helper {' '.join(args)} failed: {proc.stderr.strip()}")
    return json.loads(proc.stdout)


def discover_kids(manifest_url: str) -> list[str]:
    text = requests.get(manifest_url).text
    kids = set()
    for m in re.finditer(r'cenc:default_KID="([0-9a-fA-F-]+)"', text):
        kids.add(m.group(1).replace("-", "").lower())
    return sorted(kids)


class SEPDevice:
    """One Secure-Enclave-backed device identity, keyed by `label` so
    repeat runs reuse the same SE identity key (delete it with
    `sep-helper delete-identity <label>` to provision fresh)."""

    def __init__(self, label: str = "demo-device"):
        self.label = label
        self.device_id: str | None = None
        self.master_token: str | None = None
        self.security_level: str | None = None

    def _identity_pubkey_jwk(self) -> dict:
        return _run_helper("identity", self.label)["pubkey_jwk"]

    def _build_pop_claim(self) -> str:
        """Phase 6a's real `/provision` attestation path -- see
        server/attestation.py for exactly what this proves (a fresh
        signature only this Secure Enclave key could have produced) and
        what it doesn't (remote attestation of the key's hardware origin;
        see docs/02-tee.md)."""
        payload = json.dumps(
            {"claim": "macos_sep_v1", "timestamp": time.time()}, sort_keys=True, separators=(",", ":")
        ).encode()
        payload_b64 = b64url_encode(payload)
        signature_b64 = _run_helper("sign", self.label, payload_b64)["signature_b64"]
        return f"{payload_b64}.{signature_b64}"

    def provision(self, requested_level: str = "TEE") -> dict:
        identity_pubkey_jwk = self._identity_pubkey_jwk()
        attestation = self._build_pop_claim() if requested_level == "TEE" else None
        resp = requests.post(
            f"{BASE_URL}/provision",
            json={
                "identity_pubkey_jwk": identity_pubkey_jwk,
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

    def _ecdh_via_sep(self, server_ephemeral_pubkey_jwk: dict | None):
        """Two-phase exchange against `sep-helper ecdh-session` (see
        main.swift): the client's ephemeral public key has to be produced
        *before* the server's is known (it goes in the signed /license
        request), so this returns a (get_own_pubkey, complete) pair rather
        than a single call. The subprocess -- and the ephemeral SE key it
        holds -- lives only across this one exchange."""
        _check_helper_built()
        proc = subprocess.Popen(
            [SEP_HELPER, "ecdh-session"],
            stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
        )
        line1 = proc.stdout.readline()
        if not line1:
            raise RuntimeError(f"sep-helper ecdh-session failed to start: {proc.stderr.read()}")
        ephemeral_pubkey_jwk = json.loads(line1)["ephemeral_pubkey_jwk"]

        def complete(peer_pubkey_jwk: dict) -> bytes:
            proc.stdin.write(json.dumps({"peer_x": peer_pubkey_jwk["x"], "peer_y": peer_pubkey_jwk["y"]}) + "\n")
            proc.stdin.flush()
            line2 = proc.stdout.readline()
            proc.wait(timeout=5)
            if not line2:
                raise RuntimeError(f"sep-helper ecdh-session failed to complete: {proc.stderr.read()}")
            return b64url_decode(json.loads(line2)["shared_secret_b64"])

        return ephemeral_pubkey_jwk, complete

    def request_license(self, content_id: str, kids: list[str], session_id: str | None = None) -> dict:
        nonce = b64url_encode(os.urandom(16))
        ephemeral_pubkey_jwk, complete_ecdh = self._ecdh_via_sep(None)

        payload = server_crypto.build_signing_payload(content_id, kids, nonce, ephemeral_pubkey_jwk)
        signature_b64 = _run_helper("sign", self.label, b64url_encode(payload))["signature_b64"]

        resp = requests.post(
            f"{BASE_URL}/license",
            json={
                "master_token": self.master_token,
                "content_id": content_id,
                "kids": kids,
                "nonce": nonce,
                "ephemeral_pubkey_jwk": ephemeral_pubkey_jwk,
                "signature": signature_b64,
                "session_id": session_id,
            },
        )
        if resp.status_code != 200:
            return {"ok": False, "status": resp.status_code, "reason": resp.json().get("detail")}

        data = resp.json()
        # The shared secret -- and everything derived from it below -- is
        # the one place this honest boundary shows up: it lands in this
        # Python process's heap, same as the content key will. Only the
        # private key that produced it never did. See the module docstring.
        shared_secret = complete_ecdh(data["server_ephemeral_pubkey_jwk"])

        okm = HKDF(
            algorithm=hashes.SHA256(), length=64, salt=b64url_decode(nonce), info=server_crypto.HKDF_INFO
        ).derive(shared_secret)
        session_enc_key, session_mac_key = okm[:32], okm[32:]

        iv = b64url_decode(data["iv"])
        ciphertext = b64url_decode(data["ciphertext"])
        mac_input = server_crypto.build_mac_input(data["server_ephemeral_pubkey_jwk"], iv, ciphertext)
        expected_mac = server_crypto.mac_bytes(session_mac_key, mac_input)
        import hmac as _hmac
        if not _hmac.compare_digest(expected_mac, b64url_decode(data["mac"])):
            return {"ok": False, "status": None, "reason": "mac_verification_failed"}

        plaintext = AESGCM(session_enc_key).decrypt(iv, ciphertext, None)
        return {"ok": True, **json.loads(plaintext)}


def main() -> None:
    device = SEPDevice(label=os.environ.get("DRMPOC_SEP_LABEL", "demo-device"))

    print("== Phase 6a: Secure Enclave-backed device ==")
    prov = device.provision(requested_level="TEE")
    print(f"provisioned device {prov['device_id']}")
    print(f"  security_level granted: {prov['security_level']}")
    print(f"  attestation_kind:       {prov['attestation_kind']}  "
          f"(see server/attestation.py -- this is proof-of-possession, not remote attestation)")

    kids = discover_kids(f"{BASE_URL}/content/dash.mpd")
    print(f"discovered {len(kids)} KIDs from manifest: {kids}")

    result = device.request_license(CONTENT_ID, kids)
    if not result["ok"]:
        print(f"LICENSE DENIED: {result['status']} {result['reason']}")
        sys.exit(1)

    print(f"license granted. session {result['session_id']}, policy {result['policy']}")
    print(f"keys received for {len(result['keys'])} of {len(kids)} requested KIDs "
          f"(gap is Phase 5 tier gating): {sorted(result['keys'].keys())}")

    keys_path = os.path.join(HERE, ".last_granted_keys.json")
    with open(keys_path, "w") as f:
        json.dump(result["keys"], f)
    print(f"wrote granted content keys to {keys_path} for decrypt_segment.py to use")


if __name__ == "__main__":
    main()
