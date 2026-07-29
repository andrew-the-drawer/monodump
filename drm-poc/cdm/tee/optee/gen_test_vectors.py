#!/usr/bin/env python3
"""Phase 6b (untested scaffold): generates the offline test vectors
`host/main.c` reads, playing the "license server" role opposite the TA's
"device" role -- the mirror image of Phase 6a, where device.py plays the
device against the real server. There is no live server involved here;
this is a standalone crypto demo of the ECDH-derive -> unwrap -> AES-CTR
pipeline the TA implements (see ta/drm_poc_ta.c's file header for the
session-key derivation this must match exactly: HMAC-SHA256, not the real
protocol's HKDF).

Two-step workflow (see README.md):
  1. Boot QEMU, run `drm_poc_ca` once. It provisions the TA's device key
     and writes device_pubkey.bin to the shared data directory.
  2. On the host: `python3 gen_test_vectors.py <data_dir>` reads that
     pubkey and writes the rest of the vectors into the same directory.
  3. Run `drm_poc_ca` again (still inside QEMU) — this time it finds the
     vectors and runs the real unwrap/decrypt/hash-proof flow.

Requires the `cryptography` package (already a project dependency, see
requirements.txt).
"""
from __future__ import annotations

import hashlib
import os
import sys

from cryptography.hazmat.primitives import hashes, hmac
from cryptography.hazmat.primitives.asymmetric import ec
from cryptography.hazmat.primitives.ciphers import Cipher, algorithms, modes

SESSION_KEY_INFO = b"drm-poc-sdp-v1"
DEMO_PLAINTEXT = (
    b"Phase 6b OP-TEE SDP demo plaintext -- if you can read this outside "
    b"the TA, the SDP buffer isn't doing its job.\n"
) * 8


def derive_session_key(shared_secret: bytes) -> bytes:
    h = hmac.HMAC(shared_secret, hashes.SHA256())
    h.update(SESSION_KEY_INFO)
    return h.finalize()


def aes_ctr_encrypt(key: bytes, iv: bytes, plaintext: bytes) -> bytes:
    encryptor = Cipher(algorithms.AES(key), modes.CTR(iv)).encryptor()
    return encryptor.update(plaintext) + encryptor.finalize()


def main() -> None:
    if len(sys.argv) != 2:
        print(f"usage: {sys.argv[0]} <data_dir containing device_pubkey.bin>")
        sys.exit(1)
    data_dir = sys.argv[1]

    pubkey_path = os.path.join(data_dir, "device_pubkey.bin")
    if not os.path.exists(pubkey_path):
        print(f"{pubkey_path} not found — run drm_poc_ca inside QEMU first "
              f"(it provisions the TA's device key and writes this file).")
        sys.exit(1)

    with open(pubkey_path, "rb") as f:
        device_pubkey_x963 = f.read()
    assert len(device_pubkey_x963) == 65 and device_pubkey_x963[0] == 0x04
    device_x = int.from_bytes(device_pubkey_x963[1:33], "big")
    device_y = int.from_bytes(device_pubkey_x963[33:65], "big")
    device_pub = ec.EllipticCurvePublicNumbers(device_x, device_y, ec.SECP256R1()).public_key()

    server_ephemeral_priv = ec.generate_private_key(ec.SECP256R1())
    server_ephemeral_pub_numbers = server_ephemeral_priv.public_key().public_numbers()
    server_ephemeral_x963 = (
        b"\x04"
        + server_ephemeral_pub_numbers.x.to_bytes(32, "big")
        + server_ephemeral_pub_numbers.y.to_bytes(32, "big")
    )

    shared_secret = server_ephemeral_priv.exchange(ec.ECDH(), device_pub)
    session_key = derive_session_key(shared_secret)

    content_key = os.urandom(16)
    wrapped_key_iv = os.urandom(16)
    wrapped_key_ct = aes_ctr_encrypt(session_key, wrapped_key_iv, content_key)

    sample_iv = os.urandom(16)
    sample_ct = aes_ctr_encrypt(content_key, sample_iv, DEMO_PLAINTEXT)

    plaintext_hash = hashlib.sha256(DEMO_PLAINTEXT).digest()

    def write(name: str, data: bytes) -> None:
        path = os.path.join(data_dir, name)
        with open(path, "wb") as f:
            f.write(data)
        print(f"wrote {path} ({len(data)} bytes)")

    write("server_ephemeral_pub.bin", server_ephemeral_x963)
    write("wrapped_key.bin", wrapped_key_iv + wrapped_key_ct)
    write("encrypted_sample.bin", sample_iv + sample_ct)
    write("plaintext_sha256.bin", plaintext_hash)

    print()
    print("Vectors written. Copy this directory into the guest at "
          "/data/drm_poc (or wherever your QEMU shared folder maps to), "
          "then run drm_poc_ca again.")


if __name__ == "__main__":
    main()
