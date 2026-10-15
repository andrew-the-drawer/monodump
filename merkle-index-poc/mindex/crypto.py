"""Client-side path obfuscation.

The server must be able to address files ("replace the chunks of file X",
"give me the children of directory Y") without learning their names. We
encrypt every path *segment* separately with AES-SIV:

- SIV is deterministic: the same plaintext always yields the same ciphertext,
  so `src/app.py` maps to the same opaque path on every sync, and prefixes are
  preserved (`enc(src)/enc(app.py)` lives under `enc(src)`). That is what lets
  the server keep a tree and do prefix deletes.
- It is still authenticated encryption; without the key the server can only
  observe equality ("these two segments have the same name"), never content.

Cursor describes the same idea as encrypting each path component with a
client-held key and a deterministic nonce.

Known leak (by design, also true of per-segment schemes in general):
segment equality and segment count/length are visible to the server.
"""

from __future__ import annotations

import base64
import os
from pathlib import Path

from cryptography.hazmat.primitives.ciphers.aead import AESSIV

KEY_BYTES = 64  # AES-SIV with AES-256 needs a 512-bit key


def _b64(data: bytes) -> str:
    return base64.urlsafe_b64encode(data).rstrip(b"=").decode()


def _unb64(text: str) -> bytes:
    return base64.urlsafe_b64decode(text + "=" * (-len(text) % 4))


def load_or_create_key(key_file: Path) -> bytes:
    """Read the workspace key, creating it on first use.

    Teammates who want to share an index (see `fork`) must share this key,
    otherwise their encrypted paths will not line up.
    """
    if key_file.exists():
        key = key_file.read_bytes()
        if len(key) != KEY_BYTES:
            raise ValueError(f"{key_file} is not a {KEY_BYTES}-byte key")
        return key
    key_file.parent.mkdir(parents=True, exist_ok=True)
    key = AESSIV.generate_key(KEY_BYTES * 8)
    key_file.write_bytes(key)
    os.chmod(key_file, 0o600)
    return key


class PathCipher:
    def __init__(self, key: bytes):
        self._siv = AESSIV(key)

    def encrypt_segment(self, name: str) -> str:
        return _b64(self._siv.encrypt(name.encode(), None))

    def decrypt_segment(self, token: str) -> str:
        return self._siv.decrypt(_unb64(token), None).decode()

    def encrypt_path(self, rel_path: str) -> str:
        """`src/app.py` -> `<opaque>/<opaque>`. The root is the empty string."""
        if rel_path in ("", "."):
            return ""
        return "/".join(self.encrypt_segment(s) for s in rel_path.split("/"))

    def decrypt_path(self, enc_path: str) -> str:
        if enc_path == "":
            return ""
        return "/".join(self.decrypt_segment(s) for s in enc_path.split("/"))
