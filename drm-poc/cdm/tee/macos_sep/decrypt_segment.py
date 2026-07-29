#!/usr/bin/env python3
"""Phase 6a: real CENC decryption of a packaged CMAF segment, using a
content key that came back from `device.py`'s Secure-Enclave-backed license
request. This is the concrete "a content key is used to decrypt video"
half of Phase 6's done-when (PLAN.md) — the other half, "without that key
ever existing in the player process's address space," is honestly *not*
true here (the content key is a plain Python bytes object in this process;
see docs/02-tee.md for why that's the expected 6a boundary, and 6b for the
track that actually closes it).

Parses just enough ISO BMFF (reusing `tools/inspect_mp4.py`'s box walker)
to find the first video sample's ciphertext, IV, and subsample map, AES-CTR
decrypts it, and confirms the result is genuine H.264 by handing it to
`ffprobe` after converting from AVCC (length-prefixed) to Annex-B framing.

Usage:
    python3 cdm/tee/macos_sep/device.py             # first, to grant keys
    python3 cdm/tee/macos_sep/decrypt_segment.py       # then, to decrypt
"""
from __future__ import annotations

import contextlib
import io
import json
import os
import struct
import subprocess
import sys
import tempfile

from cryptography.hazmat.primitives.ciphers import Cipher, algorithms, modes

HERE = os.path.dirname(os.path.abspath(__file__))
TOOLS_DIR = os.path.join(HERE, "..", "..", "..", "tools")
sys.path.insert(0, os.path.abspath(TOOLS_DIR))
from inspect_mp4 import (  # noqa: E402
    CONTAINER_TYPES,
    VISUAL_FIXED_SIZE,
    VISUAL_SAMPLE_ENTRY_TYPES,
    read_boxes,
    walk as inspect_mp4_walk,
)

PACKAGED_DIR = os.path.join(HERE, "..", "..", "..", "packaging", "content", "packaged")
GRANTED_KEYS_PATH = os.path.join(HERE, ".last_granted_keys.json")


def find_box(data: bytes, start: int, end: int, target: bytes):
    """Depth-first search for the first box of type `target`; returns
    (payload_start, payload_end) or None."""
    for box_type, s, e in read_boxes(data, start, end):
        if box_type == target:
            return s, e
        if box_type in CONTAINER_TYPES:
            found = find_box(data, s, e, target)
            if found:
                return found
    return None


def find_tenc(data: bytes) -> tuple[str, int]:
    """`tenc` lives inside stsd -> sample_entry (encv/enca) -> sinf, and the
    sample_entry's fixed-size prefix needs skipping before descending into
    its child boxes — logic `tools/inspect_mp4.py`'s `walk()` already has
    (`walk_stsd`). Reuse it instead of re-deriving that offset here."""
    ctx: dict = {}
    with contextlib.redirect_stdout(io.StringIO()):
        inspect_mp4_walk(data, 0, len(data), 0, ctx)
    tenc = ctx.get("tenc")
    if not tenc:
        raise RuntimeError("no tenc box found")
    return tenc["kid"].hex, tenc["iv_size"]


def parse_tfhd(data: bytes, s: int, e: int) -> dict:
    flags = struct.unpack(">I", data[s:s + 4])[0] & 0xFFFFFF
    off = s + 4 + 4  # FullBox header + track_ID
    default_sample_size = None
    if flags & 0x000001:  # base-data-offset-present
        off += 8
    if flags & 0x000002:  # sample-description-index-present
        off += 4
    if flags & 0x000008:  # default-sample-duration-present
        off += 4
    if flags & 0x000010:  # default-sample-size-present
        default_sample_size = struct.unpack(">I", data[off:off + 4])[0]
        off += 4
    return {"default_sample_size": default_sample_size}


def parse_trun(data: bytes, s: int, e: int) -> dict:
    flags = struct.unpack(">I", data[s:s + 4])[0] & 0xFFFFFF
    off = s + 4
    sample_count = struct.unpack(">I", data[off:off + 4])[0]
    off += 4
    data_offset = 0
    if flags & 0x000001:  # data-offset-present
        data_offset = struct.unpack(">i", data[off:off + 4])[0]
        off += 4
    if flags & 0x000004:  # first-sample-flags-present
        off += 4
    sizes: list[int | None] = []
    for _ in range(sample_count):
        if flags & 0x000100:  # sample-duration-present
            off += 4
        size = None
        if flags & 0x000200:  # sample-size-present
            size = struct.unpack(">I", data[off:off + 4])[0]
            off += 4
        sizes.append(size)
        if flags & 0x000400:  # sample-flags-present
            off += 4
        if flags & 0x000800:  # sample-composition-time-offsets-present
            off += 4
    return {"data_offset": data_offset, "sample_sizes": sizes}


def parse_senc_first_sample(data: bytes, s: int, e: int, iv_size: int) -> dict:
    flags = struct.unpack(">I", data[s:s + 4])[0] & 0xFFFFFF
    has_subsamples = bool(flags & 0x2)
    off = s + 4 + 4  # FullBox header + sample_count (we only need sample 0)
    iv = data[off:off + iv_size]
    off += iv_size
    subsamples = []
    if has_subsamples:
        subsample_count = struct.unpack(">H", data[off:off + 2])[0]
        off += 2
        for _ in range(subsample_count):
            clear, enc = struct.unpack(">HI", data[off:off + 6])
            subsamples.append((clear, enc))
            off += 6
    return {"iv": iv, "subsamples": subsamples}


def decrypt_first_sample(init_path: str, media_path: str, key_hex: str) -> tuple[str, bytes]:
    init_data = open(init_path, "rb").read()
    media_data = open(media_path, "rb").read()

    kid, iv_size = find_tenc(init_data)

    moof_payload = find_box(media_data, 0, len(media_data), b"moof")
    if not moof_payload:
        raise RuntimeError(f"no moof box in {media_path}")
    # read_boxes returns payload bounds (header excluded); moof's own box
    # start (what trun's data_offset is relative to, per ISO/IEC 14496-12)
    # is 8 bytes earlier in the standard (non-64-bit-size) case.
    moof_box_start = moof_payload[0] - 8
    moof_start, moof_end = moof_payload

    traf = find_box(media_data, moof_start, moof_end, b"traf")
    tfhd_box = find_box(media_data, traf[0], traf[1], b"tfhd")
    trun_box = find_box(media_data, traf[0], traf[1], b"trun")
    senc_box = find_box(media_data, traf[0], traf[1], b"senc")

    tfhd = parse_tfhd(media_data, *tfhd_box)
    trun = parse_trun(media_data, *trun_box)
    senc = parse_senc_first_sample(media_data, *senc_box, iv_size=iv_size)

    first_sample_size = trun["sample_sizes"][0] or tfhd["default_sample_size"]
    if not first_sample_size:
        raise RuntimeError("could not determine first sample size from trun/tfhd")

    first_sample_offset = moof_box_start + trun["data_offset"]
    ciphertext = media_data[first_sample_offset:first_sample_offset + first_sample_size]

    key = bytes.fromhex(key_hex)
    iv = senc["iv"]
    iv16 = iv + b"\x00" * (16 - len(iv))  # CENC 'cenc': 8-byte IV, zero-padded, CTR counter in low bits
    decryptor = Cipher(algorithms.AES(key), modes.CTR(iv16)).decryptor()

    subsamples = senc["subsamples"]
    if subsamples:
        plaintext = bytearray()
        pos = 0
        for clear, enc in subsamples:
            plaintext += ciphertext[pos:pos + clear]
            pos += clear
            plaintext += decryptor.update(ciphertext[pos:pos + enc])
            pos += enc
        plaintext += decryptor.finalize()
        plaintext = bytes(plaintext)
    else:
        plaintext = decryptor.update(ciphertext) + decryptor.finalize()

    return kid, plaintext


def find_avcc_sps_pps(init_data: bytes) -> bytes:
    """AVC-in-MP4 stores SPS/PPS once in the init segment's `avcC` box, not
    per-sample — a fragmented sample's own NALs reference them by ID rather
    than repeating them. `ffprobe` needs them in-stream to decode a lone
    sample standalone, so we pull them out and prepend them (as Annex-B)
    ourselves. `avcC` sits inside stsd -> sample_entry (`encv`), which needs
    the same fixed-size-prefix skip as `tenc` — but since we already know
    exactly which one-level range to search, no need for the fuller
    stsd-walking `inspect_mp4.py` does for the generic case."""
    stsd = find_box(init_data, 0, len(init_data), b"stsd")
    if not stsd:
        raise RuntimeError("no stsd box found")
    s, e = stsd
    pos = s + 8  # FullBox header (4) + entry_count (4)
    for box_type, entry_s, entry_e in read_boxes(init_data, pos, e):
        if box_type in VISUAL_SAMPLE_ENTRY_TYPES:
            avcc = find_box(init_data, entry_s + VISUAL_FIXED_SIZE, entry_e, b"avcC")
            if avcc:
                avcc_data = init_data[avcc[0]:avcc[1]]
                off = 5  # version, profile, compat, level, lengthSizeMinusOne(2 low bits)
                num_sps = avcc_data[off] & 0x1F
                off += 1
                out = bytearray()
                for _ in range(num_sps):
                    length = struct.unpack(">H", avcc_data[off:off + 2])[0]
                    off += 2
                    out += b"\x00\x00\x00\x01" + avcc_data[off:off + length]
                    off += length
                num_pps = avcc_data[off]
                off += 1
                for _ in range(num_pps):
                    length = struct.unpack(">H", avcc_data[off:off + 2])[0]
                    off += 2
                    out += b"\x00\x00\x00\x01" + avcc_data[off:off + length]
                    off += length
                return bytes(out)
        break  # exactly one sample entry expected
    raise RuntimeError("no avcC found in stsd sample entry")


def avcc_to_annexb(data: bytes, length_size: int = 4) -> bytes:
    """AVCC (length-prefixed) NAL units -> Annex-B (start-code-prefixed),
    which `ffprobe -f h264` can parse directly."""
    out = bytearray()
    pos = 0
    while pos + length_size <= len(data):
        nal_len = int.from_bytes(data[pos:pos + length_size], "big")
        pos += length_size
        if nal_len <= 0 or pos + nal_len > len(data):
            break
        out += b"\x00\x00\x00\x01" + data[pos:pos + nal_len]
        pos += nal_len
    return bytes(out)


def confirm_h264(plaintext: bytes, sps_pps_annexb: bytes) -> str:
    """A weaker version of this check (`ffprobe -show_entries
    frame=pict_type`) turned out to be a false positive: CENC's subsample
    map leaves the first ~700 bytes of the slice NAL — including the slice
    header, which is where `pict_type` comes from — in the clear on
    purpose (so the container stays parseable), while only the actual
    slice *data* past that point is encrypted. So `pict_type` reads "I"
    correctly even when decrypting under a wrong key entirely, because
    that field never depended on the encrypted bytes in the first place.
    Caught this by decrypting the same sample under a wrong key and seeing
    the same "confirmed" result — see docs/02-tee.md.

    What actually depends on the encrypted region being right is whether
    the slice *data* (CABAC-coded residuals) decodes cleanly: a wrong key
    still produces a well-formed slice header (unencrypted) but garbage
    residuals, which a full decode reliably reports as bitstream errors
    ("error while decoding MB...", "corrupt decoded frame") even though
    error concealment still emits *a* frame. So the real test is a full
    `ffmpeg` decode with zero decoder warnings/errors on stderr — verified
    against both a correct and a wrong key before trusting this check.
    """
    annexb = sps_pps_annexb + avcc_to_annexb(plaintext)
    with tempfile.NamedTemporaryFile(suffix=".h264", delete=False) as f:
        f.write(annexb)
        path = f.name
    try:
        proc = subprocess.run(
            ["ffmpeg", "-v", "warning", "-f", "h264", "-i", path, "-f", "null", "-"],
            capture_output=True, text=True,
        )
        if proc.returncode != 0 or proc.stderr.strip():
            return f"ffmpeg decode reported problems — NOT a clean decode:\n{proc.stderr.strip()}"
        return "ffmpeg decoded the frame with zero warnings/errors — genuine, correctly-decrypted H.264"
    finally:
        os.unlink(path)


def main() -> None:
    if not os.path.exists(GRANTED_KEYS_PATH):
        print(f"{GRANTED_KEYS_PATH} not found — run device.py first to provision and get a license.")
        sys.exit(1)
    with open(GRANTED_KEYS_PATH) as f:
        granted_keys: dict[str, str] = json.load(f)

    init_path = os.path.join(PACKAGED_DIR, "fhd_video_init.mp4")
    media_path = os.path.join(PACKAGED_DIR, "fhd_video_1.m4s")
    if not os.path.exists(init_path):
        print(f"{init_path} not found — run packaging/encode.sh && packaging/package.sh first.")
        sys.exit(1)

    init_data = open(init_path, "rb").read()
    tenc_kid, _ = find_tenc(init_data)
    if tenc_kid not in granted_keys:
        print(f"granted keys don't include this tier's KID ({tenc_kid}) — "
              f"granted: {sorted(granted_keys)}. Was this device gated below FHD?")
        sys.exit(1)

    sps_pps_annexb = find_avcc_sps_pps(init_data)
    kid, plaintext = decrypt_first_sample(init_path, media_path, granted_keys[tenc_kid])
    print(f"decrypted first sample of fhd_video_1.m4s under KID {kid}: {len(plaintext)} bytes plaintext")
    print(confirm_h264(plaintext, sps_pps_annexb))


if __name__ == "__main__":
    main()
