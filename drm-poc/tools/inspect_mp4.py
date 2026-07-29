#!/usr/bin/env python3
"""Phase 1 tool — dump the ISO BMFF boxes that carry CENC encryption metadata.

Walks an MP4/CMAF file (init segment, media segment, or the two concatenated)
and prints, for each box it finds:

  - the plain box tree (proving headers stay in the clear even when the
    payload is encrypted)
  - 'pssh'  — per-DRM-system opaque blob + the KIDs it protects
  - 'tenc'  — the track's default KID, per-sample IV size, protection scheme
  - 'senc'  — per-sample IVs, and subsample (clear/encrypted) byte ranges
  - 'saiz'/'saio' — the sample-auxiliary-info size/offset index

Usage:
    python tools/inspect_mp4.py file1.mp4 [file2.mp4 ...]
    cat sd_video_init.mp4 sd_video_1.m4s | python tools/inspect_mp4.py -
"""
from __future__ import annotations

import struct
import sys
import uuid

CONTAINER_TYPES = {
    b"moov", b"trak", b"mdia", b"minf", b"stbl", b"mvex",
    b"moof", b"traf", b"udta", b"edts", b"sinf", b"schi", b"dinf",
}

# ISOBMFF SampleEntry fixed-field sizes (bytes after the box header) before
# any child boxes begin. SampleEntry common prefix (8) is already included.
VISUAL_SAMPLE_ENTRY_TYPES = {b"avc1", b"encv", b"hev1", b"hvc1", b"vp09", b"av01"}
AUDIO_SAMPLE_ENTRY_TYPES = {b"mp4a", b"enca", b"ac-3", b"ec-3"}
VISUAL_FIXED_SIZE = 78
AUDIO_FIXED_SIZE = 28

# urn:uuid SystemIDs for common DRM pssh boxes, for readability only.
KNOWN_SYSTEM_IDS = {
    "1077efec-c0b2-4d02-ace3-3c1e52e2fb4b": "Common (v1 CENC, DRM-agnostic KID list)",
    "edef8ba9-79d6-4ace-a3c8-27dcd51d21ed": "Widevine",
    "9a04f079-9840-4286-ab92-e65be0885f95": "PlayReady",
    "94ce86fb-07ff-4f43-adb8-93d2fa968ca2": "FairPlay",
}


def read_boxes(data: bytes, start: int, end: int):
    """Yield (type, payload_start, payload_end) for each box in data[start:end]."""
    pos = start
    while pos + 8 <= end:
        size = struct.unpack(">I", data[pos:pos + 4])[0]
        box_type = data[pos + 4:pos + 8]
        header_size = 8
        if size == 1:
            size = struct.unpack(">Q", data[pos + 8:pos + 16])[0]
            header_size = 16
        elif size == 0:
            size = end - pos
        payload_start = pos + header_size
        payload_end = pos + size
        yield box_type, payload_start, min(payload_end, end)
        pos += size
        if size <= 0:
            break


def indent_print(depth: int, msg: str):
    print("  " * depth + msg)


def parse_pssh(data: bytes, s: int, e: int, depth: int):
    version = data[s]
    system_id = uuid.UUID(bytes=data[s + 4:s + 20])
    off = s + 20
    kids = []
    if version >= 1:
        kid_count = struct.unpack(">I", data[off:off + 4])[0]
        off += 4
        for _ in range(kid_count):
            kids.append(uuid.UUID(bytes=data[off:off + 16]))
            off += 16
    data_size = struct.unpack(">I", data[off:off + 4])[0]
    off += 4
    label = KNOWN_SYSTEM_IDS.get(str(system_id), "unknown")
    indent_print(depth, f"pssh: system_id={system_id} ({label}) version={version}")
    if kids:
        indent_print(depth + 1, f"kids: {[str(k) for k in kids]}")
    indent_print(depth + 1, f"data: {data_size} bytes opaque payload (per-DRM, not our concern)")


def parse_tenc(data: bytes, s: int, e: int, depth: int):
    # FullBox header: 1 byte version, 3 bytes flags.
    version = data[s]
    off = s + 4
    off += 1  # reserved
    if version > 0:
        crypt_byte_block = data[off] >> 4
        skip_byte_block = data[off] & 0x0F
        indent_print(depth, f"tenc: pattern {crypt_byte_block}:{skip_byte_block} (cbcs-style)")
    off += 1
    is_protected = data[off]
    off += 1
    iv_size = data[off]
    off += 1
    kid = uuid.UUID(bytes=data[off:off + 16])
    off += 16
    indent_print(depth, f"tenc: default_KID={kid} is_protected={is_protected} per_sample_iv_size={iv_size}")
    return {"kid": kid, "iv_size": iv_size, "is_protected": is_protected}


def parse_saiz(data: bytes, s: int, e: int, depth: int):
    flags = struct.unpack(">I", data[s:s + 4])[0] & 0xFFFFFF
    off = s + 4
    if flags & 1:
        off += 8  # aux_info_type + parameter
    default_size = data[off]
    off += 1
    sample_count = struct.unpack(">I", data[off:off + 4])[0]
    off += 4
    sizes = []
    if default_size == 0:
        sizes = list(data[off:off + sample_count])
    indent_print(depth, f"saiz: sample_count={sample_count} default_info_size={default_size}"
                 + (f" sizes={sizes[:8]}{'...' if len(sizes) > 8 else ''}" if sizes else ""))


def parse_saio(data: bytes, s: int, e: int, depth: int):
    version = data[s]
    flags = struct.unpack(">I", data[s:s + 4])[0] & 0xFFFFFF
    off = s + 4
    if flags & 1:
        off += 8
    entry_count = struct.unpack(">I", data[off:off + 4])[0]
    off += 4
    offsets = []
    entry_size = 8 if version == 1 else 4
    fmt = ">Q" if version == 1 else ">I"
    for _ in range(entry_count):
        offsets.append(struct.unpack(fmt, data[off:off + entry_size])[0])
        off += entry_size
    indent_print(depth, f"saio: entry_count={entry_count}"
                 + (f" offsets={offsets[:8]}{'...' if len(offsets) > 8 else ''}" if offsets else ""))


def parse_senc(data: bytes, s: int, e: int, depth: int, iv_size: int):
    flags = struct.unpack(">I", data[s:s + 4])[0] & 0xFFFFFF
    has_subsamples = bool(flags & 0x2)
    off = s + 4
    sample_count = struct.unpack(">I", data[off:off + 4])[0]
    off += 4
    indent_print(depth, f"senc: sample_count={sample_count} has_subsample_info={has_subsamples}"
                 + (f" (per-sample IV size assumed {iv_size}B from tenc)" if iv_size else " (iv_size unknown, guessing 8B)"))
    iv_size = iv_size or 8
    shown = 0
    while off < e and shown < 3:
        iv = data[off:off + iv_size].hex()
        off += iv_size
        subsample_desc = ""
        if has_subsamples:
            subsample_count = struct.unpack(">H", data[off:off + 2])[0]
            off += 2
            ranges = []
            for _ in range(subsample_count):
                clear, enc = struct.unpack(">HI", data[off:off + 6])
                ranges.append((clear, enc))
                off += 6
            subsample_desc = f" subsamples(clear,enc)={ranges}"
        indent_print(depth + 1, f"sample[{shown}]: iv={iv}{subsample_desc}")
        shown += 1
    if sample_count > shown:
        indent_print(depth + 1, f"... {sample_count - shown} more samples")


def walk(data: bytes, start: int, end: int, depth: int, ctx: dict):
    for box_type, s, e in read_boxes(data, start, end):
        name = box_type.decode("ascii", "replace")
        indent_print(depth, f"{name}  size={e - s + 8}")
        if box_type == b"pssh":
            parse_pssh(data, s, e, depth + 1)
        elif box_type == b"tenc":
            info = parse_tenc(data, s, e, depth + 1)
            ctx["tenc"] = info
            ctx.setdefault("kids", set()).add(str(info["kid"]))
        elif box_type == b"saiz":
            parse_saiz(data, s, e, depth + 1)
        elif box_type == b"saio":
            parse_saio(data, s, e, depth + 1)
        elif box_type == b"senc":
            iv_size = ctx.get("tenc", {}).get("iv_size", 0)
            parse_senc(data, s, e, depth + 1, iv_size)
        elif box_type == b"stsd":
            walk_stsd(data, s, e, depth + 1, ctx)
        elif box_type in CONTAINER_TYPES:
            walk(data, s, e, depth + 1, ctx)


def walk_stsd(data: bytes, s: int, e: int, depth: int, ctx: dict):
    # FullBox header (4) + entry_count (4).
    entry_count = struct.unpack(">I", data[s + 4:s + 8])[0]
    pos = s + 8
    indent_print(depth, f"stsd: entry_count={entry_count}")
    for _ in range(entry_count):
        for box_type, entry_s, entry_e in read_boxes(data, pos, e):
            name = box_type.decode("ascii", "replace")
            indent_print(depth + 1, f"sample entry: {name}")
            if box_type in VISUAL_SAMPLE_ENTRY_TYPES:
                fixed = VISUAL_FIXED_SIZE
            elif box_type in AUDIO_SAMPLE_ENTRY_TYPES:
                fixed = AUDIO_FIXED_SIZE
            else:
                fixed = 8  # unknown entry type; best effort
            child_start = entry_s + fixed
            walk(data, child_start, entry_e, depth + 2, ctx)
            pos = entry_e
            break  # read_boxes already advances; we only want the first here


def inspect(path: str, data: bytes):
    print(f"=== {path} ({len(data)} bytes) ===")
    ctx: dict = {}
    walk(data, 0, len(data), 0, ctx)
    if ctx.get("kids"):
        print(f"--- KIDs seen in {path}: {sorted(ctx['kids'])}")
    print()
    return ctx.get("kids", set())


def main(argv):
    if len(argv) < 2:
        print(__doc__)
        return 1
    all_kids = set()
    for path in argv[1:]:
        data = sys.stdin.buffer.read() if path == "-" else open(path, "rb").read()
        all_kids |= inspect(path, data)
    print(f"=== distinct KIDs across all inputs: {len(all_kids)} ===")
    for k in sorted(all_kids):
        print(f"  {k}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
