#!/usr/bin/env bash
# Phase 1 — encode a multi-bitrate ladder from packaging/content/source/source.mp4.
#
# Four renditions, matching the tier names used throughout the PoC:
#   sd    240p  (426x240)
#   hd    480p  (854x480)
#   fhd  1080p  (1920x1080, pass-through from source)
#   uhd  2160p  (3840x2160, *upscaled* from the 1080p source — there is no real 4K
#                source in this PoC; this tier exists purely to exercise the
#                TEE-gated-key mechanics in Phase 5, not to show real 4K detail)
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
CONTENT_DIR="$SCRIPT_DIR/content"
SRC="$CONTENT_DIR/source/source.mp4"
OUT="$CONTENT_DIR/encoded"

if [[ ! -f "$SRC" ]]; then
  echo "missing $SRC — generate a source clip first" >&2
  exit 1
fi

mkdir -p "$OUT"

encode() {
  local name="$1" w="$2" h="$3" vbr="$4" maxrate="$5" bufsize="$6"
  echo "== encoding $name ($w x $h @ ${vbr}) =="
  ffmpeg -y -i "$SRC" \
    -vf "scale=${w}:${h}:flags=lanczos" \
    -c:v libx264 -preset veryfast -profile:v high -pix_fmt yuv420p \
    -b:v "$vbr" -maxrate "$maxrate" -bufsize "$bufsize" \
    -g 60 -keyint_min 60 -sc_threshold 0 \
    -c:a aac -b:a 128k -ac 2 \
    -movflags +faststart \
    "$OUT/${name}.mp4"
}

encode sd  426  240   500k   535k   750k
encode hd  854  480   1200k  1284k  1800k
encode fhd 1920 1080  4500k  4815k  6750k
encode uhd 3840 2160  9000k  9630k  13500k

echo "== done =="
ls -la "$OUT"
