#!/usr/bin/env bash
# Phase 1 — package the encoded ladder with shaka-packager under CENC, one
# distinct content key per quality tier (plus one for audio). This is the
# multi-key requirement that makes Phase 5's tier gating possible: a device
# that only receives the SD/HD/FHD keys can play everything except the UHD
# rendition, with zero client-side logic involved.
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
CONTENT_DIR="$SCRIPT_DIR/content"
ENCODED_DIR="$CONTENT_DIR/encoded"
OUT_DIR="$CONTENT_DIR/packaged"
PACKAGER="$SCRIPT_DIR/../bin/packager"
KEYS_JSON="$OUT_DIR/keys.json"

if [[ ! -x "$PACKAGER" ]]; then
  echo "missing packager binary at $PACKAGER" >&2
  exit 1
fi

mkdir -p "$OUT_DIR"

rand_hex16() { openssl rand -hex 16; }

# One KID+key pair per DRM label. Labels map 1:1 to quality tiers, matching
# the tier names used by policy.py / the /license endpoint in later phases.
LABELS=(SD HD FHD UHD AUDIO)
declare -A KEY_ID
declare -A KEY

for label in "${LABELS[@]}"; do
  KEY_ID[$label]="$(rand_hex16)"
  KEY[$label]="$(rand_hex16)"
done

KEYS_SPEC=""
for label in "${LABELS[@]}"; do
  KEYS_SPEC+="label=${label}:key_id=${KEY_ID[$label]}:key=${KEY[$label]},"
done
KEYS_SPEC="${KEYS_SPEC%,}"

# Write keys.json via env vars — bash associative arrays don't cross the
# subprocess boundary, so export each key_id/key pair first.
for label in "${LABELS[@]}"; do
  export "KEYID_${label}=${KEY_ID[$label]}"
  export "KEY_${label}=${KEY[$label]}"
done
python3 - "$KEYS_JSON" "${LABELS[@]}" <<'EOF'
import json, sys, os
out_path = sys.argv[1]
labels = sys.argv[2:]
entries = {}
for label in labels:
    entries[label] = {
        "key_id": os.environ[f"KEYID_{label}"],
        "key": os.environ[f"KEY_{label}"],
    }
with open(out_path, "w") as f:
    json.dump(entries, f, indent=2)
print(f"wrote {out_path}")
EOF

echo "== keys =="
cat "$KEYS_JSON"

STREAMS=(
  "in=${ENCODED_DIR}/sd.mp4,stream=video,init_segment=${OUT_DIR}/sd_video_init.mp4,segment_template=${OUT_DIR}/sd_video_\$Number\$.m4s,drm_label=SD"
  "in=${ENCODED_DIR}/hd.mp4,stream=video,init_segment=${OUT_DIR}/hd_video_init.mp4,segment_template=${OUT_DIR}/hd_video_\$Number\$.m4s,drm_label=HD"
  "in=${ENCODED_DIR}/fhd.mp4,stream=video,init_segment=${OUT_DIR}/fhd_video_init.mp4,segment_template=${OUT_DIR}/fhd_video_\$Number\$.m4s,drm_label=FHD"
  "in=${ENCODED_DIR}/uhd.mp4,stream=video,init_segment=${OUT_DIR}/uhd_video_init.mp4,segment_template=${OUT_DIR}/uhd_video_\$Number\$.m4s,drm_label=UHD"
  "in=${ENCODED_DIR}/fhd.mp4,stream=audio,init_segment=${OUT_DIR}/audio_init.mp4,segment_template=${OUT_DIR}/audio_\$Number\$.m4s,drm_label=AUDIO"
)

"$PACKAGER" \
  "${STREAMS[@]}" \
  --enable_raw_key_encryption \
  --keys="$KEYS_SPEC" \
  --protection_scheme cenc \
  --clear_lead 0 \
  --segment_duration 6 \
  --mpd_output "${OUT_DIR}/dash.mpd" \
  --generate_dash_if_iop_compliant_mpd \
  --generate_static_live_mpd

echo "== packaged output =="
ls -la "$OUT_DIR"
echo "== dash.mpd =="
cat "${OUT_DIR}/dash.mpd"
