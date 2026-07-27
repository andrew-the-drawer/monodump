# drm-poc

A from-scratch, Netflix-shaped DRM stack: encode → CENC-encrypt with
per-tier keys → serve a real (if simplified) license protocol → gate quality
tiers by a server-asserted security level. See `PLAN.md` for the full design
and rationale; `docs/` for the primer, protocol spec, and (later) the TEE/
attack write-ups.

**Status: Phases 0–5 implemented.** Phase 6 (real TEE — Secure Enclave /
OP-TEE) and Phase 7 (attack demo) are not part of this pass.

## One-time setup

```bash
cd /Users/lantrungseo/Documents/app-dev/lantrungseo/monodump
source venv/bin/activate   # repo-root venv, per CLAUDE.md

# packager binary (prebuilt, not in Homebrew) — already fetched into drm-poc/bin/
# if missing: download packager-osx-arm64 from
# https://github.com/shaka-project/shaka-packager/releases and chmod +x it
# into drm-poc/bin/packager
```

## Build the content (Phase 1)

```bash
cd drm-poc/packaging
./encode.sh     # ffmpeg ladder: sd(240p) hd(480p) fhd(1080p) uhd(2160p, upscaled — see encode.sh)
./package.sh    # shaka-packager, CENC, one random key per tier + one for audio
                # regenerates content/packaged/keys.json with FRESH keys every run
```

Inspect what got produced:
```bash
python3 ../tools/inspect_mp4.py content/packaged/sd_video_init.mp4 content/packaged/uhd_video_init.mp4
```
Shows the `pssh` (common, DRM-agnostic, lists all KIDs), `tenc` (per-track
default KID + IV size), and — against a media segment (`sd_video_1.m4s`) —
`senc`/`saiz`/`saio` (per-sample IVs and subsample clear/encrypted ranges).

## Run the server

```bash
cd ../server
python3 seed_content.py     # loads packaging/content/packaged/keys.json into keys.db
                             # re-run this any time you re-run package.sh (keys rotate)
uvicorn main:app --host 127.0.0.1 --port 8000
```

Open **http://127.0.0.1:8000/player/** in Chrome. `localhost` satisfies EME's
secure-context requirement, and one origin serves the player, the packaged
DASH content, and the API — no CORS needed.

- **Mode: Phase 2 — ClearKey (insecure)** — closes the EME loop against the
  trivial `/clearkey-license` endpoint. Stop the server (or comment out that
  route) and playback stops dead.
- **Mode: Phase 3+ — our license protocol**, **Device: SW** — provisions a
  software-only device (WebCrypto, non-extractable keys but no hardware
  backing) and runs the full provisioning + license exchange from
  `docs/01-protocol.md`. Gets 4 of 5 keys (no UHD) and is transparently
  capped below the 4K tier.
- **Device: TEE** — provisions with the (simulated — see below) attestation
  secret and gets all 5 keys, including UHD. Same content, same player,
  different ceiling — **zero client-side gating logic**; the cap is a pure
  consequence of which keys ClearKey was handed.

## Verifying without a human

Every route has a scriptable counterpart so the protocol and policy
properties don't rely on eyeballing a video:

```bash
# Phase 3: provisioning + license exchange, MAC/AEAD round-trip, tamper and
# replay-on-a-different-device rejection.
python3 tools/protocol_client.py

# Phase 4: all five policies (expiry+renewal, rental window, device binding,
# revocation, concurrent-stream cap), each proven by a clean HTTP rejection.
python3 tools/demo_policies.py
```

The player also accepts `?autoload=clearkey|protocol&level=SW|TEE` to drive
itself without a click — used during development to verify real decrypted
frames render via headless Chrome screenshots (`--headless=new
--screenshot=... --virtual-time-budget=...`).

`demo_policies.py` uses `/admin/policy` and `/admin/sessions/reset` to run
the 48-hour rental window and multi-second renewal cycle in a few seconds.
Those two routes plus `/admin/devices*` are demo/ops seams, not part of the
device-facing protocol — see the comments in `server/main.py`.

## What's simulated vs real

- **Real**: CENC encryption with per-tier keys (Phase 1); ECDSA/ECDH P-256 +
  HKDF + AES-GCM + HMAC session key exchange, run independently in Python
  (server, and `tools/protocol_client.py`) and in the browser via WebCrypto,
  cross-verified byte-for-byte (Phase 3); all Phase 4 policy rejections;
  Phase 5 tier gating (the KID subset really is decided server-side from a
  server-held security-level record, and ClearKey really can't decrypt what
  it wasn't given).
- **Simulated, clearly labeled in code and `docs/01-protocol.md`**: TEE
  attestation is a hardcoded shared secret
  (`SIMULATED_ATTESTATION_SECRET`), not a real hardware-rooted signature —
  that's what Phase 6 (Secure Enclave / OP-TEE, not built here) replaces.
  Policy enforcement *after* the initial grant (expiry/rental/revocation/
  concurrency) is modeled as "the periodic renewal call gets rejected and
  the client tears down playback," rather than "the CDM's already-issued
  keys stop working" — ClearKey has no native per-key expiry, and real
  per-segment re-keying is out of scope for this PoC.
- **Synthetic content**: `packaging/content/source/source.mp4` is an
  `ffmpeg testsrc2` pattern (Homebrew's ffmpeg lacks `drawtext`/libfreetype),
  not a Blender movie — same encryption/protocol properties, just not a real
  film. The "UHD" tier is a Lanczos upscale of the 1080p source, not a real
  4K source — it exists to exercise the tier-gating *mechanism*.

## Repo layout

See `PLAN.md` Part 2 for the target layout; this is what's actually here:

```
drm-poc/
├── bin/packager              gitignored — prebuilt shaka-packager binary
├── docs/
│   ├── 00-primer.md          CENC, boxes, EME state machine
│   └── 01-protocol.md        the Phase 3 protocol spec, written before the code
├── packaging/
│   ├── encode.sh / package.sh
│   └── content/               gitignored — source, encoded, packaged output
├── server/
│   ├── main.py                FastAPI app: routes
│   ├── license.py             /provision, /license handlers
│   ├── crypto.py              ECDSA/ECDH/HKDF/AEAD/HMAC primitives, root CA, master token
│   ├── policy.py              Phase 4/5 enforcement
│   ├── models.py               keys.db / devices.db / policies.db (all gitignored)
│   └── seed_content.py
├── player/
│   ├── index.html / cdm-bridge.js   shaka-player + WebCrypto protocol client
└── tools/
    ├── inspect_mp4.py          Phase 1 box dumper
    ├── protocol_client.py      Python stand-in device (used for testing)
    └── demo_policies.py        Phase 4 proof script
```
