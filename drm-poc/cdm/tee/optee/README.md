# Phase 6b — OP-TEE on QEMU + Secure Data Path

**Status: UNTESTED.** Nothing in this directory has been compiled, booted,
or run. It's written as carefully as possible against the GlobalPlatform TEE
Internal Core API and the OP-TEE build system's documented shape, but until
someone actually runs `build.sh` end to end, treat every file here as
unverified source, not a working demo. This was a deliberate scope decision
(see `PLAN.md` Part 4 and `docs/02-tee.md`): a real build needs a Linux
host, ~15–20GB of disk, and a multi-hour first sync+compile, so this pass
scaffolds the complete design instead of spending that time. If you build
it and find bugs, that's expected — fix forward and update this line.

## What this proves, and what it doesn't (yet)

Phase 6a (`cdm/tee/macos_sep`) is real, verified, and runs on this machine's
actual Secure Enclave — but it's honest that the SEP is "a key store with
compute, not a full TEE that can run our decryptor": the derived session
key and content key still land in a Python process's heap. 6b is the track
that closes that gap — decryption happens *inside* secure-world code (a
Trusted Application, "TA"), and the plaintext lands in a buffer ("Secure
Data Path", SDP) that's physically inaccessible to normal-world Linux, not
just logically off-limits.

QEMU's `qemu_v8` reference platform has no VPU and no protected display, so
there's no way to *watch* video decrypted this way — showing pixels would
require handing plaintext to normal world, which destroys the property
being demonstrated. The demo is built around a negative test instead (see
PLAN.md's own framing): can normal-world Linux read the buffer the TA just
decrypted into? No. Can we still prove the decryption was correct? Yes —
via a hash, never the plaintext itself.

## Layout

```
cdm/tee/optee/
├── README.md            this file
├── Dockerfile            Ubuntu 22.04 build environment (OP-TEE's build
│                         system targets Linux hosts, not macOS)
├── build.sh              repo init/sync + make, with CFG_SECURE_DATA_PATH=y
│                         and CFG_WITH_PAGER=n (see "toolchain trap" below)
├── run.sh                boots the built images under QEMU
├── gen_test_vectors.py   offline "license server" stand-in — generates the
│                         wrapped content key + encrypted sample the CA
│                         feeds to the TA (see "two-step workflow" below)
├── ta/                   the Trusted Application
│   ├── drm_poc_ta.c
│   ├── include/
│   │   ├── drm_poc_ta.h            UUID + command IDs, shared with host/
│   │   └── user_ta_header_defines.h
│   ├── Makefile
│   └── sub.mk
└── host/                 the Client Application ("CA")
    ├── main.c
    └── Makefile
```

## The three TA commands

See `ta/include/drm_poc_ta.h` for the exact parameter shapes.

1. **`PROVISION_KEY`** — generates (or reopens) a persistent P-256 ECDH
   keypair inside the TA via GP secure storage. Never returns the private
   key. The TA analogue of `cdm/tee/macos_sep`'s persistent identity key.
2. **`UNWRAP_AND_DECRYPT`** — derives a session key via ECDH against a
   caller-supplied peer public key, uses it to unwrap a content key, then
   AES-CTR-decrypts an encrypted sample **directly into the caller's output
   buffer**. If that buffer is genuinely SDP-backed (see below), the
   plaintext this call produces is never REE-visible.
3. **`HASH_PROOF`** — SHA-256 of a buffer, returned in place of the buffer
   itself. Lets the CA (and us) confirm decryption was correct without
   ever seeing the plaintext.

Simplification, stated plainly: session-key derivation here is
`HMAC-SHA256(ecdh_shared_secret, "drm-poc-sdp-v1")`, not the real
`docs/01-protocol.md` HKDF with a per-request nonce salt. This TA
demonstrates the SDP mechanism — the reason 6b exists — not a byte-exact
reimplementation of the Phase 3 protocol inside secure world. Wiring the
exact protocol in is future work.

## Secure Data Path

`host/main.c`'s `alloc_output_buffer()` allocates the TA's output buffer
from `/dev/dma_heap/sdp` — physical memory OP-TEE carves out of secure DRAM
specifically so it can be mapped into a TA on invocation and **never**
into OP-TEE core or Linux otherwise (`CFG_SECURE_DATA_PATH=y`). Normal
world only ever holds an opaque dma-buf file descriptor; the actual pages
are inaccessible to it by construction, enforced by the memory controller,
not by an OS-level permission check root could bypass.

Reference this was written against (cited in PLAN.md):
[`optee_test/host/xtest/sdp_basic.c`][sdp] — a CA allocates a secure buffer
and invokes a TA for *inject → transform → dump*. Our CA/TA is that same
shape with `transform` replaced by AES-CTR decrypt. The exact ioctl
struct layout and libteec entry point name for wrapping a dma-buf fd as
`TEEC_SharedMemory` have shifted across OP-TEE releases — **verify
`alloc_output_buffer()` against whatever `sdp_basic.c` looks like in the
manifest revision `repo sync` actually pulls**, don't trust this file
blindly.

`host/main.c --insecure-debug-dump` allocates an *ordinary* (non-SDP)
buffer instead and prints the plaintext straight to the console — the
deliberately-broken contrast mode PLAN.md asks for, clearly labeled as
exactly the mistake real SDP hardware exists to prevent.

## Known toolchain trap

`CFG_WITH_PAGER=y` together with `CFG_SECURE_DATA_PATH=y` hangs OP-TEE core
init on the `qemu_v8` platform ([optee_os#1656][bug]). `build.sh` builds
with `CFG_WITH_PAGER=n` — don't turn the pager on.

## Two-step workflow (provision, then generate vectors, then run for real)

There's no live license server involved in 6b — `gen_test_vectors.py` is a
standalone script playing the "server" role opposite the TA's "device"
role, mirroring `cdm/tee/macos_sep/device.py` but in the other direction:

1. Boot QEMU (`run.sh`), run `/drm_poc_ca` once. It provisions the TA's
   device key (idempotent — safe to run again) and writes
   `device_pubkey.bin` into `/data/drm_poc` in the guest.
2. Get that file onto the host (a rootfs overlay rebuild, or a 9p share if
   one is configured — buildroot's default images for `qemu_v8` don't ship
   with disk persistence, so plan for one of these rather than assuming a
   writable disk survives a reboot).
3. On the host: `python3 gen_test_vectors.py <dir containing
   device_pubkey.bin>`. Writes `server_ephemeral_pub.bin`,
   `wrapped_key.bin`, `encrypted_sample.bin`, `plaintext_sha256.bin` next
   to it.
4. Get those four files back into the guest's `/data/drm_poc` (rootfs
   overlay rebuild, most likely — see `build.sh`'s
   `BR2_ROOTFS_OVERLAY`-based approach in the Buildroot docs).
5. Run `/drm_poc_ca` again. This time it finds the vectors and runs the
   real unwrap → SDP-decrypt → attempted-read-from-Linux →
   hash-proof sequence, printing a `MATCH` line if everything worked.
6. Run `/drm_poc_ca --insecure-debug-dump` for the contrast.

## Estimated cost of actually building this

Per PLAN.md: budget a day or two of toolchain wrangling, ~15–20GB disk, and
several hours of `repo sync` + compile time on first run. Worth it for what
it teaches about TrustZone — but that's a deliberate, separate time
investment from this scaffolding pass.

[sdp]: https://github.com/OP-TEE/optee_test/blob/master/host/xtest/sdp_basic.c
[bug]: https://github.com/OP-TEE/optee_os/issues/1656
