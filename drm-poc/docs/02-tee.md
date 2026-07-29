# The TEE deep-dive (Phase 6)

Phases 3–5 built a real license protocol and real tier gating, but the one
thing they could never make honest was `SIMULATED_ATTESTATION_SECRET`: a
hardcoded string that anyone reading `server/crypto.py` could send to get
graded "TEE." Phase 6 is about what it actually takes to make that claim
real, and — the part general write-ups skip — what a TEE buys you even once
you've solved that, and what it still doesn't.

## What a TEE actually is

A TEE is a second execution environment on the same SoC, isolated from the
main OS ("REE", rich execution environment) in silicon, not by an OS
permission bit. Usually the *same* CPU cores, time-sliced between two
worlds, with the memory controller and bus fabric refusing normal-world
access to secure-world memory. That's the property that survives root:
having root in the REE doesn't imply access to the TEE, because the REE's
own kernel has no path to secure-world memory to escalate into.

Three implementations that matter here, in decreasing order of relevance to
this repo:

- **Apple Secure Enclave (SEP)** — a genuinely separate coprocessor with its
  own boot ROM and AES engine, talking to the main CPU over a mailbox
  interface. Holds keys the main CPU can use but never read out. **This
  machine has one**, and Phase 6a uses it for real.
- **ARM TrustZone** — the one that actually matters for commercial
  streaming. An `NS` (non-secure) bit propagated through the bus fabric,
  a TZASC partitioning DRAM, a secure monitor mediating `SMC` world
  switches. This is what Widevine L1 runs under (OP-TEE, QSEE, Kinibi, or a
  vendor TEE) on real Android/STB/TV silicon. Phase 6b targets this, via
  OP-TEE on QEMU's software-emulated `qemu_v8` platform.
- **Intel SGX / AMD SEV / ARM CCA** — server-side confidential computing.
  Real, but not the streaming story; not built here.

## The three Widevine security levels, precisely

| Level | Crypto | Decode | Frame buffers | Typical cap |
|---|---|---|---|---|
| **L1** | in TEE | in TEE (secure video path) | protected memory, never REE-visible | 4K/HDR |
| **L2** | in TEE | in REE | REE-visible | rare in practice |
| **L3** | in REE (software whitebox) | in REE | REE-visible | 480p–1080p |

The line that matters isn't "the key is hidden" — a software whitebox
(L3) also tries to hide the key, badly. It's that **L1's decrypted frames
never exist in memory the OS can read.** The TEE decrypts into a protected
buffer, the video decoder reads that buffer over a secure DMA path, and the
display controller composites straight from protected memory with HDCP
applied on the wire. The REE can't screenshot it because there is no REE
memory address that ever held it.

Phase 6a lands squarely in the **L2 shape**: real hardware-backed key
operations (crypto in TEE), but decode — and, in our case, even the final
AES-CTR sample decrypt — happens in an ordinary process's address space.
Phase 6b's design (untested, see below) is aimed at the L1 shape: the
decrypt itself happens inside secure-world code, into a buffer the REE
cannot read.

## How Netflix uses it, end to end

1. The device manufacturer provisions a device-unique keypair **into the
   TEE at the factory**, signed by the DRM vendor's root. It never leaves.
   This is the actual root of trust — everything past this point is
   downstream of "a key exists that only this piece of silicon can use."
2. The client authenticates (Netflix's MSL layer) and requests a license.
3. The license server validates the device certificate. Because that
   certificate chains to the vendor's factory root, **only a genuine
   provisioned TEE holds a key that produces a valid chain** — the client
   cannot lie about being L1, because lying would require forging a
   signature under a private key it doesn't have.
4. The license server returns content keys wrapped to the TEE's key, plus
   policy (HDCP level required, output restrictions, expiry).
5. The TEE unwraps, enforces the output rules, and decrypts into protected
   buffers.
6. Compromised device models get revoked at the license-server layer — the
   reason DRM vendors care so much about per-device (not per-model) keys.

Step 3 is exactly the thing Phase 6a set out to build for our own protocol,
and exactly where it hit a real wall on macOS. That's the next section.

## 6a — Secure Enclave: what got built, and the attestation wall

`cdm/tee/macos_sep/` is a small Swift CLI (`sep-helper`, built with
CryptoKit's `SecureEnclave` namespace) that the standalone Python driver
`device.py` shells out to for every private-key operation: generating and
signing with a persistent SE P-256 identity key, and running fresh
per-session ECDH against the server's ephemeral public key. Verified for
real on this machine (see "What's proven" below) — this is not a
simulation.

### The investigation: is real Apple-rooted attestation available here?

`docs/01-protocol.md`'s original plan for this section was: "the server
verifies it against Apple's device attestation root." Before writing that
verification code, we went looking for the API that would produce such an
attestation from a plain macOS command-line tool. What we found:

- `SecKeyCreateAttestation` — the Security framework function that, on
  iOS, produces exactly this kind of SEP-rooted attestation — **has no
  public header anywhere in the macOS SDK**, checked across SDK versions
  11 through 26. The symbol (`_SecKeyCreateAttestation`) is present in
  `Security.framework`'s binary (visible in its `.tbd` file), but nothing
  in a shipped header declares it for macOS targets. It's consumed
  internally by other Apple frameworks/daemons, not exposed for third-party
  use.
- Apple's public, documented attestation API — `DCAppAttestService`
  (DeviceCheck framework, App Attest) — states directly in its own header
  documentation: *"If you read `supported` from an app running on a Mac
  device, the value is `false`. This includes Mac Catalyst apps, and iOS or
  iPadOS apps running on Apple silicon."* This is unconditional; it doesn't
  depend on entitlements or provisioning profiles we're missing. App
  Attest, Apple's actual answer to "prove this key lives in a genuine SEP
  to a third party," simply isn't offered on any Mac target.

**Conclusion: there is no supported, public path to a real, third-party-
verifiable device attestation from a macOS CLI tool**, as of this
investigation. This is a genuine, useful finding — it's exactly the kind of
gap real DRM vendors solve by controlling both ends: a manufacturer-
provisioned root key burned in at the factory (which Apple does have and
use for its *own* purposes, e.g. FairPlay, App Attest on iOS), and a
verification service *they* run. We have neither end of that chain for a
generic CLI binary.

### What we built instead: proof-of-possession, honestly labeled

`server/attestation.py` verifies a **proof-of-possession claim**: a fresh
signature, made by the Secure Enclave private key itself, over a
timestamped payload (`{"claim": "macos_sep_v1", "timestamp": ...}`,
`verify_pop_claim`). This is real: only that specific SE key could have
produced that signature, and the timestamp check (60-second skew) means a
captured claim can't be replayed indefinitely. `server/license.py`'s
`handle_provision` routes it to `attestation_kind: "real_sep_pop"` on
success, distinct from the legacy `"simulated"` path — both are visible in
every `/provision` response so nothing is quietly conflated.

**What this does not prove**: that the key actually lives in a genuine SEP.
A modified or fake `sep-helper` binary running on ordinary REE memory could
self-sign the identical claim using a plain software key — nothing in the
wire protocol can tell the difference, because that's exactly the
attestation gap above. What *is* independently, mechanically true — for the
actual `cdm/tee/macos_sep` binary, on this actual machine — is that the
real identity key cannot be exported. That's demonstrated separately,
locally, not provable over the wire:

### What's proven, concretely

All of the following were run against this machine's real hardware while
building 6a (not asserted from documentation):

- **Real signing**: `sep-helper sign` produces genuine ECDSA-P256-SHA256
  signatures; verified byte-for-byte against `server/crypto.py`'s
  `verify_signature` using the `cryptography` library.
- **Real ECDH**: `sep-helper ecdh-session` produces a shared secret that
  matches, byte-for-byte, an independent ECDH computation done in Python
  against the same peer key — proving the SEP is doing genuine P-256 ECDH,
  not some internal shortcut.
- **Real proof-of-possession end to end**: `device.py` provisions against a
  running server, gets `attestation_kind: "real_sep_pop"` and
  `security_level: "TEE"` (all 5 KIDs including UHD), and a deliberately
  stale claim is correctly rejected and downgraded to `SW`.
- **Real content decryption**: `decrypt_segment.py` takes the content key
  granted through that flow and AES-CTR-decrypts the first sample of a real
  packaged FHD segment. Confirmed via a full `ffmpeg` decode with zero
  decoder warnings — see the note below on how the first version of this
  check was a false positive.
- **Real non-extractability**: `prove_nonextractable.sh` shows the on-disk
  representation of the identity key (`SecureEnclave...dataRepresentation`,
  written to `.identities/<label>.sepkey`) is a 324-byte opaque blob — not a
  32-byte P-256 scalar, doesn't parse as any standard private-key encoding
  (DER/PEM), and no 32-byte window anywhere in it reproduces the real
  public key. The private key that signed every request in this demo
  cannot be reconstructed from anything on this disk.

**A false positive worth documenting**: the first version of
`decrypt_segment.py`'s correctness check used `ffprobe -show_entries
frame=pict_type` and reported success even when decrypting under a
*wrong* key. The reason: CENC's subsample map leaves roughly the first 700
bytes of the slice NAL — including the slice header, which is where
`pict_type` is read from — in the clear on purpose (so the container stays
parseable), while only the slice *data* past that point is encrypted. A
wrong key produces a well-formed (unencrypted) header and garbage
(encrypted) residuals; `ffprobe`'s lightweight parser never noticed the
garbage. Caught by literally decrypting the same sample under a wrong key
and seeing the same "confirmed" result. The fix — a full `ffmpeg` decode,
checked for zero stderr warnings — reliably distinguishes correct
decryption (clean decode) from wrong keys (`error while decoding MB`,
`corrupt decoded frame` every time). Left as a comment in
`decrypt_segment.py` because it's a real instance of PLAN.md's "headers
stay in the clear" fact from `docs/00-primer.md` almost producing a false
"it works" result.

**Non-extractability real, remote attestation not** is the accurate
one-line summary of 6a, and it's exactly PLAN.md's own predicted honesty
boundary for this track (Part 4, "What this proves... what it doesn't"),
just with the attestation half turning out even more constrained than
expected once actually investigated.

## 6b — OP-TEE on QEMU + Secure Data Path: design, untested

`cdm/tee/optee/` is a from-scratch Trusted Application, Client Application,
and build scaffolding targeting OP-TEE's `qemu_v8` reference platform with
`CFG_SECURE_DATA_PATH=y`. **It has not been built or run** — see
`cdm/tee/optee/README.md`'s Status line and the rest of this section for
why, and what running it would actually prove.

### Why untested

OP-TEE's build system targets Linux hosts (via `repo`, cross-toolchains it
fetches itself, and a from-scratch Buildroot Linux image) — it doesn't run
on macOS. A real build needs a Linux environment (Docker, in this case),
roughly 15–20GB of disk, and a multi-hour first `repo sync` + compile.
PLAN.md itself budgets "a day or two of toolchain wrangling" for this
track. Given that cost, this pass writes the complete design — Dockerfile,
build/run scripts, TA, CA, SDP wiring, offline test-vector generator — so
it's ready to build, rather than spending that multi-hour, multi-day budget
inside this session.

### What it's designed to prove

The property Phase 6a can't reach: decryption happening *inside*
secure-world code, writing plaintext into a buffer that is physically
unreadable from normal-world Linux — not logically restricted, physically
so, via OP-TEE's Secure Data Path feature. The TA (`ta/drm_poc_ta.c`)
implements three commands — `PROVISION_KEY` (persistent device ECDH
keypair, GP secure storage), `UNWRAP_AND_DECRYPT` (ECDH-derive → unwrap a
content key → AES-CTR-decrypt a sample directly into an SDP-backed output
buffer), `HASH_PROOF` (SHA-256 of that buffer, never the buffer itself) —
against the real GlobalPlatform TEE Internal Core API OP-TEE implements.
The CA (`host/main.c`) drives those three commands, then — this is the
actual point of the demo — **tries to read the SDP output buffer itself**
and shows that fails or returns zeros, following the negative-test framing
PLAN.md insists on (`qemu_v8` has no VPU or protected display, so there's
no way to show decrypted *pixels*; showing that normal-world Linux
provably cannot read the buffer is the demonstrable substitute).

A `--insecure-debug-dump` CA mode allocates an ordinary (non-SDP) buffer
instead, for the deliberately-broken contrast PLAN.md asks for — labeled
plainly as exactly the mistake real SDP hardware exists to prevent.

### Known toolchain trap, already found by others

`CFG_WITH_PAGER=y` together with `CFG_SECURE_DATA_PATH=y` hangs OP-TEE core
init on `qemu_v8` ([optee_os#1656][bug]). `build.sh` is written with
`CFG_WITH_PAGER=n` from the start.

### Simplification, stated plainly

The TA's session-key derivation is `HMAC-SHA256(ecdh_shared_secret,
"drm-poc-sdp-v1")`, not the real HKDF from `docs/01-protocol.md` with its
per-request nonce salt. 6b exists to prove the SDP mechanism works, not to
be a byte-exact reimplementation of the Phase 3 protocol inside secure
world — wiring the real protocol in is future work once the build itself
is verified.

[bug]: https://github.com/OP-TEE/optee_os/issues/1656

## 6d — Honest limits

None of the above makes copying impossible; it raises the cost of copying,
which is the actual economic function of DRM. Specifically, even a real L1
implementation does not:

- **Stop screen capture on an open platform.** Anything that can put pixels
  on a general-purpose OS's screen can, in principle, be captured by
  something else running as the same user, unless the entire display path
  (including the capture APIs themselves) is locked down — which is why
  desktop Chrome's Widevine is capped well below what a locked-down set-top
  box or TV reaches, and why even L1 mobile playback sometimes shows a
  black rectangle to a second app's screen-recording API rather than
  relying on the TEE alone.
- **Stop the analog hole.** A camera pointed at a screen, or a microphone
  next to a speaker, defeats any digital protection scheme by construction
  — this is a physics problem, not a cryptography one, and no TEE claims to
  solve it.
- **Stop TrustZone or SEP itself from being broken.** Both have been:
  published TrustZone kernel exploits and Secure Enclave Processor research
  exist, and PLAN.md's own cited case study —
  [sigma-star, June 2026][sigma-star], carried forward into
  `docs/03-attacks.md`'s Phase 7 literature review — describes a DDR
  memory-aliasing bug on real i.MX 8M silicon that let normal-world Linux
  read OP-TEE's secure memory directly, on hardware with a real, shipped
  Secure Video Path. That is directly relevant to anyone who takes on
  PLAN.md's optional 6c (a real i.MX8M board) after this: the theoretical
  isolation this whole document describes is only as good as the specific
  chip's actual implementation of it, and that implementation has had real
  bugs.

DRM is economics, not mathematics. Everything in Phase 6 raises the cost of
extracting a key or a frame; nothing in it, including real L1 hardware,
makes that extraction mathematically impossible.

[sigma-star]: https://sigma-star.at/blog/2026/06/trustzone-intermezzo/
