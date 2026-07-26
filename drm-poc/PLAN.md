# DRM PoC — building a Netflix-shaped DRM stack from scratch

## Goal

Understand, by building it, how a commercial streaming DRM system actually works: how
content is encrypted once and delivered to many devices, how keys travel from a license
server to a client without ever being exposed, how playback policy is enforced by
cryptography rather than by client-side checks, and — the part most write-ups skip —
what a Trusted Execution Environment actually buys you and why Netflix gates 4K behind it.

The end state is a working system: a browser plays an encrypted video only after our own
license server authorises it, and a hardware-backed key on this machine participates in
that authorisation.

## Non-goals

- Shipping anything production-grade. No key ceremony, no HSM, no CA hierarchy.
- Obtaining a real Widevine licence from Google. Not available to individuals, and not
  needed — we implement the *shape* of the protocol, not the proprietary wire format.
- Breaking or circumventing real Widevine/PlayReady/FairPlay. The attack phase targets
  only the soft CDM **we** write. Real-CDM attacks get a literature review, not code.

---

## Part 1 — The mental model

Before writing code, get the component map straight. Netflix's stack decomposes into six
roles, and our PoC will have one of each.

| Role | What it does | Netflix's version | Ours |
|---|---|---|---|
| Encoder | Produces multi-bitrate renditions | Proprietary VMAF-driven per-title encoding | `ffmpeg` ladder |
| Packager | Encrypts + segments into DASH/HLS | In-house | `shaka-packager` (CENC) |
| Key server | Mints & stores content keys, maps to content IDs | In-house | FastAPI + SQLite |
| License server | Authenticates device, applies policy, wraps keys | Widevine/PlayReady/FairPlay license servers behind Netflix's own MSL layer | FastAPI, our protocol |
| CDM | Client-side secret keeper; decrypts | Widevine L1/L3, PlayReady SL3000, FairPlay | Our soft CDM + ClearKey, then a TEE-backed one |
| Player | Fetches manifest, drives EME | Netflix's player | `shaka-player` in Chrome |

Three facts that shape everything downstream:

1. **Content is encrypted once, licensed many times.** CENC (ISO/IEC 23001-7) standardises
   the encryption *in the file* so a single packaged asset serves Widevine, PlayReady and
   FairPlay clients. Only the license acquisition differs per DRM. This is why the `pssh`
   box exists — a per-DRM blob riding inside a DRM-agnostic container.
2. **The client is assumed hostile.** Every security property must survive the user owning
   root on the device. This is the constraint that forces both the crypto design and the
   TEE.
3. **Policy is enforced by key availability, not by asking nicely.** "Rental expired"
   means the server stops issuing a key, or issues one with a TEE-enforced lifetime — not
   an `if (expired) return` in the player.

**Netflix-specific detail worth building in:** Netflix wraps DRM license traffic in its own
open-source **MSL (Message Security Layer)** protocol — entity authentication, master
tokens, user ID tokens, key exchange. It's the layer above the DRM license exchange, and
it's public (`github.com/Netflix/msl`). Our Phase 4 protocol borrows its token structure,
which is what makes this a *Netflix*-shaped PoC rather than a generic one.

---

## Part 2 — Target architecture

```
                    ┌──────────────────────────────────────┐
                    │  packaging/  (offline, one-shot)     │
                    │  ffmpeg ladder → shaka-packager      │
                    │  → CENC-encrypted CMAF + DASH/HLS    │
                    └──────────────┬───────────────────────┘
                                   │ content keys (KID → key)
                                   ▼
┌─────────────┐        ┌───────────────────────────────────┐
│  player/    │        │  server/  (FastAPI)               │
│  Chrome     │        │   /provision   device onboarding  │
│  shaka-     │◄──────►│   /license     the interesting one│
│  player     │  HTTPS │   /manifest    DASH/HLS + pssh    │
│  + EME      │        │   keys.db  policies.db  devices.db│
└──────┬──────┘        └───────────────────────────────────┘
       │ decrypt request
       ▼
┌──────────────────────────────┐
│  cdm/  our Content Decryption│
│  Module                      │
│  ├─ soft/  pure Python       │  ← Phase 3, attackable on purpose
│  └─ tee/   Secure Enclave or │  ← Phase 6, keys never in our address space
│            OP-TEE TA         │
└──────────────────────────────┘
```

### Repo layout

```
drm-poc/
├── PLAN.md                  ← this file
├── README.md                ← how to run it, once it runs
├── requirements.txt         ← synced to repo root per CLAUDE.md
├── venv/                    ← gitignored
├── docs/
│   ├── 00-primer.md         ← CENC, EME, pssh, the DRM triad
│   ├── 01-protocol.md       ← our license protocol spec, written before the code
│   ├── 02-tee.md            ← the TEE deep-dive (Part 4 below)
│   └── 03-attacks.md        ← what we broke and what that proves
├── packaging/
│   ├── encode.sh            ← ffmpeg ladder
│   ├── package.sh           ← shaka-packager, multi-key
│   └── content/             ← gitignored, big binaries
├── server/
│   ├── main.py              ← FastAPI app
│   ├── license.py           ← license request/response handling
│   ├── policy.py            ← expiry, device binding, security-level gating
│   ├── crypto.py            ← RSA/ECDH wrap, AES-CTR, signing
│   └── models.py            ← device, key, policy records
├── cdm/
│   ├── soft/                ← software CDM (deliberately breakable)
│   └── tee/                 ← hardware-backed CDM
│       ├── macos_sep/       ← Swift helper: Secure Enclave P-256
│       └── optee/           ← optional: OP-TEE Trusted Application
├── player/
│   ├── index.html
│   └── cdm-bridge.js        ← EME glue; ClearKey path + custom path
└── tools/
    ├── inspect_mp4.py       ← dump pssh, senc, saio/saiz boxes
    └── extract_keys.py      ← the attack script (Phase 7)
```

---

## Part 3 — Build phases

Each phase ends with something demonstrable. Don't start the next until the current one
runs.

### Phase 0 — Primer + environment (½ day)

Read and write up, in `docs/00-primer.md`, in your own words:
- CENC: `cenc` (AES-128-CTR, full-sample) vs `cbcs` (AES-128-CBC, 1:9 pattern encryption).
  Why Apple forced `cbcs` into existence and why CMAF+`cbcs` is now the convergence point.
- The `pssh` box, `tenc` (track encryption), `senc`/`saiz`/`saio` (per-sample IVs and
  subsample maps). Note that *headers stay in the clear* — only media payloads are
  encrypted, which is why an encrypted MP4 still parses.
- EME's state machine: `requestMediaKeySystemAccess` → `MediaKeys` → `MediaKeySession` →
  `encrypted` event → `generateRequest` → license → `update`.

Set up: `venv`, `ffmpeg`, `shaka-packager`, Chrome, a test clip (Blender open movies).

**Done when:** you can articulate why a single packaged asset can serve three DRMs.

### Phase 1 — Encrypt and package (½ day)

Encode a ladder (240p/480p/1080p, plus a fake "4K" tier if the source allows), then
package with `shaka-packager` under CENC with **distinct keys per quality tier** — this is
the multi-key requirement, and it's what makes Phase 5's tier gating possible at all.

Write `tools/inspect_mp4.py` to dump the `pssh`, `tenc` and `senc` boxes. Seeing the
per-sample IVs and subsample offsets yourself is worth more than reading the spec.

**Done when:** `ffplay` on the packaged segments produces garbage, `inspect_mp4.py` shows
four distinct KIDs, and the DASH manifest lists `ContentProtection` elements.

### Phase 2 — ClearKey playback (½ day)

Wire `shaka-player` in Chrome against `org.w3.clearkey`, serving keys from a trivial
FastAPI endpoint that hands back the raw JWK. No security whatsoever — the point is to
close the EME loop and prove the packaging is correct.

**Done when:** video plays in Chrome, and deleting the key endpoint makes it stop.

**This is win condition #1 (encrypted playback works).**

### Phase 3 — A real license protocol (2–3 days) ← *the core of the PoC*

Now replace ClearKey with something Widevine-shaped. Write the spec in
`docs/01-protocol.md` **before** the code.

Provisioning (`/provision`, once per device):
- Device generates a keypair. Server issues a **device certificate** signed by our root —
  binding the public key to a device ID and a claimed **security level** (`SW`, `TEE`).
- The security level is a *server-asserted* claim, not a client-asserted one. Getting this
  right is the whole ballgame; note in the spec exactly why a client-claimed level is
  worthless.

License exchange (`/license`, per playback session):
1. Client sends a license request: content ID, the KIDs from the `pssh`, a client nonce,
   its device cert, signed with the device key.
2. Server verifies the signature and cert chain, checks the device isn't revoked.
3. Server derives a **session key** — either RSA-OAEP wrapped to the device public key, or
   ECDH against it. (ECDH is required later for the Secure Enclave, which won't do RSA, so
   prefer ECDH + HKDF from the start.)
4. Server evaluates policy (Phase 4) and selects *which subset of KIDs* this device may
   receive (Phase 5).
5. Server returns content keys encrypted under the session key, plus a policy block, the
   whole response MAC'd with a key derived alongside the session key.
6. Client unwraps, feeds keys to the CDM, playback begins.

Adopt MSL's token idea: the provisioning step returns a **master token** (server-encrypted,
opaque to the client, carrying identity + expiry) that the client replays on each license
request instead of re-doing asymmetric crypto every time.

**Done when:** playback works through your own protocol; tampering with any field of the
license request causes a clean server-side rejection; the license response is unusable if
captured and replayed on a different device.

### Phase 4 — Policy enforcement (1 day)

Implement in `policy.py`, and prove each one by making playback stop:
- **License expiry** — short-lived keys, renewal round-trip mid-playback.
- **Rental window** — first-play timestamp starts a 48h clock.
- **Device binding** — a license minted for device A is rejected/undecryptable on B.
- **Revocation** — flip a device to revoked, watch playback die at the next renewal.
- **Concurrent stream limit** — the Netflix-flavoured one: N sessions per account.

**Done when:** each policy is demonstrated by a failing playback, not by a log line. **Win
condition #2.**

### Phase 5 — Multi-key tier gating (½ day)

The 4K-requires-L1 rule, reproduced. A device provisioned as `SW` receives only the
SD/HD KIDs; a device provisioned as `TEE` receives all of them, including the 4K key.
`shaka-player` will transparently cap the ABR ladder at the tiers it can decrypt.

Document the real-world mapping: Widevine L1 + HEVC + HDCP 2.2 for Netflix 4K; L3 clients
capped at 720p/1080p depending on platform.

**Done when:** the same content, same player, two devices — one tops out at 1080p, the
other reaches 4K, with no client-side logic involved. **Win condition #3.**

### Phase 6 — TEE (2–4 days) ← *see Part 4 for the detail*

**Done when:** a content key is used to decrypt video without that key ever existing in
the player process's address space, and you can prove it with a memory dump. **Win
condition #4.**

### Phase 7 — Attack demo (1 day)

Attack **our own** soft CDM from Phase 3, then contrast with the Phase 6 TEE CDM:
1. Attach `lldb`/`gdb` to the player process, dump the heap, grep for the content key. It's
   there. Write `tools/extract_keys.py` to automate it.
2. Hook the CDM's decrypt entry point; dump plaintext frames.
3. Re-run both against the TEE-backed CDM. The key isn't in memory. The best you get is
   the *decrypted output*, which is exactly the residual attack surface real systems have —
   and the reason secure video paths and HDCP exist above the TEE.
4. Screen-capture the playing video to show what the TEE does *not* protect on a
   general-purpose OS.

Then a **literature review** (no code) in `docs/03-attacks.md`: how the published Widevine
L3 attacks worked (whitebox key extraction from the CDM binary), why they didn't
generalise to L1, and what Google changed in response. Cite; don't reimplement.

**Done when:** you have a side-by-side artefact showing the same attack succeeding against
software and failing against hardware. **Win condition #5.**

---

## Part 4 — The TEE track (deep dive)

This is what you asked to understand, so it gets its own design rather than a bullet.

### What a TEE actually is

A TEE is a second execution environment on the same SoC with hardware-enforced isolation
from the main OS ("REE", rich execution environment). Not a separate chip necessarily —
the *same* CPU cores time-slicing between two worlds, with the memory controller and bus
fabric refusing normal-world access to secure-world memory. The isolation is in silicon,
so root in the REE does not imply access to the TEE.

The concrete implementations:
- **ARM TrustZone** — the one that matters for streaming. An `NS` (non-secure) bit
  propagated through the bus fabric; the TZASC partitions DRAM; a secure monitor mediates
  world switches via `SMC`. Android phones, set-top boxes, smart TVs. This is what Widevine
  L1 runs in, typically under OP-TEE, QSEE (Qualcomm), Trustonic Kinibi, or a vendor TEE.
- **Apple Secure Enclave (SEP)** — a genuinely separate coprocessor with its own boot ROM,
  own AES engine, and a mailbox interface to the AP. Holds keys that the main CPU can use
  but never read. FairPlay's roots are here. **You have one in this machine.**
- **Intel SGX / AMD SEV / ARM CCA** — server-side confidential computing. Adjacent, mostly
  not the streaming story.

### The three Widevine security levels, precisely

| Level | Crypto | Decode | Frame buffers | Netflix cap |
|---|---|---|---|---|
| **L1** | in TEE | in TEE (secure video path) | protected memory, never REE-visible | 4K/HDR |
| **L2** | in TEE | in REE | REE-visible | rare in practice |
| **L3** | in REE (software whitebox) | in REE | REE-visible | 480p–1080p |

The critical L1 property is not just "the key is hidden" — it's that **decrypted frames
never exist in memory the OS can read**. The TEE decrypts into a protected buffer, the
video decoder reads that buffer through a secure DMA path, and the composited output goes
to the display controller with HDCP applied on the wire. At no point can the REE screenshot
it — which is why Netflix in Chrome (L3) shows you a black rectangle on screen capture on
some platforms, and why Netflix in a browser is capped at 720p/1080p while the same account
on an Android TV hits 4K.

### How Netflix uses it, end to end

1. Device manufacturer provisions a **device-unique key pair into the TEE at the factory**,
   signed by the DRM vendor's root. It never leaves. This is the root of trust — everything
   else is downstream of "a key exists that only this piece of silicon can use".
2. Netflix's client authenticates to Netflix (MSL) and requests a license.
3. The Widevine license server validates the device certificate → this tells it the
   **security level** cryptographically, since only a genuine provisioned TEE holds a key
   chaining to the vendor root. The client cannot lie about being L1.
4. The license server returns content keys **wrapped to the TEE's key**, plus policy
   (HDCP level required, output restrictions, expiry).
5. The TEE unwraps, enforces the output rules (refuses to decrypt if HDCP 2.2 isn't
   negotiated on the HDMI link), and decrypts into protected buffers.
6. Compromised device models get **revoked** at the license-server layer — the reason DRM
   vendors care so much about per-device keys.

### What we build

**6a — Real hardware, this machine (Secure Enclave).** Generate a P-256 key with
`kSecAttrTokenIDSecureEnclave` — non-extractable by construction, enforced by the SEP, not
by the keychain ACL. Use it as our device key from Phase 3: the SEP performs the ECDH
against the server's ephemeral public key, HKDF derives the session key, and we unwrap the
content key. Requires a small **Swift helper CLI** that the Python CDM shells out to
(pyobjc against the Security framework is possible but painful; a 100-line Swift binary is
cleaner). Gate it behind `SecAccessControl` with biometry to also demo user-presence
binding.

*What this proves:* the device private key genuinely cannot be extracted, even with root.
*What it doesn't:* the derived session key and content key still land in Python's heap —
the SEP is a key store with compute, not a full TEE that can run our decryptor. Be honest
about this boundary in the write-up; it's exactly the L2-vs-L1 distinction.

**6b — Optional, the real thing (OP-TEE on QEMU).** To close that gap, build OP-TEE for
QEMU ARMv8 and write a **Trusted Application** that: holds the device key, unwraps the
content key, and performs the AES-CTR sample decryption *inside* the secure world,
returning only plaintext samples. The REE-side Python CDM talks to it via the OP-TEE client
library. This is structurally what Widevine L1 does, minus the secure video path (QEMU has
no protected display).

Heavier — a day or two of toolchain wrangling — but it's the difference between reading
about TrustZone and having run code in it. Recommend attempting it; drop it without guilt
if the toolchain fights back, since 6a already carries most of the teaching value.

**6c — The write-up** (`docs/02-tee.md`): the above, plus the honest limits — TEEs don't
stop screen capture on open platforms, don't stop analog-hole recording, and have
themselves been broken (TrustZone kernel exploits, SEP research). DRM is economics, not
mathematics: it raises cost, it doesn't make copying impossible.

---

## Part 5 — Risks and open questions

- **`shaka-packager` availability on Apple Silicon** — may need a build from source or
  Docker. Check in Phase 0; `Bento4` is the fallback packager.
- **Secure Enclave is ECDH/ECDSA-only, P-256, no RSA.** Design the Phase 3 protocol around
  ECDH from day one or you'll rewrite it in Phase 6.
- **Chrome and ClearKey** requires HTTPS or `localhost`. Serve over `localhost` throughout.
- **A custom CDM can't be plugged into a browser.** EME only talks to real, signed CDMs.
  So Phases 3–7 run our protocol with the *browser as transport and player*, decrypting via
  ClearKey with keys our protocol delivered — or, for the TEE phases, via a standalone
  Python player (PyAV) outside the browser. Decide which in Phase 3 and note the
  compromise: the security boundary we're modelling is real, but the browser's own CDM
  boundary is not one we can substitute into.
- **Legal footing** — everything here operates on content we own or that is openly
  licensed, against a license server we wrote. The one thing to keep out of scope is
  touching a real commercial CDM or real Netflix traffic.

## Estimated total

8–12 focused days, of which Phase 3 and Phase 6 are ~60%. Phases 0–2 are plumbing and
should move fast; resist gold-plating them.

## Suggested first move

Phase 0 + Phase 1 in one sitting — get a CENC-encrypted asset on disk and dump its boxes.
Everything after that is easier to reason about with a real encrypted file in front of you.
