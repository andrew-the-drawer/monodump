# Primer — CENC, boxes, EME

## CENC: `cenc` vs `cbcs`

ISO/IEC 23001-7 (Common Encryption) defines how to encrypt media samples inside an ISO
BMFF (MP4) container in a way that is independent of which DRM system licenses the key.
Two encryption schemes matter in practice:

- **`cenc`** — AES-128-**CTR**, full-sample encryption. Every byte of every sample is
  encrypted. This is the original scheme (Microsoft/PlayReady lineage) and what Widevine
  on Android/Chrome OS has always used.
- **`cbcs`** — AES-128-**CBC**, with **pattern encryption**: a repeating 1-encrypted /
  9-clear 16-byte-block pattern (`1:9`) applied to each sample after the first partial
  block. Apple required CBC mode for FairPlay (its hardware crypto engines were CBC-native,
  not CTR-native), and pattern encryption was added so the scheme would still be cheap to
  decrypt on constrained silicon — only 10% of blocks need the AES operation instead of
  100%.

Why this converged: once both `cenc` and `cbcs` could be expressed as CENC encryption
*schemes* inside the same box structure, packagers could produce **one CMAF file** whose
`schm` box just says which scheme applies, and FairPlay, PlayReady and Widevine could each
license their own keys against the *same* encrypted bytes. CMAF + `cbcs` become the de
facto convergence point industry-wide because `cbcs` is a superset in practice — the CBC
pattern scheme every client is required to support, while `cenc`/CTR is optional in newer
common-encryption-capable clients. We use `cenc` (CTR) in this PoC because it is the
simpler mental model (whole-sample encryption) and both `shaka-packager` and ClearKey
support it without extra pattern-decryption bookkeeping.

## The boxes

An encrypted MP4 is a normal ISO BMFF file where a `senc`-based box graph replaces the
plain sample data with the same bytes, encrypted, plus a few extra boxes describing how to
decrypt them. Crucially, **only the media payload (`mdat`) is touched** — every structural
box (`moov`, `trak`, `mvhd`, etc.) is untouched cleartext. This is *why an encrypted MP4
still parses*: any MP4 demuxer can read the timeline, codec parameters and track layout; it
just can't produce meaningful pixels from the samples without the key.

- **`pssh`** (Protection System Specific Header) — a per-DRM opaque blob, keyed by a
  `SystemID` UUID (one UUID means "this blob is for Widevine", another for PlayReady,
  another for FairPlay). A single packaged file can carry multiple `pssh` boxes, one per
  DRM, each pointing a different license server at the same underlying content keys. This
  is the literal embodiment of "encrypt once, license many times" — the `pssh` payload
  usually contains at minimum the key ID(s) so the client knows which key to ask for.
- **`tenc`** (Track Encryption Box, inside `moov > trak > mdia > minf > stbl > stsd >
  ...> sinf`) — declares, per track, the default: which scheme (`cenc`/`cbcs`), the
  default KID, IV size, and (for `cbcs`) the default pattern.
- **`senc`** (Sample Encryption Box) — per-sample encryption metadata: for every sample in
  a fragment, its IV (or a compact per-fragment IV + counter derivation) and, if
  subsample encryption is used, the list of (clear, encrypted) byte-range pairs within
  that sample (needed because NAL unit headers within an H.264 sample are sometimes left
  clear even under full-sample schemes, for parsing robustness).
- **`saiz`/`saio`** (Sample Auxiliary Information Size/Offset) — index boxes so a reader
  can jump straight to the auxiliary (IV/subsample) info for a given sample without
  scanning `senc` linearly; in fragmented MP4 these live in the fragment's `traf`.

Net effect: decryption metadata (which key, which IV per sample, which byte ranges) rides
alongside the content in-band, in clear boxes, so a demuxer + KID → key mapping is all a
CDM needs to decrypt — it never needs out-of-band signalling beyond "here is the key for
this KID."

## EME's state machine

The W3C Encrypted Media Extensions API is the browser-side glue between `<video>` and a
platform CDM:

1. `navigator.requestMediaKeySystemAccess(keySystem, configs)` — the page asks "can you
   satisfy `org.w3.clearkey` / `com.widevine.alpha` / etc. with these container/codec
   capabilities?" Resolves to a `MediaKeySystemAccess` if a CDM matching that key system is
   available and configured acceptably (robustness, codecs).
2. `access.createMediaKeys()` → a `MediaKeys` object, then
   `video.setMediaKeys(mediaKeys)` — binds the CDM instance to this specific video element.
3. Playback starts; the browser demuxes the encrypted MP4/CMAF, sees a `pssh`/`tenc` it
   doesn't have a key for, and fires an `encrypted` event on the video element carrying the
   `initData` (typically the `pssh` payload) and its type (`cenc`).
4. The page creates a session: `mediaKeys.createSession('temporary')` →
   `session.generateRequest(initDataType, initData)`. The CDM parses `initData`, emits a
   `message` event carrying an opaque **license request** blob (CDM-specific wire format).
5. The page ships that blob to a license server however it likes (our `/license` endpoint,
   in this PoC) and gets back a **license response** blob.
6. `session.update(licenseResponseBytes)` — hands the response back to the CDM, which
   verifies/unwraps it and stores the content key(s) internally, keyed by KID. Playback
   resumes/starts decrypting.

The key property: **the page only ever sees opaque bytes** on both sides of step 5 — a
real CDM (Widevine/FairPlay) never exposes raw keys to JavaScript. ClearKey is the
deliberate exception (its "license request/response" *is* just JSON with raw JWK keys),
which is precisely why it has no security value and is only used here to close the loop
end-to-end before Phase 3 replaces it with our own protocol.

## Why one packaged asset serves three DRMs

Put together: CENC standardizes the *ciphertext and its in-band metadata* (`tenc`/`senc`/
`saiz`/`saio`), independent of DRM. The only DRM-specific parts are (a) which `pssh` blob
is present (there can be several, side by side) and (b) how a client acquires the key for
a given KID from *that DRM's* license server. So a packager encrypts the media exactly
once, embeds one `pssh` per target DRM, and three completely different client stacks
(Widevine on Chrome/Android, PlayReady on Edge/Xbox, FairPlay on Safari/iOS) can each play
the identical encrypted bytes — they just negotiate their own license for the same
underlying keys through their own EME `encrypted` → `message` → `update` cycle.
