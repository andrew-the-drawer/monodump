# Our license protocol (Phase 3)

Written before the code, per PLAN.md. Implemented in `server/crypto.py`,
`server/license.py`, `server/models.py`, and the browser half in
`player/cdm-bridge.js` (WebCrypto SubtleCrypto — no server-side "client"
process exists; the browser tab *is* the device, and its non-extractable
SubtleCrypto keys are our Phase 3–5 stand-in CDM, deliberately attackable in
Phase 7).

## Actors

- **Device** = the browser tab. Holds two WebCrypto keypairs, both generated
  with `extractable: false` so the *page's own JavaScript* cannot read the
  private key material back out — the same non-extractability property a
  software CDM's key store relies on, minus hardware backing (that's what
  Phase 6 adds).
  - **Identity keypair** (ECDSA P-256): long-lived for the browser session,
    proves "this is the device that provisioned," never re-generated between
    a `/provision` call and subsequent `/license` calls.
  - **Ephemeral keypair** (ECDH P-256): fresh per license request, used only
    for that request's key exchange, then discarded.
- **Server** (`server/`): root CA, device registry (`devices.db`), content
  key store (`keys.db`), session/policy state (`policies.db`).

## Why ECDH, not RSA

Secure Enclave (Phase 6a) only does ECDH/ECDSA over P-256 — no RSA. Designing
the session-key exchange around ECDH from day one means Phase 6 swaps *who
holds the private key* (SEP instead of a SubtleCrypto software key) without
touching the protocol.

## Provisioning — `POST /provision` (once per device)

Request:
```json
{
  "identity_pubkey_jwk": { "...": "ECDSA P-256 public JWK" },
  "requested_security_level": "SW" | "TEE",
  "attestation": "<opaque string, required only for TEE>"
}
```

Server logic:
1. Assign `device_id` = random 16-byte hex.
2. **The security level is asserted by the server, never taken on the
   client's word.** For `SW`, no evidence is required — that's the whole
   point of `SW`: it's the "I have no proof" tier, and playback policy will
   treat it that way (Phase 5 withholds the UHD key from it).
   For `TEE`, the server accepts either of two `attestation` shapes
   (`server/attestation.py`), and reports which one fired via
   `attestation_kind` in the `/provision` response:
   - The legacy stand-in: `attestation == SIMULATED_ATTESTATION_SECRET` (a
     constant in `server/crypto.py`). **A deliberate, clearly-labeled
     placeholder** — anyone reading this file can send the exact string.
     Kept for the Phase 2–5 in-browser demo, which has no hardware backing
     to speak of.
   - Phase 6a's real path: a **proof-of-possession claim** from
     `cdm/tee/macos_sep` — a fresh signature, made by the Secure Enclave
     private key itself, over a timestamped payload. This is genuinely
     real: only that SE key could have produced it, and non-extractability
     is enforced by the SEP, not by us. **It is still not remote
     attestation.** The original plan for this section was "the server
     verifies it against Apple's device attestation root" — that turned out
     to be unavailable: `SecKeyCreateAttestation` has no public header on
     macOS, and Apple's own App Attest API documents `.supported == false`
     on every Mac target, Apple silicon included (see `docs/02-tee.md` for
     the investigation). So there is no vendor-rooted chain a compromised
     client binary couldn't also fake with a plain software key. What *is*
     real and independently true for the actual `cdm/tee/macos_sep` binary —
     the identity key really can't be exported, even by us — is
     demonstrated locally (`prove_nonextractable.sh`), not provable over the
     wire to this server.

   Treat any "TEE" device in Phases 3–5's browser demo (`attestation_kind:
   "simulated"`) as a simulation used purely to exercise the tier-gating
   *mechanism*. A Phase 6a device (`attestation_kind: "real_sep_pop"`) is
   real in the narrower sense above — do not read more security guarantee
   into either than PLAN.md's own honesty note for 6a describes.
3. Issue a **device certificate**: `{device_id, identity_pubkey_jwk,
   security_level, issued_at}` signed (ECDSA-SHA256) by the server's root CA
   key. Stored client-side for completeness/debuggability; not re-verified
   on every `/license` call (see master token, next).
4. Persist `{device_id, identity_pubkey_jwk, security_level, revoked=false}`
   to `devices.db`.
5. Issue a **master token**: `base64(iv || AES-256-GCM(server_master_key,
   plaintext={device_id, issued_at, expiry}))`. Opaque to the client. This is
   the MSL-flavoured shortcut: subsequent `/license` calls send this token
   instead of re-transmitting and re-verifying the certificate chain. The
   server decrypts it, pulls `device_id`, and **re-reads `security_level` and
   `revoked` fresh from `devices.db` every time** rather than trusting
   whatever the token or an old cert claims — this is what makes Phase 4
   revocation take effect on the very next request instead of only at the
   next provisioning.

Response:
```json
{ "device_id": "...", "device_cert": {...}, "master_token": "..." }
```

## License exchange — `POST /license` (per playback session)

Request:
```json
{
  "master_token": "...",
  "content_id": "demo",
  "kids": ["<hex>", "..."],
  "nonce": "<base64url, 16 random bytes>",
  "ephemeral_pubkey_jwk": { "...": "ECDH P-256 public JWK" },
  "signature": "<base64url ECDSA-SHA256 signature>"
}
```

`kids` is the full candidate set the client discovered from the manifest's
`pssh`/`tenc` boxes (Phase 1) — the client is asking "here's everything that
exists"; the server decides which subset it actually gets.

**Signing payload** (canonical, avoids JSON-canonicalization ambiguity —
built identically by client and server as a plain byte concatenation, not
by signing the JSON object):
```
content_id.encode() + b"|"
  + ",".join(sorted(kids)).encode() + b"|"
  + nonce_b64url.encode() + b"|"
  + ephemeral_pubkey_jwk["x"].encode() + b"." + ephemeral_pubkey_jwk["y"].encode()
```
Signed with the identity private key over this byte string.

Server processing, in order (any failure below is a clean 4xx, nothing
else):
1. Decrypt `master_token` → `{device_id, issued_at, expiry}`. Reject if it
   fails to decrypt/parse, or `now > expiry` (token itself expired — separate
   from *session* expiry below).
2. Look up `device_id` in `devices.db`. 404 if unknown. **403 if
   `revoked`** — checked live, every request.
3. Recompute the signing payload from the request fields and verify against
   the device's stored `identity_pubkey_jwk`. Reject (401) on any mismatch —
   this is what makes tampering with *any* field (content_id, kids, nonce,
   ephemeral pubkey) a clean rejection: all of them are inside the signed
   payload.
4. **Policy** (`policy.py`, Phase 4): expiry, rental window, device binding
   (implicit — the session key is bound to this device's ephemeral key by
   construction), revocation (step 2), concurrent-stream cap. Any violation
   → clean rejection with a specific reason, not a silent empty key set.
5. **Tier gating** (`policy.py`, Phase 5): intersect the requested `kids`
   with the KID set the device's `security_level` is allowed —
   `SW → {SD, HD, FHD, AUDIO}`, `TEE → {SD, HD, FHD, UHD, AUDIO}`.
6. Generate a fresh server ECDH ephemeral keypair. Compute
   `shared_secret = ECDH(server_ephemeral_priv, client_ephemeral_pub)`.
7. `HKDF-SHA256(shared_secret, salt=nonce, info=b"drm-poc-license-v1",
   length=64)` → `session_enc_key` (bytes 0:32) + `session_mac_key`
   (bytes 32:64).
8. Build `payload = {"keys": {kid: key_hex, ...allowed}, "policy": {...},
   "session_id": "..."}`. Encrypt with AES-256-GCM under `session_enc_key`
   (fresh random 12-byte IV) → `(iv, ciphertext_with_tag)`.
9. `mac = HMAC-SHA256(session_mac_key, server_ephemeral_pubkey_jwk_bytes ||
   iv || ciphertext_with_tag)`. This is a second, independent integrity check
   over the whole response beyond AES-GCM's own tag, matching PLAN.md's
   explicit call for a MAC "derived alongside the session key" — belt and
   suspenders, and it's what the client checks first before even attempting
   AEAD decryption.
10. Create a `sessions` row (`policies.db`) for renewal/rental tracking.
11. Return `{server_ephemeral_pubkey_jwk, iv, ciphertext, mac}`.

Client processing:
1. Recompute `shared_secret` via its ephemeral private key (non-extractable,
   never leaves SubtleCrypto) + server's ephemeral public key.
2. Re-derive `session_enc_key`/`session_mac_key` via the same HKDF call.
3. Recompute and compare the MAC. Mismatch → discard the response, surface
   an error, do not attempt decryption.
4. AES-GCM-decrypt → `{keys, policy, session_id}`.
5. Feed `keys` into `shaka.Player.configure({drm: {clearKeys: keys}})` and
   load. ClearKey (the browser's built-in, standards-only decryptor) does
   the actual EME `generateRequest`/`update` dance internally — our protocol
   only ever decided *which* keys the player is allowed to have; ClearKey
   never talks to our `/license` endpoint at all in this mode; Phase 2's
   `/clearkey-license` route only exists for the ClearKey-native demo it was
   built for; unrelated to this endpoint.

## Why replay-on-a-different-device fails

The response is encrypted under a key derived from `ECDH(server_ephemeral,
client_ephemeral)`. A captured response, replayed verbatim to device B,
requires device B to independently derive the same `session_enc_key` — which
requires *device A's* ephemeral private key. Device B doesn't have it (it's
non-extractable and was never transmitted). So the ciphertext is
undecryptable noise to anyone but the device that generated the matching
ephemeral keypair for that specific request. No extra "device binding" logic
needed — it falls out of the key exchange.

## What's deliberately not implemented

- Full per-request certificate-chain transmission/verification (PLAN.md's
  literal step 1–2 wording). The master token supersedes it — re-verifying a
  self-signed 4-line chain on every request adds cost with no extra
  guarantee once the token already binds `device_id`, and MSL's own design
  (which this borrows from) uses the same shortcut for that reason. The cert
  is still issued and returned at provisioning time for completeness.
- Real device-cert revocation lists / CRL distribution — a single row's
  `revoked` flag in `devices.db`, checked live, does the same job at PoC
  scale.
