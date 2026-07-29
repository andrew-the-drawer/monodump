/*
 * Phase 6b (UNTESTED SCAFFOLD -- see cdm/tee/optee/README.md): shared
 * command IDs and the TA's UUID, included by both the TA and the CA.
 * Follows the same pattern as optee_examples/hello_world's include layout.
 */
#ifndef DRM_POC_TA_H
#define DRM_POC_TA_H

/* Generated for this project; not a real registered vendor UUID. */
#define TA_DRM_POC_UUID \
	{ 0x4f2b6a6e, 0x9c1d, 0x4e8a, \
	  { 0xb3, 0x0f, 0x6a, 0x8e, 0x1d, 0x2c, 0x7f, 0x51 } }

/*
 * TA_DRM_POC_CMD_PROVISION_KEY: generate (if absent) the device's P-256
 * ECDH keypair inside the TA, persisted via GP secure storage so it
 * survives across CA invocations (the analogue of macos_sep's persistent
 * identity key, Phase 6a). Never returns the private key.
 *
 * params[0] (out, memref): device public key, raw X9.63 (0x04 || X || Y),
 *                           65 bytes.
 */
#define TA_DRM_POC_CMD_PROVISION_KEY 0

/*
 * TA_DRM_POC_CMD_UNWRAP_AND_DECRYPT: the core of the demo. Derives a
 * session key via ECDH against a caller-supplied ephemeral public key (see
 * README for why this is a simplified HMAC-based derivation, not the exact
 * HKDF from docs/01-protocol.md), uses it to unwrap a content key, then
 * AES-CTR-decrypts an encrypted sample directly into params[3], which must
 * be an SDP-backed shared memory reference -- never a normal one. This is
 * the operation that never lets plaintext reach normal-world-readable
 * memory.
 *
 * params[0] (in, memref):  peer (server) ephemeral public key, raw X9.63,
 *                           65 bytes.
 * params[1] (in, memref):  wrapped content key: 16-byte IV || N-byte
 *                           AES-CTR ciphertext (content key is 16 bytes,
 *                           AES-128).
 * params[2] (in, memref):  encrypted sample: 16-byte IV || ciphertext.
 * params[3] (inout, memref): SDP-backed output buffer, at least as large
 *                           as the sample ciphertext. Decrypted plaintext
 *                           is written here and nowhere else.
 */
#define TA_DRM_POC_CMD_UNWRAP_AND_DECRYPT 1

/*
 * TA_DRM_POC_CMD_HASH_PROOF: SHA-256 of the buffer at params[0] -- meant
 * to be called with the same SDP buffer CMD_UNWRAP_AND_DECRYPT just wrote
 * to. Proves correct decryption without ever handing plaintext back to
 * normal world.
 *
 * params[0] (in, memref):  the SDP buffer to hash.
 * params[1] (out, memref): 32-byte SHA-256 digest.
 */
#define TA_DRM_POC_CMD_HASH_PROOF 2

#endif /* DRM_POC_TA_H */
