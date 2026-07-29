/*
 * Phase 6b TA (UNTESTED SCAFFOLD -- see cdm/tee/optee/README.md for status
 * and exactly what has and hasn't been verified).
 *
 * Implements the three commands in include/drm_poc_ta.h against the
 * GlobalPlatform TEE Internal Core API, following the shape OP-TEE
 * implements it in. Simplifications relative to docs/01-protocol.md's real
 * Phase 3 protocol, made deliberately to keep this a reasonable first TA
 * rather than a byte-exact reimplementation, and called out here rather
 * than silently:
 *
 *   - Session key derivation is HMAC-SHA256(ecdh_shared_secret,
 *     "drm-poc-sdp-v1"), not the real HKDF-SHA256 with a per-request nonce
 *     salt. A real integration would want the exact same HKDF call
 *     server/crypto.py uses.
 *   - No signing/identity keypair, no master token, no policy -- this TA
 *     only demonstrates the ECDH-derive -> unwrap -> decrypt-into-SDP
 *     pipeline, which is the part 6b exists to prove (secure-world
 *     decrypt + SDP buffer isolation). Wiring in the rest of the protocol
 *     is future work, not required for the win condition PLAN.md Phase 6
 *     states (decrypt without the key ever being REE-visible).
 */
#include <tee_internal_api.h>
#include <tee_internal_api_extensions.h>

#include <drm_poc_ta.h>

#define DEVICE_KEY_OBJECT_ID ((void *)"drm_poc_device_key")
#define DEVICE_KEY_OBJECT_ID_LEN 19

#define ECC_COORD_SIZE 32
#define ECC_PUBKEY_X963_SIZE (1 + 2 * ECC_COORD_SIZE) /* 0x04 || X || Y */
#define AES_BLOCK_SIZE 16
#define CONTENT_KEY_SIZE 16 /* AES-128 content keys, matching server/crypto.py's tier keys */
#define SESSION_KEY_DERIVE_INFO ((void *)"drm-poc-sdp-v1")
#define SESSION_KEY_DERIVE_INFO_LEN 14
#define SHA256_DIGEST_SIZE 32

struct session_ctx {
	TEE_ObjectHandle device_key; /* opened lazily by PROVISION_KEY */
};

TEE_Result TA_CreateEntryPoint(void)
{
	return TEE_SUCCESS;
}

void TA_DestroyEntryPoint(void)
{
}

TEE_Result TA_OpenSessionEntryPoint(uint32_t param_types, TEE_Param params[4],
				    void **session_ctx_out)
{
	struct session_ctx *ctx;

	(void)param_types;
	(void)params;

	ctx = TEE_Malloc(sizeof(*ctx), TEE_MALLOC_FILL_ZERO);
	if (!ctx)
		return TEE_ERROR_OUT_OF_MEMORY;
	ctx->device_key = TEE_HANDLE_NULL;
	*session_ctx_out = ctx;
	return TEE_SUCCESS;
}

void TA_CloseSessionEntryPoint(void *session_ctx)
{
	struct session_ctx *ctx = session_ctx;

	if (ctx->device_key != TEE_HANDLE_NULL)
		TEE_CloseObject(ctx->device_key);
	TEE_Free(ctx);
}

/*
 * Opens the persisted device key if one exists, else generates a fresh
 * P-256 ECDH keypair and persists it under a fixed object ID -- the TA
 * analogue of macos_sep's identity key, minus per-label multiplexing
 * (this scaffold assumes a single device identity per TA instance).
 */
static TEE_Result get_or_create_device_key(TEE_ObjectHandle *out)
{
	TEE_Result res;
	TEE_ObjectHandle persistent = TEE_HANDLE_NULL;
	TEE_ObjectHandle fresh = TEE_HANDLE_NULL;
	TEE_Attribute curve_attr;

	res = TEE_OpenPersistentObject(TEE_STORAGE_PRIVATE,
					DEVICE_KEY_OBJECT_ID,
					DEVICE_KEY_OBJECT_ID_LEN,
					TEE_DATA_FLAG_ACCESS_READ,
					&persistent);
	if (res == TEE_SUCCESS) {
		*out = persistent;
		return TEE_SUCCESS;
	}
	if (res != TEE_ERROR_ITEM_NOT_FOUND)
		return res;

	res = TEE_AllocateTransientObject(TEE_TYPE_ECDH_KEYPAIR, 256, &fresh);
	if (res != TEE_SUCCESS)
		return res;

	TEE_InitValueAttribute(&curve_attr, TEE_ATTR_ECC_CURVE,
				TEE_ECC_CURVE_NIST_P256, 0);
	res = TEE_GenerateKey(fresh, 256, &curve_attr, 1);
	if (res != TEE_SUCCESS) {
		TEE_FreeTransientObject(fresh);
		return res;
	}

	res = TEE_CreatePersistentObject(TEE_STORAGE_PRIVATE,
					  DEVICE_KEY_OBJECT_ID,
					  DEVICE_KEY_OBJECT_ID_LEN,
					  TEE_DATA_FLAG_ACCESS_READ |
					  TEE_DATA_FLAG_ACCESS_WRITE,
					  fresh, NULL, 0, &persistent);
	TEE_FreeTransientObject(fresh);
	if (res != TEE_SUCCESS)
		return res;

	*out = persistent;
	return TEE_SUCCESS;
}

static TEE_Result cmd_provision_key(struct session_ctx *ctx, uint32_t param_types,
				    TEE_Param params[4])
{
	TEE_Result res;
	uint8_t x[ECC_COORD_SIZE];
	uint8_t y[ECC_COORD_SIZE];
	uint32_t x_len = sizeof(x);
	uint32_t y_len = sizeof(y);
	uint8_t *out;
	uint32_t out_len;

	if (TEE_PARAM_TYPES(TEE_PARAM_TYPE_MEMREF_OUTPUT, TEE_PARAM_TYPE_NONE,
			     TEE_PARAM_TYPE_NONE, TEE_PARAM_TYPE_NONE) != param_types)
		return TEE_ERROR_BAD_PARAMETERS;

	if (ctx->device_key == TEE_HANDLE_NULL) {
		res = get_or_create_device_key(&ctx->device_key);
		if (res != TEE_SUCCESS)
			return res;
	}

	res = TEE_GetObjectBufferAttribute(ctx->device_key,
					    TEE_ATTR_ECC_PUBLIC_VALUE_X, x, &x_len);
	if (res != TEE_SUCCESS)
		return res;
	res = TEE_GetObjectBufferAttribute(ctx->device_key,
					    TEE_ATTR_ECC_PUBLIC_VALUE_Y, y, &y_len);
	if (res != TEE_SUCCESS)
		return res;

	out = params[0].memref.buffer;
	out_len = params[0].memref.size;
	if (out_len < ECC_PUBKEY_X963_SIZE)
		return TEE_ERROR_SHORT_BUFFER;

	out[0] = 0x04;
	TEE_MemMove(out + 1, x, ECC_COORD_SIZE);
	TEE_MemMove(out + 1 + ECC_COORD_SIZE, y, ECC_COORD_SIZE);
	params[0].memref.size = ECC_PUBKEY_X963_SIZE;
	return TEE_SUCCESS;
}

/*
 * ECDH(device_priv, peer_pub) -> HMAC-SHA256(shared_secret, "drm-poc-sdp-v1")
 * -> 32-byte session key. See the file header for why this isn't the real
 * HKDF from docs/01-protocol.md.
 */
static TEE_Result derive_session_key(TEE_ObjectHandle device_key,
				      const uint8_t *peer_x, const uint8_t *peer_y,
				      uint8_t session_key[SHA256_DIGEST_SIZE])
{
	TEE_Result res;
	TEE_OperationHandle derive_op = TEE_HANDLE_NULL;
	TEE_OperationHandle mac_op = TEE_HANDLE_NULL;
	TEE_ObjectHandle shared_secret_obj = TEE_HANDLE_NULL;
	TEE_ObjectHandle hmac_key_obj = TEE_HANDLE_NULL;
	TEE_Attribute peer_attrs[2];
	TEE_Attribute hmac_key_attr;
	uint8_t shared_secret[ECC_COORD_SIZE];
	uint32_t shared_secret_len = sizeof(shared_secret);
	uint32_t session_key_len = SHA256_DIGEST_SIZE;

	res = TEE_AllocateOperation(&derive_op, TEE_ALG_ECDH_P256,
				    TEE_MODE_DERIVE, 256);
	if (res != TEE_SUCCESS)
		goto out;
	res = TEE_SetOperationKey(derive_op, device_key);
	if (res != TEE_SUCCESS)
		goto out;

	res = TEE_AllocateTransientObject(TEE_TYPE_GENERIC_SECRET, 256,
					   &shared_secret_obj);
	if (res != TEE_SUCCESS)
		goto out;

	TEE_InitRefAttribute(&peer_attrs[0], TEE_ATTR_ECC_PUBLIC_VALUE_X,
			      (void *)peer_x, ECC_COORD_SIZE);
	TEE_InitRefAttribute(&peer_attrs[1], TEE_ATTR_ECC_PUBLIC_VALUE_Y,
			      (void *)peer_y, ECC_COORD_SIZE);
	TEE_DeriveKey(derive_op, peer_attrs, 2, shared_secret_obj);

	res = TEE_GetObjectBufferAttribute(shared_secret_obj, TEE_ATTR_SECRET_VALUE,
					    shared_secret, &shared_secret_len);
	if (res != TEE_SUCCESS)
		goto out;

	res = TEE_AllocateTransientObject(TEE_TYPE_HMAC_SHA256, 256, &hmac_key_obj);
	if (res != TEE_SUCCESS)
		goto out;
	TEE_InitRefAttribute(&hmac_key_attr, TEE_ATTR_SECRET_VALUE,
			      shared_secret, shared_secret_len);
	res = TEE_PopulateTransientObject(hmac_key_obj, &hmac_key_attr, 1);
	if (res != TEE_SUCCESS)
		goto out;

	res = TEE_AllocateOperation(&mac_op, TEE_ALG_HMAC_SHA256, TEE_MODE_MAC, 256);
	if (res != TEE_SUCCESS)
		goto out;
	res = TEE_SetOperationKey(mac_op, hmac_key_obj);
	if (res != TEE_SUCCESS)
		goto out;

	TEE_MACInit(mac_op, NULL, 0);
	res = TEE_MACComputeFinal(mac_op, SESSION_KEY_DERIVE_INFO,
				   SESSION_KEY_DERIVE_INFO_LEN,
				   session_key, &session_key_len);

out:
	if (derive_op != TEE_HANDLE_NULL)
		TEE_FreeOperation(derive_op);
	if (mac_op != TEE_HANDLE_NULL)
		TEE_FreeOperation(mac_op);
	if (shared_secret_obj != TEE_HANDLE_NULL)
		TEE_FreeTransientObject(shared_secret_obj);
	if (hmac_key_obj != TEE_HANDLE_NULL)
		TEE_FreeTransientObject(hmac_key_obj);
	return res;
}

static TEE_Result aes_ctr(TEE_OperationMode mode, const uint8_t *key, uint32_t key_bits,
			   const uint8_t iv[AES_BLOCK_SIZE],
			   const uint8_t *in, uint32_t in_len,
			   uint8_t *out, uint32_t *out_len)
{
	TEE_Result res;
	TEE_ObjectHandle key_obj = TEE_HANDLE_NULL;
	TEE_OperationHandle op = TEE_HANDLE_NULL;
	TEE_Attribute key_attr;

	res = TEE_AllocateTransientObject(TEE_TYPE_AES, key_bits, &key_obj);
	if (res != TEE_SUCCESS)
		goto out;
	TEE_InitRefAttribute(&key_attr, TEE_ATTR_SECRET_VALUE, (void *)key, key_bits / 8);
	res = TEE_PopulateTransientObject(key_obj, &key_attr, 1);
	if (res != TEE_SUCCESS)
		goto out;

	res = TEE_AllocateOperation(&op, TEE_ALG_AES_CTR, mode, key_bits);
	if (res != TEE_SUCCESS)
		goto out;
	res = TEE_SetOperationKey(op, key_obj);
	if (res != TEE_SUCCESS)
		goto out;

	TEE_CipherInit(op, iv, AES_BLOCK_SIZE);
	res = TEE_CipherDoFinal(op, in, in_len, out, out_len);

out:
	if (key_obj != TEE_HANDLE_NULL)
		TEE_FreeTransientObject(key_obj);
	if (op != TEE_HANDLE_NULL)
		TEE_FreeOperation(op);
	return res;
}

/*
 * The operation 6b exists to demonstrate: decrypts directly into
 * params[3], which the CA must have allocated as an SDP-backed buffer
 * (see host/main.c). Nothing in this function ever copies plaintext
 * anywhere else -- if params[3] is genuinely SDP memory, that plaintext
 * physically cannot land anywhere normal-world Linux can read.
 */
static TEE_Result cmd_unwrap_and_decrypt(struct session_ctx *ctx, uint32_t param_types,
					  TEE_Param params[4])
{
	TEE_Result res;
	uint8_t session_key[SHA256_DIGEST_SIZE];
	uint8_t content_key[CONTENT_KEY_SIZE];
	uint32_t content_key_len = sizeof(content_key);
	uint8_t *peer_pub, *wrapped_key, *sample;
	uint32_t peer_pub_len, wrapped_key_len, sample_len, out_len;

	if (TEE_PARAM_TYPES(TEE_PARAM_TYPE_MEMREF_INPUT, TEE_PARAM_TYPE_MEMREF_INPUT,
			     TEE_PARAM_TYPE_MEMREF_INPUT, TEE_PARAM_TYPE_MEMREF_INOUT) !=
	    param_types)
		return TEE_ERROR_BAD_PARAMETERS;

	if (ctx->device_key == TEE_HANDLE_NULL)
		return TEE_ERROR_ACCESS_DENIED; /* must PROVISION_KEY first */

	peer_pub = params[0].memref.buffer;
	peer_pub_len = params[0].memref.size;
	if (peer_pub_len != ECC_PUBKEY_X963_SIZE || peer_pub[0] != 0x04)
		return TEE_ERROR_BAD_PARAMETERS;

	res = derive_session_key(ctx->device_key, peer_pub + 1,
				  peer_pub + 1 + ECC_COORD_SIZE, session_key);
	if (res != TEE_SUCCESS)
		return res;

	wrapped_key = params[1].memref.buffer;
	wrapped_key_len = params[1].memref.size;
	if (wrapped_key_len <= AES_BLOCK_SIZE)
		return TEE_ERROR_BAD_PARAMETERS;

	res = aes_ctr(TEE_MODE_DECRYPT, session_key, 256, wrapped_key,
		      wrapped_key + AES_BLOCK_SIZE, wrapped_key_len - AES_BLOCK_SIZE,
		      content_key, &content_key_len);
	if (res != TEE_SUCCESS)
		return res;
	if (content_key_len != CONTENT_KEY_SIZE)
		return TEE_ERROR_BAD_PARAMETERS;

	sample = params[2].memref.buffer;
	sample_len = params[2].memref.size;
	if (sample_len <= AES_BLOCK_SIZE)
		return TEE_ERROR_BAD_PARAMETERS;

	out_len = params[3].memref.size;
	res = aes_ctr(TEE_MODE_DECRYPT, content_key, 128, sample,
		      sample + AES_BLOCK_SIZE, sample_len - AES_BLOCK_SIZE,
		      params[3].memref.buffer, &out_len);
	if (res != TEE_SUCCESS)
		return res;
	params[3].memref.size = out_len;
	return TEE_SUCCESS;
}

static TEE_Result cmd_hash_proof(uint32_t param_types, TEE_Param params[4])
{
	TEE_Result res;
	TEE_OperationHandle digest_op = TEE_HANDLE_NULL;
	uint32_t out_len;

	if (TEE_PARAM_TYPES(TEE_PARAM_TYPE_MEMREF_INPUT, TEE_PARAM_TYPE_MEMREF_OUTPUT,
			     TEE_PARAM_TYPE_NONE, TEE_PARAM_TYPE_NONE) != param_types)
		return TEE_ERROR_BAD_PARAMETERS;

	if (params[1].memref.size < SHA256_DIGEST_SIZE)
		return TEE_ERROR_SHORT_BUFFER;

	res = TEE_AllocateOperation(&digest_op, TEE_ALG_SHA256, TEE_MODE_DIGEST, 0);
	if (res != TEE_SUCCESS)
		return res;

	out_len = params[1].memref.size;
	res = TEE_DigestDoFinal(digest_op, params[0].memref.buffer, params[0].memref.size,
				 params[1].memref.buffer, &out_len);
	TEE_FreeOperation(digest_op);
	if (res != TEE_SUCCESS)
		return res;

	params[1].memref.size = out_len;
	return TEE_SUCCESS;
}

TEE_Result TA_InvokeCommandEntryPoint(void *session_ctx, uint32_t cmd_id,
				      uint32_t param_types, TEE_Param params[4])
{
	struct session_ctx *ctx = session_ctx;

	switch (cmd_id) {
	case TA_DRM_POC_CMD_PROVISION_KEY:
		return cmd_provision_key(ctx, param_types, params);
	case TA_DRM_POC_CMD_UNWRAP_AND_DECRYPT:
		return cmd_unwrap_and_decrypt(ctx, param_types, params);
	case TA_DRM_POC_CMD_HASH_PROOF:
		return cmd_hash_proof(param_types, params);
	default:
		return TEE_ERROR_NOT_SUPPORTED;
	}
}
