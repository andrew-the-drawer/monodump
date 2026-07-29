/*
 * Phase 6b CA (UNTESTED SCAFFOLD -- see cdm/tee/optee/README.md).
 *
 * Drives the drm_poc TA through the three commands in
 * ta/include/drm_poc_ta.h, and -- this is the actual point of 6b, per
 * PLAN.md's "design the demo around the negative test, not the pixels" --
 * proves the SDP output buffer is unreadable from normal-world Linux
 * rather than trying to show decoded pixels (QEMU has no protected
 * display path to show them on anyway).
 *
 * Test vectors (server ephemeral pubkey, wrapped content key, encrypted
 * sample, expected plaintext hash) come from files on disk, generated
 * offline by ../gen_test_vectors.py against this TA instance's real
 * provisioned public key -- see the README for the two-step workflow
 * (provision once, generate vectors on the host, run again).
 *
 * The SDP allocation path (`alloc_sdp_buffer`) follows the pattern in
 * OP-TEE's own reference test, cited in PLAN.md:
 *   https://github.com/OP-TEE/optee_test/blob/master/host/xtest/sdp_basic.c
 * That file is the source of truth for the exact ioctl/libteec call shapes
 * on whatever OP-TEE version actually gets built; treat the constants and
 * function names here as a best-effort reproduction, not verified against
 * a real build.
 */
#include <err.h>
#include <fcntl.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/ioctl.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <unistd.h>

#include <tee_client_api.h>

#include <drm_poc_ta.h>

#define ECC_PUBKEY_X963_SIZE 65
#define SHA256_DIGEST_SIZE 32

static const char *DEFAULT_DATA_DIR = "/data/drm_poc";

/* --- DMA-BUF SDP heap allocation, per optee_test/host/xtest/sdp_basic.c --- */

#define DMA_HEAP_IOC_MAGIC 'H'
struct dma_heap_allocation_data {
	uint64_t len;
	uint32_t fd;
	uint32_t fd_flags;
	uint64_t heap_flags;
};
#define DMA_HEAP_IOCTL_ALLOC _IOWR(DMA_HEAP_IOC_MAGIC, 0x0, struct dma_heap_allocation_data)

/*
 * Returns a TEEC_SharedMemory whose backing pages come from the
 * "/dev/dma_heap/sdp" heap -- physical memory OP-TEE carved out of secure
 * DRAM specifically so it can be mapped into a TA on demand and never into
 * OP-TEE core or Linux otherwise. `insecure_debug` allocates an ordinary
 * TEEC shared memory buffer instead, for the deliberately-broken contrast
 * mode PLAN.md asks for.
 */
static TEEC_Result alloc_output_buffer(TEEC_Context *ctx, size_t size,
					int insecure_debug, TEEC_SharedMemory *shm,
					int *dmabuf_fd_out)
{
	*dmabuf_fd_out = -1;

	if (insecure_debug) {
		memset(shm, 0, sizeof(*shm));
		shm->size = size;
		shm->flags = TEEC_MEM_INPUT | TEEC_MEM_OUTPUT;
		return TEEC_AllocateSharedMemory(ctx, shm);
	}

	int heap_fd = open("/dev/dma_heap/sdp", O_RDWR | O_CLOEXEC);
	if (heap_fd < 0)
		err(1, "open /dev/dma_heap/sdp (does this kernel have "
		       "CFG_SECURE_DATA_PATH's SDP DMA-heap driver enabled?)");

	struct dma_heap_allocation_data alloc = {
		.len = size,
		.fd_flags = O_RDWR | O_CLOEXEC,
	};
	if (ioctl(heap_fd, DMA_HEAP_IOCTL_ALLOC, &alloc) < 0)
		err(1, "DMA_HEAP_IOCTL_ALLOC");
	close(heap_fd);

	memset(shm, 0, sizeof(*shm));
	shm->size = size;
	shm->flags = TEEC_MEM_INPUT | TEEC_MEM_OUTPUT;
	/*
	 * The exact libteec entry point for wrapping a dma-buf fd as shared
	 * memory has varied across OP-TEE releases
	 * (TEEC_RegisterSharedMemoryFileDescriptor in some, a
	 * tee_client_api extension in others) -- confirm against the
	 * actual optee_client headers this build pulls in.
	 */
	TEEC_Result res = TEEC_RegisterSharedMemoryFileDescriptor(ctx, shm, alloc.fd);
	*dmabuf_fd_out = alloc.fd;
	return res;
}

/* --- test vector I/O --- */

static uint8_t *read_file(const char *dir, const char *name, size_t *len_out)
{
	char path[512];
	snprintf(path, sizeof(path), "%s/%s", dir, name);
	FILE *f = fopen(path, "rb");
	if (!f)
		err(1, "fopen %s", path);
	fseek(f, 0, SEEK_END);
	long len = ftell(f);
	fseek(f, 0, SEEK_SET);
	uint8_t *buf = malloc(len);
	if (!buf)
		err(1, "malloc");
	if (fread(buf, 1, len, f) != (size_t)len)
		err(1, "fread %s", path);
	fclose(f);
	*len_out = (size_t)len;
	return buf;
}

static void write_file(const char *dir, const char *name, const uint8_t *data, size_t len)
{
	char path[512];
	snprintf(path, sizeof(path), "%s/%s", dir, name);
	FILE *f = fopen(path, "wb");
	if (!f)
		err(1, "fopen %s for write", path);
	fwrite(data, 1, len, f);
	fclose(f);
}

static void hex_print(const char *label, const uint8_t *data, size_t len)
{
	printf("%s: ", label);
	for (size_t i = 0; i < len; i++)
		printf("%02x", data[i]);
	printf("\n");
}

int main(int argc, char *argv[])
{
	TEEC_Result res;
	TEEC_Context ctx;
	TEEC_Session sess;
	TEEC_Operation op;
	TEEC_UUID uuid = TA_DRM_POC_UUID;
	uint32_t err_origin;
	int insecure_debug = (argc > 1 && strcmp(argv[1], "--insecure-debug-dump") == 0);
	const char *data_dir = DEFAULT_DATA_DIR;

	res = TEEC_InitializeContext(NULL, &ctx);
	if (res != TEEC_SUCCESS)
		errx(1, "TEEC_InitializeContext failed: 0x%x", res);

	res = TEEC_OpenSession(&ctx, &sess, &uuid, TEEC_LOGIN_PUBLIC, NULL, NULL, &err_origin);
	if (res != TEEC_SUCCESS)
		errx(1, "TEEC_OpenSession failed: 0x%x (origin 0x%x)", res, err_origin);

	/* --- step 1: provision (idempotent) and print the device pubkey --- */
	uint8_t device_pubkey[ECC_PUBKEY_X963_SIZE];
	memset(&op, 0, sizeof(op));
	op.paramTypes = TEEC_PARAM_TYPES(TEEC_MEMREF_TEMP_OUTPUT, TEEC_NONE, TEEC_NONE, TEEC_NONE);
	op.params[0].tmpref.buffer = device_pubkey;
	op.params[0].tmpref.size = sizeof(device_pubkey);
	res = TEEC_InvokeCommand(&sess, TA_DRM_POC_CMD_PROVISION_KEY, &op, &err_origin);
	if (res != TEEC_SUCCESS)
		errx(1, "PROVISION_KEY failed: 0x%x (origin 0x%x)", res, err_origin);
	hex_print("device public key (x963)", device_pubkey, sizeof(device_pubkey));
	write_file(data_dir, "device_pubkey.bin", device_pubkey, sizeof(device_pubkey));
	printf("wrote %s/device_pubkey.bin -- feed this to ../gen_test_vectors.py "
	       "on the host, then re-run with the generated vectors present.\n", data_dir);

	/* --- step 2: load test vectors (see gen_test_vectors.py) --- */
	size_t peer_pub_len, wrapped_key_len, sample_len, expected_hash_len;
	uint8_t *peer_pub = read_file(data_dir, "server_ephemeral_pub.bin", &peer_pub_len);
	uint8_t *wrapped_key = read_file(data_dir, "wrapped_key.bin", &wrapped_key_len);
	uint8_t *sample = read_file(data_dir, "encrypted_sample.bin", &sample_len);
	uint8_t *expected_hash = read_file(data_dir, "plaintext_sha256.bin", &expected_hash_len);

	/* --- step 3: allocate the output buffer (SDP, unless --insecure-debug-dump) --- */
	size_t plaintext_size = sample_len - 16; /* minus the 16-byte IV prefix */
	TEEC_SharedMemory out_shm;
	int dmabuf_fd;
	res = alloc_output_buffer(&ctx, plaintext_size, insecure_debug, &out_shm, &dmabuf_fd);
	if (res != TEEC_SUCCESS)
		errx(1, "output buffer allocation failed: 0x%x", res);

	if (insecure_debug)
		printf("!!! --insecure-debug-dump: output buffer is ORDINARY shared memory, "
		       "NOT SDP. This is exactly the mistake real L1 hardware forbids. !!!\n");

	/* --- step 4: unwrap + decrypt directly into that buffer --- */
	memset(&op, 0, sizeof(op));
	op.paramTypes = TEEC_PARAM_TYPES(TEEC_MEMREF_TEMP_INPUT, TEEC_MEMREF_TEMP_INPUT,
					  TEEC_MEMREF_TEMP_INPUT, TEEC_MEMREF_WHOLE);
	op.params[0].tmpref.buffer = peer_pub;
	op.params[0].tmpref.size = peer_pub_len;
	op.params[1].tmpref.buffer = wrapped_key;
	op.params[1].tmpref.size = wrapped_key_len;
	op.params[2].tmpref.buffer = sample;
	op.params[2].tmpref.size = sample_len;
	op.params[3].memref.parent = &out_shm;
	res = TEEC_InvokeCommand(&sess, TA_DRM_POC_CMD_UNWRAP_AND_DECRYPT, &op, &err_origin);
	if (res != TEEC_SUCCESS)
		errx(1, "UNWRAP_AND_DECRYPT failed: 0x%x (origin 0x%x)", res, err_origin);

	/* --- step 5: the actual point of 6b -- try to read the output ourselves --- */
	if (!insecure_debug) {
		printf("attempting to read the SDP output buffer directly from "
		       "normal-world Linux userspace...\n");
		int all_zero = 1;
		uint8_t *p = out_shm.buffer;
		for (size_t i = 0; i < plaintext_size && i < 64; i++)
			if (p[i] != 0) { all_zero = 0; break; }
		if (all_zero)
			printf("  read succeeded but returned all zeros -- the mapping "
			       "Linux sees for this dma-buf is not backed by the "
			       "physical SDP pages the TA actually wrote to.\n");
		else
			hex_print("  UNEXPECTED: read real-looking bytes from an SDP buffer",
				  p, 32);
	} else {
		printf("insecure debug mode: reading the (ordinary, non-SDP) output buffer:\n");
		hex_print("  plaintext (visible to normal world on purpose, to contrast)",
			  out_shm.buffer, plaintext_size < 32 ? plaintext_size : 32);
	}

	/* --- step 6: prove correctness via hash, never via plaintext --- */
	uint8_t digest[SHA256_DIGEST_SIZE];
	memset(&op, 0, sizeof(op));
	op.paramTypes = TEEC_PARAM_TYPES(TEEC_MEMREF_WHOLE, TEEC_MEMREF_TEMP_OUTPUT,
					  TEEC_NONE, TEEC_NONE);
	op.params[0].memref.parent = &out_shm;
	op.params[1].tmpref.buffer = digest;
	op.params[1].tmpref.size = sizeof(digest);
	res = TEEC_InvokeCommand(&sess, TA_DRM_POC_CMD_HASH_PROOF, &op, &err_origin);
	if (res != TEEC_SUCCESS)
		errx(1, "HASH_PROOF failed: 0x%x (origin 0x%x)", res, err_origin);

	hex_print("TA-reported SHA-256 of decrypted plaintext", digest, sizeof(digest));
	hex_print("expected SHA-256 (from gen_test_vectors.py)", expected_hash,
		  expected_hash_len);
	if (expected_hash_len == sizeof(digest) && memcmp(digest, expected_hash, sizeof(digest)) == 0)
		printf("MATCH -- decryption was correct, proven without the plaintext "
		       "ever leaving the TA-controlled buffer for inspection here.\n");
	else
		printf("MISMATCH -- decryption did not produce the expected plaintext.\n");

	free(peer_pub);
	free(wrapped_key);
	free(sample);
	free(expected_hash);
	TEEC_ReleaseSharedMemory(&out_shm);
	if (dmabuf_fd >= 0)
		close(dmabuf_fd);
	TEEC_CloseSession(&sess);
	TEEC_FinalizeContext(&ctx);
	return 0;
}
