#include <stdio.h>
#include <unistd.h>
#include <sys/socket.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <linux/if_alg.h>
#include <linux/socket.h>
#include <string.h>
#include <stdlib.h>
#include <errno.h>
#include <stdint.h>
#include <assert.h>
#include <fcntl.h>
#include <limits.h>

#include "af_alg.h"

#define ITER_NO            1
#define PAYLOAD_AES_BLOCKS 1
#define PAYLOAD_SIZE       (AES_BLOCK_SIZE * PAYLOAD_AES_BLOCKS)

/*
 * Adapted from https://github.com/dsprenkels/randombytes/blob/master/randombytes.c
 */
static int get_urandom_bytes(void *buf, size_t n)
{
	int fd;
	size_t offset = 0, count;
	ssize_t tmp;
	do {
		fd = open("/dev/urandom", O_RDONLY);
	} while (fd == -1 && errno == EINTR);
	if (fd == -1)
		return -1;

	while (n > 0) {
		count = n <= SSIZE_MAX ? n : SSIZE_MAX;
		tmp = read(fd, (char *)buf + offset, count);
		if (tmp == -1 && (errno == EAGAIN || errno == EINTR)) {
			continue;
		}
		if (tmp == -1)
			return -1; /* Unrecoverable IO error */
		offset += tmp;
		n -= tmp;
	}
	assert(n == 0);

	return 0;
}

static void check_aes_buffers(uint8_t *aes_buf_in, uint8_t *aes_buf_out, int blocks_no)
{
        int i =0;

        for (i = 0; i < blocks_no; ++i) {
                if(memcmp(aes_buf_in + i * AES_BLOCK_SIZE,
                        aes_buf_out + i * AES_BLOCK_SIZE, AES_BLOCK_SIZE) != 0) {
                        fprintf(stderr, "Block no. %d verification failed!\n", i);
                        dump_aes_buffer(stderr, "Block 1: ", aes_buf_in + i * AES_BLOCK_SIZE, 1);
                        dump_aes_buffer(stderr, "Block 2: ", aes_buf_out + i * AES_BLOCK_SIZE, 1);

                        exit(EXIT_FAILURE);
                }
        }
}

static int set_randomized_key(struct crypto_op *cop, uint8_t *key, unsigned int keysize)
{
	get_urandom_bytes(key, keysize);
	dump_buffer(stdout, "key: ", key, keysize);
	printf("\n");

	af_alg_set_key(cop, key, keysize);

	return 0;
}

static int set_random_iv(struct crypto_op *cop)
{
	struct af_alg_iv *iv;

	iv = af_alg_get_iv_ptr(cop);
	get_urandom_bytes(iv->iv, cop->iv_size);
	iv->ivlen = cop->iv_size;

	dump_buffer(stdout, "iv:", iv->iv, cop->iv_size);
	printf("\n");

	return 0;
}

static int set_random_aad(struct crypto_op *cop, uint8_t *aad)
{
	af_alg_set_aadlen(cop);

	get_urandom_bytes(aad, cop->aad_size);

	return 0;
}

static int stress(char *alg, char *alg_type, unsigned int keysize,
			int iv_size, size_t aad_size, size_t taglen)
{
	int ret;

	struct sockaddr_alg sa;
	struct crypto_op *cop;

	uint8_t *data_in;
	uint8_t *data_in_bkp;
	uint8_t *data_out;
	uint8_t *key;
	uint8_t *aad;
	uint8_t *plaintext_in, *plaintext_out;
	uint8_t *ciphertext_in, *ciphertext_out;
	uint8_t *tag_in, *tag_out;

	size_t data_in_len;
	size_t data_out_len;

	printf("---- Running testcase for %s, %s, %u bytes key ----\n\n",
				alg_type, alg, keysize);

	memset(&sa, 0, sizeof(struct sockaddr_alg));
	sa.salg_family = AF_ALG;
	strncpy((char *)sa.salg_type, alg_type, 14);
	strncpy((char *)sa.salg_name, alg, 60);

	// For encryption maximum input data length:
	//     AAD || plaintext
	// For decryption maximum input data length:
	//     AAD || ciphertext || authentication tag
	data_in_len = aad_size + PAYLOAD_SIZE + taglen;

	// For encryption maximum output data length:
	//     ciphertext || authentication tag
	// For decryption maximum output data length:
	//     AAD || plaintext (kernel documentation issue?)
	data_out_len = aad_size + PAYLOAD_SIZE + taglen;

	// Allocate buffers
	alloc_buffer(&data_in, data_in_len);
	alloc_buffer(&data_in_bkp, data_in_len);
	alloc_buffer(&data_out, data_out_len );
	alloc_buffer(&key, keysize);

	// Setup AAD/plaintext/ciphertext/tag buffers for encryption/decryption
	// (they point to various offsets inside data_in/data_out blocks)
	//
	// TODO - do the same as libkcapi and have a function that is provided
	// a buffer of size [aad_size + payload_size + tag_size] and returns
	// pointers to various offsets inside the initial buffer marking the
	// aad/plaintext/ciphertext/tag.
	aad = data_in;

	plaintext_in = data_in + aad_size;
	plaintext_out = data_out + aad_size;

	ciphertext_in = data_in + aad_size;
	ciphertext_out = data_out + aad_size;

	tag_in = data_in + aad_size + PAYLOAD_SIZE;
	tag_out = data_out + aad_size + PAYLOAD_SIZE;

	// Allocate and initialize struct crypto_op
	cop = crypto_op_create();
	crypto_op_init(cop, iv_size, aad_size, taglen);

	// Open socket, run bind() and accept()
	ret = af_alg_sock_setup(cop, &sa);
	if (ret) {
		fprintf(stderr, "Failed to run testcase for "
			"%s, %s, %u bytes key\n\n", (char *)sa.salg_type,
			(char *)sa.salg_name, keysize);

		return -1;
	}

	// Set a random key.
	//
	// We cannot run setsockopt on a tfmfd multiple times (after the first
	// run, it return -EBUSY). Therefore keep this call outside of the
	// stress loop.
	set_randomized_key(cop, key, keysize);

	// Set taglen
	if (taglen)
		af_alg_set_taglen(cop);

	for (int i = 0; i < ITER_NO; ++i) {
		printf("---- Loop no %d ----\n\n", i);

		// Set random IV and AAD
		if (iv_size)
			set_random_iv(cop);
		if (aad_size)
			set_random_aad(cop, aad);

		// Send random blocks
		get_urandom_bytes(plaintext_in, PAYLOAD_SIZE);
		dump_aes_buffer(stdout, "plaintext_in:", plaintext_in,
						PAYLOAD_AES_BLOCKS);

		// Make a copy of the {aad, plaintext} block so we can compare
		// it with the decryption results
		memcpy(data_in_bkp, data_in, data_in_len);

		// Encrypt
		// Make sure that the right input data length is provided for
		// encryption. Input data blocks look like this:
		// AAD || plaintext
		//
		// Otherwise -EINVAL will be returned.
		encrypt(cop, data_in, aad_size + PAYLOAD_SIZE, data_out,
						data_out_len);
		dump_aes_buffer(stdout, "ciphertext:", ciphertext_out,
						PAYLOAD_AES_BLOCKS);

		if (taglen)
			dump_buffer(stdout, "tag: ", tag_out, taglen);

		// Decrypt
		memcpy(ciphertext_in, ciphertext_out, PAYLOAD_SIZE);
		if (taglen)
			memcpy(tag_in, tag_out, taglen);

		// Make sure that the right input/output data lengths are provided for
		// decryption:
		// Input data blocks look like this:
		// AAD || ciphertext || authentication tag
		// Output data blocks look like this:
		// AAD || plaintext - in the official kernel documentation
		//                    there is no specification that the output
		//                    block contians the AAD as well (?)
		//
		// Otherwise -EINVAL will be returned.
		decrypt(cop, data_in, aad_size + PAYLOAD_SIZE + taglen,
					data_out, aad_size + PAYLOAD_SIZE);
		dump_aes_buffer(stdout, "plaintext_out:", plaintext_out,
						PAYLOAD_AES_BLOCKS);

		check_aes_buffers(data_in_bkp + aad_size, plaintext_out,
						PAYLOAD_AES_BLOCKS);
	}
	printf("PASS!\n\n");

	crypto_op_finish(cop);

	return 0;
}

static int stress_skcipher(char *alg, unsigned int keysize, size_t iv_size)
{
	int ret;

	ret = stress(alg, "skcipher", keysize, iv_size, 0, 0);
	if (ret) {
		fprintf(stderr, "FAIL: testcase "
			"%s, %s, %u bytes key\n\n", "skcipher",
			alg, keysize);
	}

	return ret;
}

static int stress_aead(char *alg, unsigned int keysize, size_t iv_size,
				size_t aad_size, size_t taglen)
{
	int ret;

	ret = stress(alg, "aead", keysize, iv_size, aad_size, taglen);
	if (ret) {
		fprintf(stderr, "FAIL: testcase "
			"%s, %s, %u bytes key\n\n", "aead",
			alg, keysize);
	}

	return ret;
}

int main(void)
{
	stress_skcipher("ecb(aes)", AES_KEY128_SIZE, 0);
	stress_skcipher("ecb(aes)", AES_KEY192_SIZE, 0);
	stress_skcipher("ecb(aes)", AES_KEY256_SIZE, 0);

	stress_skcipher("cbc(aes)", AES_KEY128_SIZE, AES_IV_SIZE);
	stress_skcipher("cbc(aes)", AES_KEY192_SIZE, AES_IV_SIZE);
	stress_skcipher("cbc(aes)", AES_KEY256_SIZE, AES_IV_SIZE);

	stress_skcipher("ctr(aes)", AES_KEY128_SIZE, AES_IV_SIZE);
	stress_skcipher("ctr(aes)", AES_KEY192_SIZE, AES_IV_SIZE);
	stress_skcipher("ctr(aes)", AES_KEY256_SIZE, AES_IV_SIZE);

	stress_skcipher("pcbc(aes)", AES_KEY128_SIZE, AES_IV_SIZE);
	stress_skcipher("pcbc(aes)", AES_KEY192_SIZE, AES_IV_SIZE);
	stress_skcipher("pcbc(aes)", AES_KEY256_SIZE, AES_IV_SIZE);

	stress_skcipher("cfb(aes)", AES_KEY128_SIZE, AES_IV_SIZE);
	stress_skcipher("cfb(aes)", AES_KEY192_SIZE, AES_IV_SIZE);
	stress_skcipher("cfb(aes)", AES_KEY256_SIZE, AES_IV_SIZE);

	stress_skcipher("ofb(aes)", AES_KEY128_SIZE, AES_IV_SIZE);
	stress_skcipher("ofb(aes)", AES_KEY192_SIZE, AES_IV_SIZE);
	stress_skcipher("ofb(aes)", AES_KEY256_SIZE, AES_IV_SIZE);

	stress_aead("gcm(aes)", AES_KEY128_SIZE, GCM_IV_SIZE, GCM_AAD_SIZE, GCM_TAGLEN);
	stress_aead("gcm(aes)", AES_KEY192_SIZE, GCM_IV_SIZE, GCM_AAD_SIZE, GCM_TAGLEN);
	stress_aead("gcm(aes)", AES_KEY256_SIZE, GCM_IV_SIZE, GCM_AAD_SIZE, GCM_TAGLEN);

	return 0;
}
