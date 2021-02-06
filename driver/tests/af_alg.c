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

int alloc_buffer(uint8_t **buf, unsigned int size)
{
	uint8_t *buf_ptr;

	buf_ptr = malloc(size);
	if (!buf_ptr) {
		perror("Could not allocate buffer!");
		exit(EXIT_FAILURE);
	}

	*buf = buf_ptr;

	return 0;
}

void dump_buffer(FILE *file, char *msg, uint8_t *buf, unsigned int size)
{
	unsigned int i;

	if (msg)
		fprintf(file, "%s \n", msg);

	for (i = 0; i < size; ++i)
		fprintf(file, "%02x", buf[i]);
	fprintf(file, "\n");
}

void dump_aes_buffer(FILE *file, char *msg, uint8_t *aes_buf, int blocks_no)
{
	int i = 0;

	if (msg)
		fprintf(file, "%s \n", msg);

	for (i = 0; i < blocks_no; ++i) {
		dump_buffer(file, NULL, aes_buf + i * AES_BLOCK_SIZE, AES_BLOCK_SIZE);
	}
	fprintf(file, "\n");
}

int af_alg_sock_setup(struct crypto_op *cop, struct sockaddr_alg *sa)
{
	int ret;

	// Setup AF_ALG socket
	cop->tfmfd = socket(AF_ALG, SOCK_SEQPACKET, 0);
	if (cop->tfmfd == -1) {
		perror("socket");
		exit(EXIT_FAILURE);
	}

	ret = bind(cop->tfmfd, (struct sockaddr *)sa, sizeof(*sa));
	if (ret == -1) {
		perror("bind");
		return -1;
	}

	cop->opfd = accept(cop->tfmfd, NULL, 0);
	if (cop->opfd == -1) {
		perror("accept");
		return -1;
	}

	return 0;
}

int af_alg_set_key(struct crypto_op *cop, uint8_t *key, size_t key_size)
{
	int ret;

	ret = setsockopt(cop->tfmfd, SOL_ALG, ALG_SET_KEY, key, key_size);
	if (ret == -1) {
		perror("setsockopt ALG_SET_KEY");
		exit(EXIT_FAILURE);
	}

	return 0;
}

int af_alg_set_taglen(struct crypto_op *cop)
{
	int ret;

	ret = setsockopt(cop->tfmfd, SOL_ALG, ALG_SET_AEAD_AUTHSIZE, NULL, cop->taglen);
	if (ret == -1) {
		perror("setsockopt ALG_SET_AEAD_AUTHSIZE");
		exit(EXIT_FAILURE);
	}

	return 0;
}

void *af_alg_get_iv_ptr(struct crypto_op *cop)
{
	struct cmsghdr *cmsg;

	cmsg = CMSG_FIRSTHDR(&cop->msg);
	cmsg = CMSG_NXTHDR(&cop->msg, cmsg);

	return (void *)CMSG_DATA(cmsg);
}

static int af_alg_set_crypto_op(struct crypto_op *cop, uint32_t op)
{
	struct cmsghdr *cmsg;

	cmsg = CMSG_FIRSTHDR(&cop->msg);
	*(__u32 *)CMSG_DATA(cmsg) = op;

	return 0;
}

static int af_alg_set_encryption(struct crypto_op *cop, void *data, size_t size)
{
	af_alg_set_crypto_op(cop, ALG_OP_ENCRYPT);

	cop->iov.iov_base = data;
	cop->iov.iov_len = size;

	return 0;
}

static int af_alg_set_decryption(struct crypto_op *cop, void *data, size_t size)
{
	af_alg_set_crypto_op(cop, ALG_OP_DECRYPT);

	cop->iov.iov_base = data;
	cop->iov.iov_len = size;

	return 0;
}

int af_alg_set_aadlen(struct crypto_op *cop)
{
	struct cmsghdr *cmsg;
	uint32_t *aad_ptr;
	uint32_t aad_size;

	aad_size = cop->aad_size;

	// Skip encryption/decryption header
	cmsg = CMSG_FIRSTHDR(&cop->msg);
	// Skip IV header
	if (cop->iv_size)
		cmsg = CMSG_NXTHDR(&cop->msg, cmsg);
	// Get AAD header
	cmsg = CMSG_NXTHDR(&cop->msg, cmsg);

	aad_ptr = (void *)CMSG_DATA(cmsg);
	*aad_ptr = aad_size;

	return 0;
}

int af_alg_set_iv(struct crypto_op *cop, uint8_t *iv)
{
	struct af_alg_iv *af_iv;

	af_iv = af_alg_get_iv_ptr(cop);
	af_iv->ivlen = cop->iv_size;
	memcpy(af_iv->iv, iv, cop->iv_size);

	return 0;
}

struct crypto_op *crypto_op_create(void)
{
	struct crypto_op *cop;

	cop = calloc(1, sizeof(struct crypto_op));
	if (!cop) {
		perror("Cannot allocate space for struct crypto_op!");
		exit(EXIT_FAILURE);
	}

	return cop;
}

void crypto_op_init(struct crypto_op *cop, size_t iv_size,
				size_t aad_size, size_t taglen)
{
	size_t cbuf_size;
	uint8_t *cbuf;
	struct cmsghdr *cmsg;

	// sizeof(u32) is used here because ALG_OP_ENCRYPT/DECRYPT are
	// represented in the kernel as u32 in struct af_alg_control->op
	// (actually it is an int, but the data sent from userspace is casted
	// to u32 everywhere):
	// https://elixir.bootlin.com/linux/latest/source/include/crypto/if_alg.h#L41
	//
	// This CMSG header stores the type of crypto operation to be performed
	// (encryption or decryption) to CMSG_DATA()
	cbuf_size = CMSG_SPACE(sizeof(uint32_t));

	// sizeof(struct af_alg_iv) + iv_size is used here to allocate enough
	// space to hold the iv_len and the actual iv data.
	//
	// struct af_alg_iv {
	//	__u32	ivlen;
	//	__u8	iv[0];
	// };
	//
	// struct af_alg_iv is the one actually passed from userspace to
	// kernel. The reason we have to allocate space for [sizeof(struct
	// af_alg_iv) + iv_size] is because it contains a flexible array at the
	// end. See gcc docs on zero length arrays in structs:
	// https://gcc.gnu.org/onlinedocs/gcc/Zero-Length.html
	if (iv_size)
		cbuf_size += CMSG_SPACE(sizeof(struct af_alg_iv) + iv_size);

	// sizeof(u32) is used here because the AAD size is
	// represented in the kernel as u32 in struct af_alg_control->aead_assoclen
	// (actually it is an unsigned int, but the data sent from userspace is
	// casted to u32 everywhere):
	// https://elixir.bootlin.com/linux/latest/source/include/crypto/if_alg.h#L41
	//
	// This CMSG header stores AAD length to CMSG_DATA()
	if (aad_size)
		cbuf_size += CMSG_SPACE(sizeof(uint32_t));

	cbuf = calloc(1, cbuf_size);
	if (!cbuf) {
		perror("Cannot allocate space for cbuf!");
		exit(EXIT_FAILURE);
	}

	cop->iv_size = iv_size;
	cop->aad_size = aad_size;
	cop->taglen = taglen;
	cop->msg.msg_control = cbuf;
	cop->msg.msg_controllen = cbuf_size;

	cmsg = CMSG_FIRSTHDR(&cop->msg);
	cmsg->cmsg_level = SOL_ALG;
	cmsg->cmsg_type = ALG_SET_OP;
	cmsg->cmsg_len = CMSG_LEN(sizeof(uint32_t));

	if (iv_size) {
		cmsg = CMSG_NXTHDR(&cop->msg, cmsg);
		cmsg->cmsg_level = SOL_ALG;
		cmsg->cmsg_type = ALG_SET_IV;
		cmsg->cmsg_len = CMSG_LEN(sizeof(struct af_alg_iv) + iv_size);
	}

	if (aad_size) {
		cmsg = CMSG_NXTHDR(&cop->msg, cmsg);
		cmsg->cmsg_level = SOL_ALG;
		cmsg->cmsg_type = ALG_SET_AEAD_ASSOCLEN;
		cmsg->cmsg_len = CMSG_LEN(sizeof(uint32_t));
	}

	cop->msg.msg_iov = &cop->iov;
	cop->msg.msg_iovlen = 1;
}

void crypto_op_finish(struct crypto_op *cop)
{
	close(cop->opfd);
	close(cop->tfmfd);

	free(cop);
}

int encrypt(struct crypto_op *cop, uint8_t *data_in, size_t data_in_len,
			uint8_t *data_out, size_t data_out_len)
{
	int ret;

	af_alg_set_encryption(cop, data_in, data_in_len);

	ret = sendmsg(cop->opfd, &cop->msg, 0);
	if (ret == -1) {
		perror("sendmsg");
		exit(EXIT_FAILURE);
	}

	ret = read(cop->opfd, data_out, data_out_len);
	if (ret == -1) {
		perror("read");
		exit(EXIT_FAILURE);
	}

	return 0;
}

int decrypt(struct crypto_op *cop, uint8_t *data_in, size_t data_in_len,
			uint8_t *data_out, size_t data_out_len)
{
	int ret;

	af_alg_set_decryption(cop, data_in, data_in_len);

	ret = sendmsg(cop->opfd, &cop->msg, 0);
	if (ret == -1) {
		perror("sendmsg");
		exit(EXIT_FAILURE);
	}

	ret = read(cop->opfd, data_out, data_out_len);
	if (ret == -1) {
		perror("read");
		exit(EXIT_FAILURE);
	}

	return 0;
}

void buf_eq(char *desc, uint8_t *buf1, uint8_t *buf2, unsigned int nbytes)
{
	if (memcmp(buf1, buf2, nbytes)) {
		fprintf(stderr, "%s: data mismatch!\n", desc);
		dump_buffer(stderr, NULL, buf1, nbytes);
		dump_buffer(stderr, NULL, buf2, nbytes);

		exit(EXIT_FAILURE);
	}
}
