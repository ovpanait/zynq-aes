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

#ifndef SOL_ALG
#define SOL_ALG 279
#endif

#define AES_BLOCK_SIZE  16
#define AES_IV_SIZE     16
#define AES_KEY128_SIZE 16
#define AES_KEY256_SIZE 32

#define ITER_NO            1
#define PAYLOAD_AES_BLOCKS 1000
#define PAYLOAD_SIZE       (AES_BLOCK_SIZE * PAYLOAD_AES_BLOCKS)

struct crypto_op {
	int tfmfd;
	int opfd;
	uint8_t *cbuf;
	struct msghdr msg;
	struct iovec iov;
};

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

static int af_alg_setup(struct crypto_op *cop, struct sockaddr_alg *sa)
{
	int tfmfd, ret;

	// Setup AF_ALG socket
	tfmfd = socket(AF_ALG, SOCK_SEQPACKET, 0);
	if (tfmfd == -1) {
		perror("socket");
		exit(EXIT_FAILURE);
	}

	ret = bind(tfmfd, (struct sockaddr *)sa, sizeof(*sa));
	if (ret == -1) {
		perror("bind");
		exit(EXIT_FAILURE);
	}

	cop->tfmfd = tfmfd;

	return 0;
}

static int alloc_buffer(uint8_t **buf, unsigned int size)
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

static void dump_buffer(FILE *file, char *msg, uint8_t *buf, unsigned int size)
{
	unsigned int i;

	if (msg)
		fprintf(file, "%s \n", msg);

	for (i = 0; i < size; ++i)
		fprintf(file, "%02x", buf[i]);
	fprintf(file, "\n");
}

static void dump_aes_buffer(FILE *file, char *msg, uint8_t *aes_buf, int blocks_no)
{
	int i = 0;

	if (msg)
		fprintf(file, "%s \n", msg);

	for (i = 0; i < blocks_no; ++i) {
		dump_buffer(file, NULL, aes_buf + i * AES_BLOCK_SIZE, AES_BLOCK_SIZE);
	}
	fprintf(file, "\n");
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

static int set_randomized_key(int tfmfd, uint8_t *key, unsigned int keysize)
{
	int ret;

	get_urandom_bytes(key, keysize);
	dump_buffer(stdout, "key: ", key, keysize);
	printf("\n");

	ret = setsockopt(tfmfd, SOL_ALG, ALG_SET_KEY, key, keysize);
	if (ret == -1) {
		perror("setsockopt ALG_SET_KEY");
		exit(EXIT_FAILURE);
	}

	return 0;
}

static struct crypto_op *crypto_op_create(void)
{
	struct crypto_op *cop;

	cop = calloc(1, sizeof(struct crypto_op));
	if (!cop) {
		perror("Cannot allocate space for struct crypto_op!");
		exit(EXIT_FAILURE);
	}

	return cop;
}

static void crypto_op_init(struct crypto_op *cop, size_t iv_size)
{
	size_t cbuf_size;
	uint8_t *cbuf;
	struct cmsghdr *cmsg;

	cbuf_size = CMSG_SPACE(4);
	if (iv_size)
		cbuf_size += CMSG_SPACE(4 + iv_size);
	cbuf = calloc(1, cbuf_size);
	if (!cbuf) {
		perror("Cannot allocate space for cbuf!");
		exit(EXIT_FAILURE);
	}

	cop->msg.msg_control = cbuf;
	cop->msg.msg_controllen = cbuf_size;

	cmsg = CMSG_FIRSTHDR(&cop->msg);
	cmsg->cmsg_level = SOL_ALG;
	cmsg->cmsg_type = ALG_SET_OP;
	cmsg->cmsg_len = CMSG_LEN(4);

	if (iv_size) {
		cmsg = CMSG_NXTHDR(&cop->msg, cmsg);
		cmsg->cmsg_level = SOL_ALG;
		cmsg->cmsg_type = ALG_SET_IV;
		cmsg->cmsg_len = CMSG_LEN(4 + iv_size);
	}

	cop->msg.msg_iov = &cop->iov;
	cop->msg.msg_iovlen = 1;
}

static void crypto_op_finish(struct crypto_op *cop)
{
	close(cop->opfd);
	close(cop->tfmfd);

	free(cop->cbuf);
	free(cop);
}

static int set_random_iv(struct crypto_op *cop, size_t iv_size)
{
	struct af_alg_iv *iv;
	struct cmsghdr *cmsg;

	cmsg = CMSG_FIRSTHDR(&cop->msg);
	cmsg = CMSG_NXTHDR(&cop->msg, cmsg);
	iv = (void *)CMSG_DATA(cmsg);
	iv->ivlen = iv_size;

	get_urandom_bytes(iv->iv, iv_size);
	dump_buffer(stdout, "iv:", iv->iv, iv_size);
	printf("\n");

	return 0;
}

static int encrypt(struct crypto_op *cop, uint8_t *plaintext,
			uint8_t *ciphertext, size_t size)
{
	int ret;
	struct cmsghdr *cmsg;

	cmsg = CMSG_FIRSTHDR(&cop->msg);

	*(__u32 *)CMSG_DATA(cmsg) = ALG_OP_ENCRYPT;
	cop->iov.iov_base = plaintext;
	cop->iov.iov_len = size;

	ret = sendmsg(cop->opfd, &cop->msg, 0);
	if (ret == -1) {
		perror("sendmsg");
		exit(EXIT_FAILURE);
	}

	ret = read(cop->opfd, ciphertext, cop->iov.iov_len);
	if (ret == -1) {
		perror("read");
		exit(EXIT_FAILURE);
	}

	return 0;
}
static int decrypt(struct crypto_op *cop, uint8_t *plaintext,
			uint8_t *ciphertext, size_t size)
{
	int ret;
	struct cmsghdr *cmsg;

	cmsg = CMSG_FIRSTHDR(&cop->msg);

	*(__u32 *)CMSG_DATA(cmsg) = ALG_OP_DECRYPT;
	cop->iov.iov_base = ciphertext;

	ret = sendmsg(cop->opfd, &cop->msg, 0);
	if (ret == -1) {
		perror("sendmsg");
		exit(EXIT_FAILURE);
	}

	memset(plaintext, 0, cop->iov.iov_len);
	ret = read(cop->opfd, plaintext, cop->iov.iov_len);
	if (ret == -1) {
		perror("read");
		exit(EXIT_FAILURE);
	}

	return 0;
}


static int stress(char *alg, unsigned int keysize, int iv_size)
{
	struct sockaddr_alg sa;
	struct crypto_op *cop;

	uint8_t *plaintext_in;
	uint8_t *plaintext_out;
	uint8_t *ciphertext;
	uint8_t *key;

	memset(&sa, 0, sizeof(struct sockaddr_alg));
	sa.salg_family = AF_ALG;
	strncpy((char *)sa.salg_type, "skcipher", 14);
	strncpy((char *)sa.salg_name, alg, 60);

	// Allocate buffers
	alloc_buffer(&plaintext_in, PAYLOAD_SIZE);
	alloc_buffer(&plaintext_out, PAYLOAD_SIZE);
	alloc_buffer(&ciphertext, PAYLOAD_SIZE);
	alloc_buffer(&key, keysize);

	cop = crypto_op_create();
	af_alg_setup(cop, &sa);

	printf("---- Running testcase for %s, %s, %u bytes key ----\n\n",
				(char *)sa.salg_type, (char *)sa.salg_name, keysize);

	set_randomized_key(cop->tfmfd, key, keysize);

	cop->opfd = accept(cop->tfmfd, NULL, 0);
	if (cop->opfd == -1) {
		perror("accept");
		exit(EXIT_FAILURE);
	}

	crypto_op_init(cop, iv_size);
	if (iv_size)
		set_random_iv(cop, AES_IV_SIZE);

	get_urandom_bytes(plaintext_in, PAYLOAD_SIZE);
	dump_aes_buffer(stdout, "plaintext_in:", plaintext_in, PAYLOAD_AES_BLOCKS);

	for (int i = 0; i < ITER_NO; ++i) {
		printf("---- Loop no %d ----\n\n", i);

		encrypt(cop, plaintext_in, ciphertext, PAYLOAD_SIZE);
		dump_aes_buffer(stdout, "ciphertext:", ciphertext, PAYLOAD_AES_BLOCKS);

		decrypt(cop, plaintext_out, ciphertext, PAYLOAD_SIZE);
		dump_aes_buffer(stdout, "plaintext_out:", plaintext_out, PAYLOAD_AES_BLOCKS);

		check_aes_buffers(plaintext_in, plaintext_out, PAYLOAD_AES_BLOCKS);

	}
	printf("PASS!\n\n");

	crypto_op_finish(cop);

	return 0;
}

int main(void)
{
	stress("ecb(aes)", AES_KEY128_SIZE, 0);
	stress("ecb(aes)", AES_KEY256_SIZE, 0);

	stress("cbc(aes)", AES_KEY128_SIZE, AES_IV_SIZE);
	stress("cbc(aes)", AES_KEY256_SIZE, AES_IV_SIZE);

	stress("ctr(aes)", AES_KEY128_SIZE, AES_IV_SIZE);
	stress("ctr(aes)", AES_KEY256_SIZE, AES_IV_SIZE);

	stress("pcbc(aes)", AES_KEY128_SIZE, AES_IV_SIZE);
	stress("pcbc(aes)", AES_KEY256_SIZE, AES_IV_SIZE);

	stress("cfb(aes)", AES_KEY128_SIZE, AES_IV_SIZE);
	stress("cfb(aes)", AES_KEY256_SIZE, AES_IV_SIZE);

	return 0;
}
