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
                if(strncmp(aes_buf_in + i * AES_BLOCK_SIZE,
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

	ret = setsockopt(tfmfd, SOL_ALG, ALG_SET_KEY, key, keysize);
	if (ret == -1) {
		perror("setsockopt ALG_SET_KEY");
		exit(EXIT_FAILURE);
	}

	return 0;
}

static int do_ecb_stress(unsigned int keysize)
{
        int opfd;
        int tfmfd;
        struct sockaddr_alg sa = {
                .salg_family = AF_ALG,
                .salg_type = "skcipher",
                .salg_name = "ecb(aes)"
        };
        struct msghdr msg = {};
        struct cmsghdr *cmsg;
        uint8_t cbuf[CMSG_SPACE(4)] = {0};

        struct iovec iov;

	uint8_t *plaintext_in;
	uint8_t *plaintext_out;
	uint8_t *ciphertext;
	uint8_t *key;

        int ret;

	// Allocate buffers
	plaintext_in = malloc(PAYLOAD_SIZE);
	plaintext_out = malloc(PAYLOAD_SIZE);
	ciphertext = malloc(PAYLOAD_SIZE);
	key = malloc(keysize);
	if (!plaintext_in || !ciphertext || !plaintext_out || !key) {
		perror("Could not allocate buffers!");
		exit(EXIT_FAILURE);
	}

        // Setup AF_ALG socket
        tfmfd = socket(AF_ALG, SOCK_SEQPACKET, 0);
        if (tfmfd == -1) {
                perror("socket");
                exit(EXIT_FAILURE);
        }

        ret = bind(tfmfd, (struct sockaddr *)&sa, sizeof(sa));
        if (ret == -1) {
                perror("bind");
                exit(EXIT_FAILURE);
        }

	set_randomized_key(tfmfd, key, keysize);

        opfd = accept(tfmfd, NULL, 0);
        if (opfd == -1) {
                perror("accept");
                exit(EXIT_FAILURE);
        }

        msg.msg_control = cbuf;
        msg.msg_controllen = sizeof(cbuf);

        cmsg = CMSG_FIRSTHDR(&msg);
        cmsg->cmsg_level = SOL_ALG;
        cmsg->cmsg_type = ALG_SET_OP;
        cmsg->cmsg_len = CMSG_LEN(4);

        msg.msg_iov = &iov;
        msg.msg_iovlen = 1;

        iov.iov_len = PAYLOAD_SIZE;

	get_urandom_bytes(plaintext_in, PAYLOAD_SIZE);
	dump_aes_buffer(stdout, "plaintext_in:", plaintext_in, PAYLOAD_AES_BLOCKS);

        for (int i = 0; i < ITER_NO; ++i) {
                printf("Iteration no.: %d\n\n", i);
                // Encrypt
                *(__u32 *)CMSG_DATA(cmsg) = ALG_OP_ENCRYPT;
                iov.iov_base = plaintext_in;

                ret = sendmsg(opfd, &msg, 0);
                if (ret == -1) {
                        perror("sendmsg");
                        exit(EXIT_FAILURE);
                }

                memset(ciphertext, 0, iov.iov_len);
                ret = read(opfd, ciphertext, iov.iov_len);
                if (ret == -1) {
                        perror("read");
                        exit(EXIT_FAILURE);
                }

                dump_aes_buffer(stdout, "ciphertext:", ciphertext, PAYLOAD_AES_BLOCKS);

                // Decrypt
                *(__u32 *)CMSG_DATA(cmsg) = ALG_OP_DECRYPT;
                iov.iov_base = ciphertext;

                ret = sendmsg(opfd, &msg, 0);
                if (ret == -1) {
                        perror("sendmsg");
                        exit(EXIT_FAILURE);
                }

                memset(plaintext_out, 0, iov.iov_len);
                ret = read(opfd, plaintext_out, iov.iov_len);
                if (ret == -1) {
                        perror("read");
                        exit(EXIT_FAILURE);
                }

                dump_aes_buffer(stdout, "plaintext_out:", plaintext_out, PAYLOAD_AES_BLOCKS);
                check_aes_buffers(plaintext_in, plaintext_out, PAYLOAD_AES_BLOCKS);

        }
        printf("Great success! All blocks match!\n");

        close(opfd);
        close(tfmfd);

        return 0;
}

static int do_cbc_stress(unsigned int keysize)
{
        int opfd;
        int tfmfd;
        struct sockaddr_alg sa = {
                .salg_family = AF_ALG,
                .salg_type = "skcipher",
                .salg_name = "cbc(aes)"
        };
        struct msghdr msg = {};
        struct cmsghdr *cmsg;
        uint8_t cbuf[CMSG_SPACE(4) + CMSG_SPACE(20)] = {0};

        struct af_alg_iv *iv; // init vector needed for CBC
        struct iovec iov;

	uint8_t *plaintext_in;
	uint8_t *plaintext_out;
	uint8_t *ciphertext;
	uint8_t *key;

        int ret;

        // Allocate buffers
        plaintext_in = malloc(PAYLOAD_SIZE);
        plaintext_out = malloc(PAYLOAD_SIZE);
        ciphertext = malloc(PAYLOAD_SIZE);
        key = malloc(keysize);
        if (!plaintext_in || !ciphertext || !plaintext_out || !key) {
                perror("Could not allocate buffers!");
                exit(EXIT_FAILURE);
        }

        // Setup AF_ALG socket
        tfmfd = socket(AF_ALG, SOCK_SEQPACKET, 0);

        if (tfmfd == -1) {
                perror("socket");
                exit(EXIT_FAILURE);
        }

        ret = bind(tfmfd, (struct sockaddr *)&sa, sizeof(sa));
        if (ret == -1) {
                perror("bind");
                exit(EXIT_FAILURE);
        }

	set_randomized_key(tfmfd, key, keysize);

        opfd = accept(tfmfd, NULL, 0);
        if (opfd == -1) {
                perror("accept");
                exit(EXIT_FAILURE);
        }

        msg.msg_control = cbuf;
        msg.msg_controllen = sizeof(cbuf);

        cmsg = CMSG_FIRSTHDR(&msg);
        cmsg->cmsg_level = SOL_ALG;
        cmsg->cmsg_type = ALG_SET_OP;
        cmsg->cmsg_len = CMSG_LEN(4);

        cmsg = CMSG_NXTHDR(&msg, cmsg);
        cmsg->cmsg_level = SOL_ALG;
        cmsg->cmsg_type = ALG_SET_IV;
	cmsg->cmsg_len = CMSG_LEN(4 + AES_IV_SIZE);
	iv = (void *)CMSG_DATA(cmsg);
	iv->ivlen = AES_IV_SIZE;
	get_urandom_bytes(iv->iv, AES_IV_SIZE);
	dump_buffer(stdout, "iv:", iv->iv, AES_IV_SIZE);

        cmsg = CMSG_FIRSTHDR(&msg);

        msg.msg_iov = &iov;
        msg.msg_iovlen = 1;

	iov.iov_len = PAYLOAD_SIZE;

	get_urandom_bytes(plaintext_in, PAYLOAD_SIZE);
	dump_aes_buffer(stdout, "plaintext_in:", plaintext_in, PAYLOAD_AES_BLOCKS);

        for (int i = 0; i < ITER_NO; ++i) {
                printf("Iteration no.: %d\n\n", i);
                // Encrypt
                *(__u32 *)CMSG_DATA(cmsg) = ALG_OP_ENCRYPT;
                iov.iov_base = plaintext_in;

                ret = sendmsg(opfd, &msg, 0);
                if (ret == -1) {
                        perror("sendmsg");
                        exit(EXIT_FAILURE);
                }

                memset(ciphertext, 0, iov.iov_len);
                ret = read(opfd, ciphertext, iov.iov_len);
                if (ret == -1) {
                        perror("read");
                        exit(EXIT_FAILURE);
                }

                dump_aes_buffer(stdout, "ciphertext:", ciphertext, PAYLOAD_AES_BLOCKS);

                // Decrypt
                *(__u32 *)CMSG_DATA(cmsg) = ALG_OP_DECRYPT;
                iov.iov_base = ciphertext;

                ret = sendmsg(opfd, &msg, 0);
                if (ret == -1) {
                        perror("sendmsg");
                        exit(EXIT_FAILURE);
                }

                memset(plaintext_out, 0, iov.iov_len);
                ret = read(opfd, plaintext_out, iov.iov_len);
                if (ret == -1) {
                        perror("read");
                        exit(EXIT_FAILURE);
                }

                dump_aes_buffer(stdout, "plaintext_out:", plaintext_out, PAYLOAD_AES_BLOCKS);
                check_aes_buffers(plaintext_in, plaintext_out, PAYLOAD_AES_BLOCKS);

        }
        printf("Great success! All blocks match!\n");

        close(opfd);
        close(tfmfd);

        return 0;
}

int main(void)
{
	do_ecb_stress(AES_KEY128_SIZE);
	do_cbc_stress(AES_KEY128_SIZE);

	do_ecb_stress(AES_KEY256_SIZE);
	do_cbc_stress(AES_KEY256_SIZE);

	return 0;
}
