#include <stdio.h>
#include <unistd.h>
#include <sys/socket.h>
#include <linux/if_alg.h>
#include <linux/socket.h>
#include <string.h>
#include <stdlib.h>

#include <stdint.h>
#include <assert.h>

#ifndef SOL_ALG
#define SOL_ALG 279
#endif

#define AES_BLOCK_SIZE 16

#define ITER_NO 100
#define PAYLOAD_AES_BLOCKS 555
#define PAYLOAD_SIZE (AES_BLOCK_SIZE * PAYLOAD_AES_BLOCKS)

static void dump_aes_buffer(char *msg, char *aes_buf, int blocks_no)
{
        int i =0, j = 0;

	printf("%s \n", msg);
	for (i = 0; i < blocks_no; ++i) {
                for (j = 0; j < AES_BLOCK_SIZE; ++j)
		        printf("%02x", aes_buf[i * AES_BLOCK_SIZE + j]);
	        printf("\n");
        }
        printf("\n");
}

static void check_aes_buffers(char *aes_buf_in, char *aes_buf_out, int blocks_no)
{
        int i =0;

	for (i = 0; i < blocks_no; ++i) {
                assert(strncmp(aes_buf_in + i * AES_BLOCK_SIZE,
                        aes_buf_out + i * AES_BLOCK_SIZE, AES_BLOCK_SIZE) == 0);
        }
}

int main(void)
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
        char cbuf[CMSG_SPACE(4)] = {0};

        struct iovec iov;

        int ret;

        // Allocate buffers
	char *plaintext_in = malloc(PAYLOAD_SIZE + 1);
	char *plaintext_out = malloc(PAYLOAD_SIZE + 1);
	char *ciphertext = malloc(PAYLOAD_SIZE + 1);
	if (plaintext_in == NULL || ciphertext == NULL || plaintext_out == NULL) {
		perror("Could not allocate buffers!");
		exit(EXIT_FAILURE);
	}

	ciphertext[PAYLOAD_SIZE - 1] = '\0';
	plaintext_out[PAYLOAD_SIZE - 1] = '\0';

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

        ret = setsockopt(tfmfd, SOL_ALG, ALG_SET_KEY,
                        "\x54\x68\x61\x74"
                        "\x73\x20\x6D\x79"
                        "\x20\x4B\x75\x6E"
                        "\x67\x20\x46\x75", 16);
        if (ret == -1) {
                perror("setsockopt ALG_SET_KEY");
                exit(EXIT_FAILURE);
        }

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

        iov.iov_len = 0;

        // Setup input plaintext
	for (int i = 0; i < PAYLOAD_AES_BLOCKS; ++i) {
		sprintf(plaintext_in + iov.iov_len, "Single bloc%05d", i);
		iov.iov_len += AES_BLOCK_SIZE;
        }
        assert(iov.iov_len == PAYLOAD_SIZE);

        dump_aes_buffer("plaintext_in:", plaintext_in, PAYLOAD_AES_BLOCKS);

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

                dump_aes_buffer("ciphertext:", ciphertext, PAYLOAD_AES_BLOCKS);

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

                dump_aes_buffer("plaintext_out:", plaintext_out, PAYLOAD_AES_BLOCKS);
                check_aes_buffers(plaintext_in, plaintext_out, PAYLOAD_AES_BLOCKS);

        }
        printf("Great success! All blocks match!\n");

        close(opfd);
        close(tfmfd);

        return 0;
}
