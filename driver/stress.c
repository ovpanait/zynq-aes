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
	iov.iov_len = 16;

	char *plaintext_in = malloc(17);
	char *plaintext_out = malloc(17);
	char *ciphertext = malloc(17);
	if (plaintext_in == NULL || ciphertext == NULL || plaintext_out == NULL) {
		perror("Could not allocate buf");
		exit(EXIT_FAILURE);
	}

	ciphertext[16] = '\0';
	plaintext_out[16] = '\0';

	for (int i = 0; i < 10000; ++i) {
		// Encrypt
		sprintf(plaintext_in, "Single bloc%05d", i);
		assert(strlen(plaintext_in) == 16);

		printf("%s\n", plaintext_in);
		printf("plaintext_in: ");
		for (int i = 0; i < 16; i++) {
			printf("%02x", (unsigned char)plaintext_in[i]);
		}
		printf("\n");

		*(__u32 *)CMSG_DATA(cmsg) = ALG_OP_ENCRYPT;
		iov.iov_base = plaintext_in;

		ret = sendmsg(opfd, &msg, 0);
		if (ret == -1) {
			perror("sendmsg");
			exit(EXIT_FAILURE);
		}

		ret = read(opfd, ciphertext, 16);
		if (ret == -1) {
			perror("read");
			exit(EXIT_FAILURE);
		}
		
		printf("ciphertext: ");
		for (int i = 0; i < 16; i++) {
			printf("%02x", (unsigned char)ciphertext[i]);
		}
		printf("\n");

		// Decrypt
		*(__u32 *)CMSG_DATA(cmsg) = ALG_OP_DECRYPT;
		iov.iov_base = ciphertext;

		ret = sendmsg(opfd, &msg, 0);
		if (ret == -1) {
			perror("sendmsg");
			exit(EXIT_FAILURE);
		}

		ret = read(opfd, plaintext_out, 16);
		if (ret == -1) {
			perror("read");
			exit(EXIT_FAILURE);
		}

		printf("plaintext_out: ");
		for (int i = 0; i < 16; i++) {
			printf("%02x", (unsigned char)plaintext_out[i]);
		}
		printf("\n");
		
		assert(strncmp(plaintext_in, plaintext_out, 16) == 0);
	}
        close(opfd);
        close(tfmfd);

        return 0;
}
