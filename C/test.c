#include <stdio.h>
#include <stdint.h>
#include <string.h>

#include "aes.h"

static void dump_buffer(uint8_t *buf, unsigned int len, char *dbg)
{
	unsigned int i;

	if (dbg)
		printf("%s\n", dbg);

	for (i = 0; i < len; ++i)
		printf("%02x", buf[i]);

	printf("\n\n");
}

void test_crypto(void)
{
	uint8_t ciphertext[AES_BLOCK_SIZE];
	uint8_t sched[(Nb * (Nr + 1)) * Nb];

	uint8_t plaintext[AES_BLOCK_SIZE] = {
		0x54, 0x77, 0x6F, 0x20,
		0x4F, 0x6E, 0x65, 0x20,
		0x4E, 0x69, 0x6E, 0x65,
		0x20, 0x54, 0x77, 0x6F
	};

#ifdef AES_256
	uint8_t key[AES_KEYSIZE] = {
		0x54, 0x68, 0x61, 0x74,
		0x73, 0x20, 0x6D, 0x79,
		0x20, 0x4B, 0x75, 0x6E,
		0x67, 0x20, 0x46, 0x75,
		0x54, 0x68, 0x61, 0x74,
		0x73, 0x20, 0x6D, 0x79,
		0x20, 0x4B, 0x75, 0x6E,
		0x67, 0x20, 0x46, 0x75
	};
#else
	uint8_t key[AES_KEYSIZE] = {
		0x54, 0x68, 0x61, 0x74,
		0x73, 0x20, 0x6D, 0x79,
		0x20, 0x4B, 0x75, 0x6E,
		0x67, 0x20, 0x46, 0x75
	};
#endif

	dump_buffer(key, AES_KEYSIZE, "key:");
	key_expansion(sched, key);

	printf("Encrypting..\n");
	dump_buffer(plaintext, AES_BLOCK_SIZE, "plaintext:");
	cipher(plaintext, ciphertext, sched);
	dump_buffer(ciphertext, AES_BLOCK_SIZE, "ciphertext:");

	printf("Decrypting..\n");
	dump_buffer(ciphertext, AES_BLOCK_SIZE, "ciphertext:");
	memset(plaintext, 0x0, AES_BLOCK_SIZE);
	decipher(ciphertext, plaintext, sched);
	dump_buffer(plaintext, AES_BLOCK_SIZE, "plaintext:");
}

int main(int argc, char **argv)
{
	test_crypto();

	return 0;
}
