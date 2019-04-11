#include <stdio.h>
#include <stdint.h>
#include <string.h>

#include "aes.h"

int main(int argc, char **argv)
{
	int i;
	uint8_t ciphertext[AES_BLK_BYTE_CNT];
	uint8_t sched[(Nb * (Nr + 1)) * Nb];

	uint8_t key[AES128_KEY_BYTE_CNT] = {
		0x54, 0x68, 0x61, 0x74,
		0x73, 0x20, 0x6D, 0x79,
		0x20, 0x4B, 0x75, 0x6E,
		0x67, 0x20, 0x46, 0x75
	};

	uint8_t plaintext[AES_BLK_BYTE_CNT] = {
		0x54, 0x77, 0x6F, 0x20,
		0x4F, 0x6E, 0x65, 0x20,
		0x4E, 0x69, 0x6E, 0x65,
		0x20, 0x54, 0x77, 0x6F
	};

	key_expansion(sched, key);
	cipher(plaintext, ciphertext, sched);

	printf("key:\n");
	for (i = 0; i < AES128_KEY_BYTE_CNT; ++i)
		printf("%02x", key[i]);
	printf("\n\n");

	printf("Encrypting..\n");
	printf("plaintext:\n");
	for (i = 0; i < AES_BLK_BYTE_CNT; ++i)
		printf("%02x", plaintext[i]);
	printf("\n\n");

	printf("ciphertext:\n");
	for (i = 0; i < AES_BLK_BYTE_CNT; ++i)
		printf("%02x", ciphertext[i]);
	printf("\n\n");

	printf("Decrypting..\n");
	printf("ciphertext:\n");
	for (i = 0; i < AES_BLK_BYTE_CNT; ++i)
		printf("%02x", ciphertext[i]);
	printf("\n\n");

	memset(plaintext, 0x0, AES_BLK_BYTE_CNT);
	decipher(ciphertext, plaintext, sched);

	printf("plaintext:\n");
	for (i = 0; i < AES_BLK_BYTE_CNT; ++i)
		printf("%02x", plaintext[i]);
	printf("\n\n");

	return 0;
}
