#include <stdio.h>
#include <stdint.h>

#include "aes.h"


// Populate state 2D array
static void to_state(state_t state, uint8_t *key)
{
	int row, col;
	int key_i;

	for (col = 0, key_i = 0; col < Nb; ++col) {
		for (row = 0; row < Nb; ++row, ++key_i) {
			state[row][col] = key[key_i];
		}
	}
}

static void print_state(state_t state)
{
	int row, col;

	printf("\n");
	for (row = 0; row < Nb; ++row) {
		for (col = 0; col < Nb; ++col) {
			printf("%02X ", state[row][col]);
		}
		printf("\n");
	}
}

#ifdef DEBUG
int main(int argc, char **argv)
{
	state_t state;

	uint8_t key[Nb * Nk] = {
		0x54, 0x68, 0x61, 0x74,
		0x73, 0x20, 0x6D, 0x79,
		0x20, 0x4B, 0x75, 0x6E,
		0x67, 0x20, 0x46, 0x75
	};

	to_state(state, key);
	print_state(state);
}
#endif
