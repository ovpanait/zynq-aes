/*
 * Shared functions used by multiple processing stages.
 */

#include "aes.h"

#ifdef DEBUG
void dbg_state(const char *dbg_msg, state_t state)
{
	int row, col;

	printf("%s:\n", dbg_msg);
	for (row = 0; row < Nb; ++row) {
		for (col = 0; col < Nb; ++col) {
			printf("%02X ", state[row][col]);
		}
		printf("\n");
	}
	printf("\n");
}
#endif

void add_round_key(state_t state, uint8_t *key)
{
	int row, col;
	int key_i;

	for (col = 0, key_i = 0; col < Nb; ++col) {
		for (row = 0; row < Nb; ++row, ++key_i) {
			state[row][col] ^= key[key_i];
		}
	}

	#ifdef DEBUG
	dbg_state(__func__, state);
	#endif
}
