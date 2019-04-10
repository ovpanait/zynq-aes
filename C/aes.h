#ifndef AES_H
#define AES_H

#define Nk 4
#define Nr 10
#define Nb 4

#define AES128_KEY_BYTE_CNT (128 / 8)
#define AES_BLK_BYTE_CNT (128 / 8)

#define get_sbox(x) (sbox[(x)])
extern const uint8_t sbox[256];

typedef uint8_t state_t[Nb][Nb];

void key_expansion(uint8_t *sched, uint8_t *key);
void cipher(uint8_t *plaintext, uint8_t *sched, uint8_t *cipher);

#ifdef DEBUG
static void dbg_state(const char *dbg_msg, state_t state)
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

static void add_round_key(state_t state, uint8_t *key)
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

#endif
