#include <stdio.h>
#include <stdint.h>

#include "aes.h"

// Populate state 2D array
static void plaintext_to_state(state_t state, uint8_t *plaintext)
{
	int row, col;
	int plaintext_i;

	for (col = 0, plaintext_i = 0; col < Nb; ++col) {
		for (row = 0; row < Nb; ++row, ++plaintext_i) {
			state[row][col] = plaintext[plaintext_i];
		}
	}

	#ifdef DEBUG
	dbg_state(__func__, state);
	#endif
}

static void state_to_ciphertext(state_t state, uint8_t *ciphertext)
{
	int row, col;
	int ciphertext_i;

	for (col = 0, ciphertext_i = 0; col < Nb; ++col) {
		for (row = 0; row < Nb; ++row, ++ciphertext_i) {
			ciphertext[ciphertext_i] = state[row][col];
		}
	}
}

// Substitute bytes
static void sub_bytes(state_t state)
{
	int row, col;

	for (row = 0; row < Nb; ++row) {
		for (col = 0; col < Nb; ++col) {
			state[row][col] = get_sbox(state[row][col]);
		}
	}

	#ifdef DEBUG
	dbg_state(__func__, state);
	#endif
}

// Shift rows
static void shift_rows(state_t state)
{
	uint8_t temp;

	// Rotate first row 1 columns to left
	temp        = state[1][0];
	state[1][0] = state[1][1];
	state[1][1] = state[1][2];
	state[1][2] = state[1][3];
	state[1][3] = temp;

	// Rotate second row 2 columns to left
	temp        = state[2][0];
	state[2][0] = state[2][2];
	state[2][2] = temp;

	temp        = state[2][1];
	state[2][1] = state[2][3];
	state[2][3] = temp;

	// Rotate third row 3 columns to left
	temp        = state[3][0];
	state[3][0] = state[3][3];
	state[3][3] = state[3][2];
	state[3][2] = state[3][1];
	state[3][1] = temp;

	#ifdef DEBUG
	dbg_state(__func__, state);
	#endif
}

// Mix columns
static inline uint8_t mul2(uint8_t op)
{
	return ((op << 1) ^ (((op >> 7) & 1) * 0x1b));
}

static inline uint8_t mul3(uint8_t op)
{
	return mul2(op) ^ op;
}

/*
 * --         --     --             --
 * |02 03 01 01|     |s00 s01 s02 s03|
 * |01 02 03 01|     |s10 s11 s12 s13|
 * |01 01 02 03|  X  |s20 s21 s22 s23|
 * |03 01 01 02|     |s30 s31 s32 s33|
 * --          -     --             --
 */
static void mix_columns(state_t state)
{
	int col;
	uint8_t tmp[Nb];

	for (col = 0; col < Nb; ++col) {
		tmp[0] = state[0][col];
		tmp[1] = state[1][col];
		tmp[2] = state[2][col];
		tmp[3] = state[3][col];

		state[0][col] = mul2(tmp[0]) ^ mul3(tmp[1]) ^ tmp[2] ^ tmp[3];
		state[1][col] = tmp[0] ^ mul2(tmp[1]) ^ mul3(tmp[2]) ^tmp[3];
		state[2][col] = tmp[0] ^ tmp[1] ^ mul2(tmp[2]) ^ mul3(tmp[3]);
		state[3][col] = mul3(tmp[0]) ^ tmp[1] ^ tmp[2] ^mul2(tmp[3]);
	}

	#ifdef DEBUG
	dbg_state(__func__, state);
	#endif
}

void cipher(uint8_t *plaintext, uint8_t *ciphertext, uint8_t *sched)
{
	int round;
	state_t state;

	plaintext_to_state(state, plaintext);

	// cipher round 0
	add_round_key(state, sched);

	// rounds 1 -> Nr - 1
	for (round = 1; round < Nr; ++round) {
		sub_bytes(state);
		shift_rows(state);
		mix_columns(state);
		add_round_key(state, sched + (round * Nb * 4));
	}

	// last round
	sub_bytes(state);
	shift_rows(state);
	add_round_key(state, sched + (round * Nb * 4));

	state_to_ciphertext(state, ciphertext);
}
