#ifndef AES_H
#define AES_H

#include <stdio.h>
#include <stdint.h>

#define Nb 4

#ifdef AES_256
	#define Nk 8
	#define Nr 14
#else
	#define Nk 4
	#define Nr 10
#endif

#define AES_KEYSIZE      (Nk * 4)
#define AES_BLOCK_SIZE   (Nb * 4)
#define ROUND_KEY_SIZE   AES_BLOCK_SIZE

#define get_sbox(x) (sbox[(x)])
extern const uint8_t sbox[256];

typedef uint8_t state_t[Nb][Nb];

void key_expansion(uint8_t *sched, uint8_t *key);
void cipher(uint8_t *plaintext, uint8_t *cipher, uint8_t *sched);
void decipher(uint8_t *ciphertext, uint8_t *plaintext, uint8_t *sched);

void add_round_key(state_t state, uint8_t *key);

#ifdef DEBUG
void dbg_state(const char *dbg_msg, state_t state);
#endif

#endif
