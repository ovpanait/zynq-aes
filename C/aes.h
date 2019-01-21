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

#endif
