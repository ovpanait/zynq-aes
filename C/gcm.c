#include <limits.h>
#include <string.h>

#include "aes.h"
#include "test.h"

#define BYTES_128BIT (128 / CHAR_BIT)

#define BIT0(val) (((val) & (1 << 0)) >> 0)
#define BIT7(val) (((val) & (1 << 7)) >> 7)

static void xor128(uint8_t *dest, const uint8_t *src)
{
	size_t i;

#ifdef DEBUG
	dump_buffer_bits(dest, BYTES_128BIT, "xor128 - before: ");
#endif

	for (i = 0; i < BYTES_128BIT; ++i) {
		dest[i] ^= src[i];
	}

#ifdef DEBUG
	dump_buffer_bits(dest, BYTES_128BIT, "xor128 - after : ");
#endif
}

static void shl128(uint8_t *data)
{
	size_t i;

#ifdef DEBUG
	dump_buffer_bits(data, BYTES_128BIT, "shl128 - before: ");
#endif

	for (i = 0; i < BYTES_128BIT - 1; ++i) {
		data[i] <<= 1;
		data[i] |= BIT7(data[i+1]);
	}

	data[i] <<= 1;

#ifdef DEBUG
	dump_buffer_bits(data, BYTES_128BIT, "shl128 - after : ");
#endif
}

static void shr128(uint8_t *data)
{
	size_t i;

#ifdef DEBUG
	dump_buffer_bits(data, BYTES_128BIT, "shr128 - before: ");
#endif

	for (i = BYTES_128BIT - 1; i >= 1; --i) {
		data[i] >>= 1;
		data[i] |= BIT0(data[i-1]) << 7;
	}

	data[i] >>= 1;

#ifdef DEBUG
	dump_buffer_bits(data, BYTES_128BIT, "shr128 - after : ");
#endif
}

static void gcm_gf_mult(uint8_t *a, uint8_t *b, uint8_t *result)
{
	size_t i;
	uint8_t a0;
	uint8_t polynomial[16] = {
		0x00, 0x00, 0x00, 0x00,
		0x00, 0x00, 0x00, 0x00,
		0x00, 0x00, 0x00, 0x00,
		0x00, 0x00, 0x00, 0x87
	};

	memset(result, 0, BYTES_128BIT);

	for (i = 0; i < 128; ++i) {
		a0 = BIT7(a[0]);

		if (BIT0(b[BYTES_128BIT - 1]))
			xor128(result, a);

		shl128(a);
		if (a0)
			xor128(a, polynomial);

		shr128(b);
	}
}

int main(int agrc, char **argv)
{
	uint8_t a[16] = {0x7b, 0x5b, 0x54, 0x65, 0x73, 0x74, 0x56, 0x65, 0x63, 0x74, 0x6f, 0x72, 0x5d, 0x53, 0x47, 0x5d};
	uint8_t b[16] = {0x48, 0x69, 0x28, 0x53, 0x68, 0x61, 0x79, 0x29, 0x5b, 0x47, 0x75, 0x65, 0x72, 0x6f, 0x6e, 0x5d};

	uint8_t result[16];

	gcm_gf_mult(a, b, result);
	dump_buffer(result, 16, "result: ");
}

