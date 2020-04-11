/*
 * AES GCM implementation used as reference for debugging Verilog design.
 * Still incomplete:
 *     - IV size limited to 96 bits
 *     - missing support for 192/256-bit AES operations
 *     - probably other things that I can't remember right now
 *
 * AES GCM references:
 * https://luca-giuzzi.unibs.it/corsi/Support/papers-cryptography/gcm-spec.pdf
 * https://nvlpubs.nist.gov/nistpubs/Legacy/SP/nistspecialpublication800-38d.pdf
*/

#include <limits.h>
#include <string.h>
#include <endian.h>

#include "aes.h"
#include "test.h"

#define BYTES_128BIT (128 / CHAR_BIT)

#define BIT0(val) (((val) & (1 << 0)) >> 0)
#define BIT7(val) (((val) & (1 << 7)) >> 7)

#define BLOCK_SIZE  AES_BLOCK_SIZE
#define KEY_SIZE    AES_KEYSIZE
#define IV_SIZE     12

static void xor128(uint8_t *dest, const uint8_t *src)
{
	size_t i;

	for (i = 0; i < BYTES_128BIT; ++i) {
		dest[i] ^= src[i];
	}
}

static void shl128(uint8_t *data)
{
	size_t i;

	for (i = 0; i < BYTES_128BIT - 1; ++i) {
		data[i] <<= 1;
		data[i] |= BIT7(data[i+1]);
	}

	data[i] <<= 1;
}

static void shr128(uint8_t *data)
{
	size_t i;

	for (i = BYTES_128BIT - 1; i >= 1; --i) {
		data[i] >>= 1;
		data[i] |= BIT0(data[i-1]) << 7;
	}

	data[i] >>= 1;
}

static void inc32(uint8_t *ptr)
{
	uint32_t val = htobe32(*(uint32_t *)ptr);
	val += 1;
	val = htobe32(val);
	memcpy(ptr, &val, sizeof(uint32_t));
}

/*
 * NOTE:
 * GCM does not treat input blocks as MSB <--- LSB. Instead, it treats
 * them as LSB ---> MSB, so shifts and polynomial need to be reversed.
 */
static void gcm_gf_mult(uint8_t *op1, uint8_t *op2, uint8_t *result)
{
	uint8_t a[BYTES_128BIT];
	uint8_t b[BYTES_128BIT];
	uint8_t polynomial[16] = {
		0xe1, 0x00, 0x00, 0x00,
		0x00, 0x00, 0x00, 0x00,
		0x00, 0x00, 0x00, 0x00,
		0x00, 0x00, 0x00, 0x00
	};
	uint8_t a0;
	size_t i;

	memset(result, 0, BYTES_128BIT);
	memcpy(a, op1, BYTES_128BIT);
	memcpy(b, op2, BYTES_128BIT);

	for (i = 0; i < 128; ++i) {
		a0 = BIT0(a[BYTES_128BIT - 1]);

		if (BIT7(b[0]))
			xor128(result, a);

		shr128(a);
		if (a0)
			xor128(a, polynomial);

		shl128(b);
	}
}

static void gctr(uint8_t *key_sched, uint8_t *icb, uint8_t *indata,
		uint64_t indata_len, uint8_t *outdata)
{
	size_t i;
	uint64_t blocks_no = indata_len / BLOCK_SIZE;

	for (i = 0; i < blocks_no; ++i) {
		cipher(icb, outdata, key_sched);
		xor128(outdata, indata);

		outdata += BLOCK_SIZE;
		indata += BLOCK_SIZE;

		inc32(icb + (BLOCK_SIZE - sizeof(uint32_t)));
	}
}

static void gcm_ghash(uint8_t *subkey_H, uint8_t *data, uint64_t data_len,
		uint8_t *ghash)
{
	uint8_t ghash_next[BLOCK_SIZE];
	uint64_t i;
	uint64_t blocks_no = data_len / BLOCK_SIZE;

	// -> GHASH(0) = {128{0}} (128 bits of 0)
	// -> for each block in data:
	// ->     GHASH(i) = (GHASH(i-1) ^ data(i)) * subkey_H
	for (i = 0; i < blocks_no; ++i) {
		xor128(ghash, data);
		gcm_gf_mult(ghash, subkey_H, ghash_next);
		memcpy(ghash, ghash_next, BLOCK_SIZE);

		data += BLOCK_SIZE;
	}
}

static void gcm_tag(uint8_t *key_sched, uint8_t *j0,
		uint8_t *ciphertext, uint64_t ciphertext_len,
		uint8_t *aad, uint64_t aad_len,
		uint8_t *tag)
{
	uint8_t subkey_H[BLOCK_SIZE];
	uint8_t ghash_extra[BLOCK_SIZE];
	uint8_t ghash[BLOCK_SIZE];

	// Assemble [len(A)[64] || len(C)[64]] block needed by ghash
	// TODO - check for overflow
	uint64_t ciphertext_bits = ciphertext_len * 8; // len(A) in bits
	uint64_t aad_bits = aad_len * 8;               // len(C) in bits

	ciphertext_bits = htobe64(ciphertext_bits);
	aad_bits = htobe64(aad_bits);
	memcpy(ghash_extra, &aad_bits, sizeof(uint64_t));
	memcpy(ghash_extra + sizeof(uint64_t), &ciphertext_bits, sizeof(uint64_t));

	// Encrypt a full block of 0s to obtain the subkey H used by GHASH
	memset(ghash, 0, BLOCK_SIZE);
	cipher(ghash, subkey_H, key_sched);

	// GHASH(H, A, C, len(A) || len(C))
	gcm_ghash(subkey_H, aad, aad_len, ghash);
	gcm_ghash(subkey_H, ciphertext, ciphertext_len, ghash);
	gcm_ghash(subkey_H, ghash_extra, BLOCK_SIZE, ghash);

	// Tag = MSB[t](GCTR(J0, GHASH))
	// Tag = Most t significant bits of GCTR(J0, GHASH)
	gctr(key_sched, j0, ghash, BLOCK_SIZE, tag);
}

static void aes_gcm(uint8_t *key, uint8_t *iv, uint64_t iv_len,
				uint8_t *indata, uint64_t indata_len,
				uint8_t *aad, uint64_t aad_len,
				uint8_t *tag, uint8_t *outdata)
{
	uint8_t key_sched[(Nb * (Nr + 1)) * Nb];
	uint8_t crypto_icb[BLOCK_SIZE];
	uint8_t j0[BLOCK_SIZE];

	if (iv_len == IV_SIZE) {
		uint8_t iv_padding[4] = {0x00, 0x00, 0x00, 0x01};

		memcpy(j0, iv, IV_SIZE);
		memcpy(j0 + IV_SIZE, iv_padding, 4);
	}

	memcpy(crypto_icb, j0, BLOCK_SIZE);
	inc32(crypto_icb + (BLOCK_SIZE - sizeof(uint32_t)));

	key_expansion(key_sched, key);
	// Compute C
	gctr(key_sched, crypto_icb, indata, indata_len, outdata);
	// Compute Tag
	gcm_tag(key_sched, j0, outdata, indata_len, aad, aad_len, tag);
}

int main(int argc, char **argv)
{
	uint8_t tag[BLOCK_SIZE];

/*
	[Keylen = 128]
	[IVlen = 96]
	[PTlen = 128]
	[AADlen = 0]
	[Taglen = 128]

	K  = 00000000000000000000000000000000
	P  = 00000000000000000000000000000000
	IV = 000000000000000000000000

	C  = 0388dace60b6a392f328c2b971b2fe78
	T  = ab6e47d42cec13bdf53a67b21257bddf
*/
/*
	uint8_t key[KEY_SIZE] = {
		0x00, 0x00, 0x00, 0x00,
		0x00, 0x00, 0x00, 0x00,
		0x00, 0x00, 0x00, 0x00,
		0x00, 0x00, 0x00, 0x00
	};
	uint8_t iv[12] = {
		0x00, 0x00, 0x00, 0x00,
		0x00, 0x00, 0x00, 0x00,
		0x00, 0x00, 0x00, 0x00
	};
	uint8_t indata[BLOCK_SIZE] = {
		0x00, 0x00, 0x00, 0x00,
		0x00, 0x00, 0x00, 0x00,
		0x00, 0x00, 0x00, 0x00,
		0x00, 0x00, 0x00, 0x00
	};
	uint64_t indata_blocks = 1;

	uint8_t *aad = NULL;
	uint64_t aad_blocks = 0;

	uint8_t outdata[BLOCK_SIZE];
*/

/*
	[Keylen = 128]
	[IVlen = 96]
	[PTlen = 512]
	[AADlen = 0]
	[Taglen = 128]

	K  = feffe9928665731c6d6a8f9467308308
	P  = d9313225f88406e5a55909c5aff5269a
	     86a7a9531534f7da2e4c303d8a318a72
	     1c3c0c95956809532fcf0e2449a6b525
	     b16aedf5aa0de657ba637b391aafd255
	IV = cafebabefacedbaddecaf888

	C  = 42831ec2217774244b7221b784d0d49c
	     e3aa212f2c02a4e035c17e2329aca12e
	     21d514b25466931c7d8f6a5aac84aa05
	     1ba30b396a0aac973d58e091473f5985
	T  = 4d5c2af327cd64a62cf35abd2ba6fab4
*/
/*
	uint8_t key[KEY_SIZE] = {
		0xfe, 0xff, 0xe9, 0x92,
		0x86, 0x65, 0x73, 0x1c,
		0x6d, 0x6a, 0x8f, 0x94,
		0x67, 0x30, 0x83, 0x08
	};
	uint8_t iv[IV_SIZE] = {
		0xca, 0xfe, 0xba, 0xbe,
		0xfa, 0xce, 0xdb, 0xad,
		0xde, 0xca, 0xf8, 0x88
	};
	uint8_t indata[4 * BLOCK_SIZE] = {
		0xd9, 0x31, 0x32, 0x25, 0xf8, 0x84, 0x06, 0xe5,
		0xa5, 0x59, 0x09, 0xc5, 0xaf, 0xf5, 0x26, 0x9a,
		0x86, 0xa7, 0xa9, 0x53, 0x15, 0x34, 0xf7, 0xda,
		0x2e, 0x4c, 0x30, 0x3d, 0x8a, 0x31, 0x8a, 0x72,
		0x1c, 0x3c, 0x0c, 0x95, 0x95, 0x68, 0x09, 0x53,
		0x2f, 0xcf, 0x0e, 0x24, 0x49, 0xa6, 0xb5, 0x25,
		0xb1, 0x6a, 0xed, 0xf5, 0xaa, 0x0d, 0xe6, 0x57,
		0xba, 0x63, 0x7b, 0x39, 0x1a, 0xaf, 0xd2, 0x55
	};
	uint64_t indata_len = 4 * BLOCK_SIZE;

	uint8_t *aad = NULL;
	uint64_t aad_len = 0;

	uint8_t outdata[4 * BLOCK_SIZE];
*/

/*
	[Keylen = 128]
	[IVlen = 96]
	[PTlen = 256]
	[AADlen = 384]
	[Taglen = 128]

	Key = 48b7f337cdf9252687ecc760bd8ec184
	IV = 3e894ebb16ce82a53c3e05b2
	PT = bb2bac67a4709430c39c2eb9acfabc0d456c80d30aa1734e57997d548a8f0603
	AAD = 7d924cfd37b3d046a96eb5e132042405c8731e06509787bbeb41f258275746495e884d69871f77634c584bb007312234
	CT = d263228b8ce051f67e9baf1ce7df97d10cd5f3bc972362055130c7d13c3ab2e7
	Tag = 71446737ca1fa92e6d026d7d2ed1aa9c
*/
///*
	uint8_t key[KEY_SIZE] = {
		0x48, 0xb7, 0xf3, 0x37,
		0xcd, 0xf9, 0x25, 0x26,
		0x87, 0xec, 0xc7, 0x60,
		0xbd, 0x8e, 0xc1, 0x84
		};
		uint8_t iv[IV_SIZE] = {
		0x3e, 0x89, 0x4e, 0xbb,
		0x16, 0xce, 0x82, 0xa5,
		0x3c, 0x3e, 0x05, 0xb2
	};
	uint8_t indata[2 * BLOCK_SIZE] = {
		0xbb, 0x2b, 0xac, 0x67,
		0xa4, 0x70, 0x94, 0x30,
		0xc3, 0x9c, 0x2e, 0xb9,
		0xac, 0xfa, 0xbc, 0x0d,
		0x45, 0x6c, 0x80, 0xd3,
		0x0a, 0xa1, 0x73, 0x4e,
		0x57, 0x99, 0x7d, 0x54,
		0x8a, 0x8f, 0x06, 0x03
	};
	uint64_t indata_len = 2 * BLOCK_SIZE;

	uint8_t aad[3 * BLOCK_SIZE] = {
		0x7d, 0x92, 0x4c, 0xfd,
		0x37, 0xb3, 0xd0, 0x46,
		0xa9, 0x6e, 0xb5, 0xe1,
		0x32, 0x04, 0x24, 0x05,
		0xc8, 0x73, 0x1e, 0x06,
		0x50, 0x97, 0x87, 0xbb,
		0xeb, 0x41, 0xf2, 0x58,
		0x27, 0x57, 0x46, 0x49,
		0x5e, 0x88, 0x4d, 0x69,
		0x87, 0x1f, 0x77, 0x63,
		0x4c, 0x58, 0x4b, 0xb0,
		0x07, 0x31, 0x22, 0x34
	};
	uint64_t aad_len = 3 * BLOCK_SIZE;

	uint8_t outdata[2 * BLOCK_SIZE];
//*/

	aes_gcm(key, iv, IV_SIZE, indata, indata_len, aad, aad_len, tag, outdata);

	dump_buffer(outdata, indata_len, "C: ");
	dump_buffer(tag, BLOCK_SIZE, "T: ");
}

