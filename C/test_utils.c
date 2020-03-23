#include <stdio.h>
#include <limits.h>
#include "test.h"

void dump_buffer(uint8_t *buf, unsigned int len, char *dbg)
{
	unsigned int i;

	if (dbg)
		printf("%s", dbg);

	for (i = 0; i < len; ++i)
		printf("%02x", buf[i]);

	printf("\n");
}

void dump_buffer_bits(uint8_t *buf, unsigned int len, char *dbg)
{
	int i, j;

	if (dbg)
		printf("%s", dbg);

	for (i = 0; i < len; ++i) {
		for (j = CHAR_BIT; j >= 0; --j) {
			printf("%d", (buf[i] >> j) & 1);
			if (j % (CHAR_BIT / 2) == 0)
				printf(" ");
		}
	}

	printf("\n\n");
}
