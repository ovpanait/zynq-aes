#include "test.h"

void dump_buffer(uint8_t *buf, unsigned int len, char *dbg)
{
	unsigned int i;

	if (dbg)
		printf("%s\n", dbg);

	for (i = 0; i < len; ++i)
		printf("%02x", buf[i]);

	printf("\n\n");
}


