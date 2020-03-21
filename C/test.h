#ifndef TEST_H
#define TEST_H

#include <stdint.h>

void dump_buffer(uint8_t *buf, unsigned int len, char *dbg);
void dump_buffer_bits(uint8_t *buf, unsigned int len, char *dbg);

#endif
