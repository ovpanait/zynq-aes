CC=gcc
CFLAGS=-DDEBUG -I.

DEPS= aes.h

%.o: %.c $(DEPS)
	$(CC) -c -o $@ $< $(CFLAGS)

test: cipher.o key_expansion.o test.o
	$(CC) -o $@ $^ $(CFLAGS)

.SILENT:
.PHONY: clean

clean:
	rm -f *.o key_expansion cipher test
