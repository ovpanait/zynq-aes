CC=gcc
CFLAGS=-DDEBUG -I.

DEPS= aes.h

%.o: %.c $(DEPS)
	$(CC) -c -o $@ $< $(CFLAGS)

key_expansion: key_expansion.o
	gcc -o $@ $< $(CFLAGS)

cipher: cipher.o
	gcc -o $@ $< $(CFLAGS)

.PHONY: clean

clean:
	rm -f *.o key_expansion cipher
