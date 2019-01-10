CC=gcc
CFLAGS=-DDEBUG

key_expansion: key_expansion.o
	gcc -o $@ $< $(CFLAGS)

.PHONY: clean

clean:
	rm -f *.o key_expansion
