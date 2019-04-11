CFLAGS= -I.

DEPS= aes.h

DEBUG ?= 0
ifeq ($(DEBUG), 1)
    CFLAGS += -DDEBUG
endif

%.o: %.c $(DEPS)
	$(CC) -c -o $@ $< $(CFLAGS)

test: cipher.o decipher.o key_expansion.o test.o
	$(CC) -o $@ $^ $(CFLAGS)

.SILENT: clean
.PHONY: clean

clean:
	rm -f *.o key_expansion cipher test
