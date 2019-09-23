CFLAGS= -I. -Wall

HEADERS = aes.h

DEBUG ?= 0
ifeq ($(DEBUG), 1)
    CFLAGS += -DDEBUG
endif

%.o: %.c $(HEADERS)

test: cipher.o decipher.o key_expansion.o test.o aes_utils.o

.SILENT: clean
.PHONY: clean

clean:
	rm -f *.o test
