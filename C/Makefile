DEBUG ?= 0
KEY_SIZE ?= 128
HEADERS = aes.h
CFLAGS= -I. -Wall

ifeq ($(KEY_SIZE), 256)
	CFLAGS += -DAES_256
endif

ifeq ($(DEBUG), 1)
    CFLAGS += -DDEBUG
endif

%.o: %.c $(HEADERS)

test: cipher.o decipher.o key_expansion.o test.o aes_utils.o test_utils.o

gcm: test_utils.o gcm.o

.SILENT: clean
.PHONY: clean

clean:
	rm -f *.o test gcm
