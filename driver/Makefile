# Uncomment to enable debug info
# CFLAGS_zynqaes.o := -DDEBUG
# CFLAGS_zynqaes_aead.o := -DDEBUG
# CFLAGS_zynqaes_skcipher.o := -DDEBUG

obj-m := zynqaes_crypto.o
zynqaes_crypto-objs := zynqaes.o zynqaes_skcipher.o zynqaes_aead.o

SRC := $(shell pwd)

all:
	$(MAKE) -C $(KERNEL_DIR) M=$(SRC)

modules_install:
	$(MAKE) -C $(KERNEL_DIR) M=$(SRC) modules_install

clean:
	rm -f *.o *~ core .depend .*.cmd *.ko *.mod.c *.mod
	rm -f Module.markers Module.symvers modules.order
	rm -rf .tmp_versions Modules.symvers built-in.a
