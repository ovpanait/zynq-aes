# Taken from the Linux kernel from tools/scripts/Makefile.include
# Needed to make the compilation work properly with both CROSS_COMPILE and
# Yocto toolchain.
#
# Makefiles suck: This macro sets a default value of $(2) for the
# variable named by $(1), unless the variable has been set by
# environment or command line. This is necessary for CC and AR
# because make sets default values, so the simpler ?= approach
# won't work as expected.
define allow-override
  $(if $(or $(findstring environment,$(origin $(1))),\
            $(findstring command line,$(origin $(1)))),,\
    $(eval $(1) = $(2)))
endef

# Allow setting various cross-compile vars or setting CROSS_COMPILE as a prefix.
$(call allow-override,CC,$(CROSS_COMPILE)gcc)
$(call allow-override,AR,$(CROSS_COMPILE)ar)
$(call allow-override,LD,$(CROSS_COMPILE)ld)
$(call allow-override,CXX,$(CROSS_COMPILE)g++)
$(call allow-override,STRIP,$(CROSS_COMPILE)strip)

CFLAGS += -Wall

all: stress gcm

stress: stress.c af_alg.c

gcm: gcm.c af_alg.c

clean:
	rm -rf stress
