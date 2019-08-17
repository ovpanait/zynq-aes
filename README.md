# AES hardware engine for Xilinx Zynq platform

- 128 bit keys (so far)
- ECB/CBC support
- IPSEC offloading OK
- driver compatible with linux-xlnx v4.14 branch

## Quick Start for Arty Z7-20 board using Yocto

### Prerequisites - Build Host Packages
```sh
sudo apt-get install gawk wget git-core diffstat unzip texinfo gcc-multilib \
     build-essential chrpath socat cpio python python3 python3-pip python3-pexpect \
     xz-utils debianutils iputils-ping python3-git python3-jinja2 libegl1-mesa libsdl1.2-dev \
     xterm
```

### Setup
```sh
git clone -b master git://git.yoctoproject.org/poky
# Needed by meta-xilinx-bsp
git clone -b master git://github.com/openembedded/meta-openembedded
# The master branch of meta-xilinx is broken for now, master-next is the up-to-date one
git clone -b master-next git://github.com/Xilinx/meta-xilinx
git clone -b master git://github.com/ovpanait/meta-artyz7
git clone -b master https://github.com/ovpanait/zynq-aes.git

. poky/oe-init-build-env
bitbake-layers add-layer ../meta-openembedded/meta-oe/
echo 'LAYERSERIES_COMPAT_xilinx += "warrior"' >> ../meta-xilinx/meta-xilinx-bsp/conf/layer.conf
bitbake-layers add-layer ../meta-xilinx/meta-xilinx-bsp/
bitbake-layers add-layer ../meta-artyz7
bitbake-layers add-layer ../zynq-aes/yocto/meta-zynqaes

echo 'MACHINE="arty-zynq7"' >> conf/local.conf
echo 'DTC_BFLAGS_append = " -@"' >> conf/local.conf
echo 'PACKAGECONFIG_append_pn-openssl = " cryptodev-linux"' >> conf/local.conf
echo 'IMAGE_INSTALL_append = " openssh cryptodev-linux cryptodev-module cryptodev-tests"' >> conf/local.conf
echo 'IMAGE_INSTALL_append = " openssl-bin openssl openssl-engines"' >> conf/local.conf
echo 'IMAGE_INSTALL_append = " kernel-modules zynqaes-mod"' >> conf/local.conf
echo 'VIRTUAL_BITSTREAM = "1"' >> conf/local.conf
echo 'PREFERRED_PROVIDER_virtual/bitstream = "zynqaes-firmware-xc7z020clg400-1"' >> conf/local.conf
```

### Build a minimal console-only image:
```sh
bitbake core-image-minimal
```

### Copy image to sd-card
```sh
sudo dd if=tmp/deploy/images/arty-zynq7/core-image-minimal-arty-zynq7.wic of=/dev/mmcblkX bs=4M iflag=fullblock oflag=direct conv=fsync status=progress
```

### Run benchmarks
```sh
root@arty-zynq7:~# mkdir -p /sys/kernel/config/device-tree/overlays/zynqaes
root@arty-zynq7:~# umount /boot
root@arty-zynq7:~# cat /boot/devicetree/pl-zynqaes.dtbo > /sys/kernel/config/device-tree/overlays/zynqaes/dtbo
root@arty-zynq7:~# modprobe cryptodev
root@arty-zynq7:~# modprobe crypto-engine
root@arty-zynq7:~# openssl speed -evp aes-128-ecb -elapsed
root@arty-zynq7:~# openssl speed -evp aes-128-cbc -elapsed
```

## Benchmarks
#### ECB
```sh

Software-only:
root@arty-zynq7:~# openssl speed -evp aes-128-ecb -elapsed
OpenSSL 1.1.1a  20 Nov 2018
built on: Fri Jun  7 11:04:38 2019 UTC
options:bn(64,32) rc4(char) des(long) aes(partial) idea(int) blowfish(ptr) 
compiler: arm-poky-linux-gnueabi-gcc  -march=armv7-a -mthumb -mfpu=neon -mfloat-abi=hard -mcpu=cortex-a9 -fstack-protector-strong  -D_FORTIFY_SOURCE=2 -Wformat -Wformat-security -Werror=format-security --sysroot=recipe-sysroot -O2 -pipe -g -feliminate-unused-debug-types -fdebug-prefix-map= -fdebug-prefix-map= -fdebug-prefix-map= -DOPENSSL_USE_NODELETE -DOPENSSL_PIC -DOPENSSL_CPUID_OBJ -DOPENSSL_BN_ASM_MONT -DOPENSSL_BN_ASM_GF2m -DSHA1_ASM -DSHA256_ASM -DSHA512_ASM -DKECCAK1600_ASM -DAES_ASM -DBSAES_ASM -DGHASH_ASM -DECP_NISTZ256_ASM -DPOLY1305_ASM -DNDEBUG
The 'numbers' are in 1000s of bytes per second processed.
type             16 bytes     64 bytes    256 bytes   1024 bytes   2048 bytes   4096 bytes   8192 bytes  16384 bytes  32768 bytes  65536 bytes
aes-128-ecb      20565.61k    23967.59k    25016.06k    25291.09k    25331.03k    25340.59k    25329.66k    25285.97k    24958.29k    24226.47k

HW acceleration:
root@arty-zynq7:~# openssl speed  -evp aes-128-ecb -elapsed
OpenSSL 1.1.1c  28 May 2019
built on: Sat Jul 20 06:22:15 2019 UTC
options:bn(64,32) rc4(char) des(long) aes(partial) idea(int) blowfish(ptr) 
compiler: arm-poky-linux-gnueabi-gcc  -mthumb -mfpu=neon -mfloat-abi=hard -mcpu=cortex-a9 -fstack-protector-strong  -D_FORTIFY_SOURCE=2 -Wformat -Wformat-security -Werror=format-security --sysroot=recipe-sysroot -O2 -pipe -g -feliminate-unused-debug-types -fmacro-prefix-map=                      -fdebug-prefix-map=                      -fdebug-prefix-map=                      -fdebug-prefix-map= -DOPENSSL_USE_NODELETE -DOPENSSL_PIC -DOPENSSL_CPUID_OBJ -DOPENSSL_BN_ASM_MONT -DOPENSSL_BN_ASM_GF2m -DSHA1_ASM -DSHA256_ASM -DSHA512_ASM -DKECCAK1600_ASM -DAES_ASM -DBSAES_ASM -DGHASH_ASM -DECP_NISTZ256_ASM -DPOLY1305_ASM -DNDEBUG
The 'numbers' are in 1000s of bytes per second processed.
type             16 bytes     64 bytes    256 bytes   1024 bytes   2048 bytes   4096 bytes   8192 bytes  16384 bytes  32768 bytes  65536 bytes
aes-128-ecb        179.87k      716.76k     2801.24k     9425.92k    14497.11k    23075.50k    31304.36k    36973.23k       40544.94k    43537.75k


```

#### CBC
```sh
Software-only:
root@arty-zynq7:~# openssl speed -elapsed aes-128-cbc             
OpenSSL 1.1.1a  20 Nov 2018
built on: Fri Jun  7 11:04:38 2019 UTC
options:bn(64,32) rc4(char) des(long) aes(partial) idea(int) blowfish(ptr)
compiler: arm-poky-linux-gnueabi-gcc  -march=armv7-a -mthumb -mfpu=neon -mfloat-abi=hard -mcpu=cortex-a9
 -fstack-protector-strong  -D_FORTIFY_SOURCE=2 -Wformat -Wformat-security -Werror=format-security --sysr
oot=recipe-sysroot -O2 -pipe -g -feliminate-unused-debug-types -fdebug-prefix-map= -fdebug-prefix-map= -
fdebug-prefix-map= -DOPENSSL_USE_NODELETE -DOPENSSL_PIC -DOPENSSL_CPUID_OBJ -DOPENSSL_BN_ASM_MONT -DOPEN
SSL_BN_ASM_GF2m -DSHA1_ASM -DSHA256_ASM -DSHA512_ASM -DKECCAK1600_ASM -DAES_ASM -DBSAES_ASM -DGHASH_ASM 
-DECP_NISTZ256_ASM -DPOLY1305_ASM -DNDEBUG
The 'numbers' are in 1000s of bytes per second processed.
type             16 bytes     64 bytes    256 bytes   1024 bytes   2048 bytes   4096 bytes   8192 bytes   16384 bytes  32768 bytes  65536 bytes
aes-128-cbc      17959.16k    21204.69k    22471.77k    22814.04k    22863.87k    22882.99k    22915.75k    22937.60k 22850.22k    22478.85k

HW acceleration:
root@arty-zynq7:~# openssl speed  -evp aes-128-cbc -elapsed
built on: Sat Jul 20 06:22:15 2019 UTC
options:bn(64,32) rc4(char) des(long) aes(partial) idea(int) blowfish(ptr) 
compiler: arm-poky-linux-gnueabi-gcc  -mthumb -mfpu=neon -mfloat-abi=hard -mcpu=cortex-a9 -fstack-protector-strong  -D_FORTIFY_SOURCE=2 -Wformat -Wformat-security -Werror=format-security --sysroot=recipe-sysroot -O2 -pipe -g -feliminate-unused-debug-types -fmacro-prefix-map=                      -fdebug-prefix-map=                      -fdebug-prefix-map=                      -fdebug-prefix-map= -DOPENSSL_USE_NODELETE -DOPENSSL_PIC -DOPENSSL_CPUID_OBJ -DOPENSSL_BN_ASM_MONT -DOPENSSL_BN_ASM_GF2m -DSHA1_ASM -DSHA256_ASM -DSHA512_ASM -DKECCAK1600_ASM -DAES_ASM -DBSAES_ASM -DGHASH_ASM -DECP_NISTZ256_ASM -DPOLY1305_ASM -DNDEBUG
The 'numbers' are in 1000s of bytes per second processed.
type             16 bytes     64 bytes    256 bytes   1024 bytes   2048 bytes   4096 bytes   8192 bytes  16384 bytes  32768 bytes  65536 bytes
aes-128-cbc        164.58k      684.57k     2752.77k     9492.48k    15233.71k    23097.34k    30135.64k    36776.62k    40239.10k    43166.38k
```
## Block design and AXI DMA config

![](https://github.com/ovpanait/zynq-aes/blob/master/block_design.png)
![](https://github.com/ovpanait/zynq-aes/blob/master/axi_dma.png)
