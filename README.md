# AES hardware engine for Xilinx Zynq platform

- 128/256-bit keys
- ECB/CBC/PCBC/CTR/CFB/OFB
- IPSEC offloading OK
- driver compatible with linux-xlnx v4.19 branch

## Quick Start
Generate bitstream for your platform (must have vivado environment sourced).  
In my case, the part code for ARTY Z7-20 board is xc7z020clg400-1:  
```sh
make PART="xc7z020clg400-1" bitstream
```
Get the bitstream from:
```sh
$ ls -lah synthesis/zynq_aes/zynq_aes.runs/impl_1/*bit
-rw-rw-r-- 1 xxx xxx 2,0M sep 17 22:31 synthesis/zynq_aes/zynq_aes.runs/impl_1/zynq_aes_bd_wrapper.bit
```
Run regression tests (XSIM):
```sh
make test
```

## Openssl Benchmarks
#### ECB
```sh

Software-only:
root@arty-zynq7:~# openssl speed -evp aes-128-ecb -elapsed
type             16 bytes     64 bytes    256 bytes   1024 bytes   2048 bytes   4096 bytes   8192 bytes  16384 bytes  32768 bytes  65536 bytes
aes-128-ecb      20565.61k    23967.59k    25016.06k    25291.09k    25331.03k    25340.59k    25329.66k    25285.97k    24958.29k    24226.47k

HW acceleration:
type             16 bytes     64 bytes    256 bytes   1024 bytes   2048 bytes   4096 bytes   8192 bytes  16384 bytes  32768 bytes  65536 bytes
aes-128-ecb        212.22k      843.43k     3546.28k    13027.67k    23939.68k    35828.36k    47195.78k    56138.49k    62379.75k    65688.92k

root@arty-zynq7:~# openssl speed -evp aes-256-ecb -elapsed
type             16 bytes     64 bytes    256 bytes   1024 bytes   2048 bytes   4096 bytes   8192 bytes  16384 bytes  32768 bytes  65536 bytes
aes-256-ecb        234.04k      928.11k     3666.94k    14110.72k    22911.66k    32818.52k    41937.58k    49327.35k    53974.05k    56615.21
```

#### CTR
```sh
Software-only:
root@arty-zynq7:~# openssl speed -elapsed aes-256-ctr            
type             16 bytes     64 bytes    256 bytes   1024 bytes   2048 bytes   4096 bytes   8192 bytes  16384 bytes  32768 bytes  65536 bytes
aes-256 cbc      16144.04k    16890.18k    17274.45k    17376.94k    17436.67k    17417.56k    17479.00k    17569.11k    17651.03k    17629.18k

HW acceleration:
root@arty-zynq7:~# openssl speed  -evp aes-256-cbc -elapsed
type             16 bytes     64 bytes    256 bytes   1024 bytes   2048 bytes   4096 bytes   8192 bytes  16384 bytes  32768 bytes  65536 bytes
aes-256-ctr        423.87k      893.80k     3534.08k    13635.93k    22278.14k    32269.65k    41446.06k    48873.47k    53630.29k    56527.54k
```

## Block design and AXI DMA config

![](https://github.com/ovpanait/zynq-aes/blob/master/block_design.png)
![](https://github.com/ovpanait/zynq-aes/blob/master/axi_dma.png)

## Quick Start for Arty Z7-20 board using Yocto (untested recently)

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
git clone -b master git://github.com/Xilinx/meta-xilinx
git clone -b master git://github.com/ovpanait/meta-artyz7
git clone -b master git://github.com/ovpanait/zynq-aes

. poky/oe-init-build-env
bitbake-layers add-layer ../meta-openembedded/meta-oe/
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
