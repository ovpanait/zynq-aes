# AES hardware engine for Xilinx Zynq platform

- 128/256-bit keys
- GCM/ECB/CBC/PCBC/CTR/CFB/OFB
- IPSEC offloading OK
- driver compatible with linux-xlnx v5.4 branch

#### Notes on GCM support:  
Currently, the hw engine is limited to receiving full 128-bit blocks for  
processing. This works well for ECB/CBC/PCBC/CTR/CFB/OFB modes of operation  
since they only deal with block-sized data, but GCM can process arbitrary-sized  
AAD/CRYPTDATA.

The consequence is that we pad AAD/CRYPTDATA with zeros in the Linux kernel  
driver before sending it for processing. This means splitting the scatterlist  
provided by the crypto layer and creating a new one, which introduces  
considerable overhead.

Therefore, there is a lot of room for improvement in this area (converting the  
processing pipeline input to deal with arbitrary-sized data) and it is on my  
TODO list.


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
## Petalinux Build
Note: vivado and petalinux environment scripts must be sourced prior to running these.  

### Setup workdir
```sh
mkdir zynq-aes-petalinux                                                                                       
cd zynq-aes-petalinux
git clone https://github.com/ovpanait/zynq-aes.git zynq-aes-hw && cd zynq-aes-hw
```

### Generate bitstream and update petalinux layer
In my case, the part code for ARTY Z7-20 board is xc7z020clg400-1:
```sh
make PART="xc7z020clg400-1" bitstream # this can take some time
make yocto
```
### Create Petalinux image
```sh
export ZYNQAES_XSA="$(realpath synthesis/output/zynqaes_hw.xsa)"
export ZYNQAES_YOCTO_LAYER="$(realpath yocto/meta-zynqaes)"

cd ..
petalinux-create --type project --template zynq --name zynq-aes-build && cd zynq-aes-build
petalinux-config --get-hw-description "${ZYNQAES_XSA}"

echo "BBLAYERS += \"${ZYNQAES_YOCTO_LAYER}\" "  >> build/conf/bblayers.conf
echo "IMAGE_INSTALL_append = \" zynqaes-mod\"" >> build/conf/local.conf

petalinux-build
```
### Sanity runtime test
After booting the generated image, run on target:
```sh
mkdir -p /sys/kernel/config/device-tree/overlays/zynqaes
cat /boot/devicetree/pl-zynqaes.dtbo > /sys/kernel/config/device-tree/overlays/zynqaes/dtbo

root@zynq-aes-build:~# modprobe tcrypt mode=500 sec=1
tcrypt: 
testing speed of async ecb(aes) (zynqaes-ecb) encryption
tcrypt: test 0 (128 bit key, 16 byte blocks): 8397 operations in 1 seconds (134352 bytes)
tcrypt: test 1 (128 bit key, 64 byte blocks): 9120 operations in 1 seconds (583680 bytes)
tcrypt: test 2 (128 bit key, 256 byte blocks): 9046 operations in 1 seconds (2315776 bytes)
tcrypt: test 3 (128 bit key, 1024 byte blocks): 7142 operations in 1 seconds (7313408 bytes)
tcrypt: test 4 (128 bit key, 1472 byte blocks): 7132 operations in 1 seconds (10498304 bytes)
tcrypt: test 5 (128 bit key, 8192 byte blocks): 4220 operations in 1 seconds (34570240 bytes)
...
```

## Block design and AXI DMA config

![](https://github.com/ovpanait/zynq-aes/blob/master/bd/block_design.png)
![](https://github.com/ovpanait/zynq-aes/blob/master/bd/axi_dma.png)

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
