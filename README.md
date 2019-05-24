# AES hardware accelerator for Xilinx Zynq platform

- ECB/CBC support

### Benchmarks
#### ECB
```sh

Software-only:

root@xilinx-zynq:~# openssl speed -evp aes-128-ecb -elapsed
Doing aes-128-ecb for 3s on 16 size blocks: 4131616 aes-128-ecb's in 3.00s
Doing aes-128-ecb for 3s on 64 size blocks: 1140184 aes-128-ecb's in 3.00s
Doing aes-128-ecb for 3s on 256 size blocks: 293425 aes-128-ecb's in 3.00s
Doing aes-128-ecb for 3s on 1024 size blocks: 73802 aes-128-ecb's in 3.00s
Doing aes-128-ecb for 3s on 8192 size blocks: 9222 aes-128-ecb's in 3.00s
OpenSSL 1.0.2o  27 Mar 2018
built on: reproducible build, date unspecified
options:bn(64,32) rc4(ptr,char) des(idx,cisc,16,long) aes(partial) idea(int) blowfish(ptr) 
compiler: arm-wrs-linux-gnueabi-gcc  -march=armv7-a -marm -mfpu=neon -mfloat-abi=hard  -DL_ENDIAN       -DTERMIO  -O2 -pipe -g -feliminate-unused-debug-types  -Wall -Wa,--noexecstack -DHAVE_CRYPTODEV -DUSE_CRYPTODEV_DIGESTS
The 'numbers' are in 1000s of bytes per second processed.
type             16 bytes     64 bytes    256 bytes   1024 bytes   8192 bytes
aes-128-ecb      22035.29k    24323.93k    25038.93k    25191.08k    25182.21k

HW acceleration:



```
