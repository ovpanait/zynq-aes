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

#### CBC
```sh
Software-only:
root@arty-zynq7:~# openssl speed -elapsed aes-128-cbc             
You have chosen to measure elapsed time instead of user CPU time.
Doing aes-128 cbc for 3s on 16 size blocks: 3901399 aes-128 cbc's in 3.00s
Doing aes-128 cbc for 3s on 64 size blocks: 1032087 aes-128 cbc's in 3.00s
Doing aes-128 cbc for 3s on 256 size blocks: 265225 aes-128 cbc's in 3.00s
Doing aes-128 cbc for 3s on 512 size blocks: 133035 aes-128 cbc's in 3.00s
Doing aes-128 cbc for 3s on 1024 size blocks: 66651 aes-128 cbc's in 3.00s
Doing aes-128 cbc for 3s on 2048 size blocks: 33393 aes-128 cbc's in 3.00s
Doing aes-128 cbc for 3s on 4096 size blocks: 16699 aes-128 cbc's in 3.00s
Doing aes-128 cbc for 3s on 8192 size blocks: 8362 aes-128 cbc's in 3.00s
Doing aes-128 cbc for 3s on 16384 size blocks: 4175 aes-128 cbc's in 3.00s
OpenSSL 1.1.1a  20 Nov 2018
built on: Wed May 22 06:38:44 2019 UTC
options:bn(64,32) rc4(char) des(long) aes(partial) idea(int) blowfish(ptr) 
compiler: arm-poky-linux-gnueabi-gcc  -march=armv7-a -mthumb -mfpu=neon -mfloat-abi=hard -mcpu=cortex-a9 -fstack-protector-strong  -D_FORTIFY_SOURCE=2 -Wformat -Wformat-security -Werror=format-security --sysroot=recipe-sysroot -O2 -pipe -g -feliminate-unused-debug-types -fdebug-prefix-map= -fdebug-prefix-map= -fdebug-prefix-map= -DOPENSSL_USE_NODELETE -DOPENSSL_PIC -DOPENSSL_CPUID_OBJ -DOPENSSL_BN_ASM_MONT -DOPENSSL_BN_ASM_GF2m -DSHA1_ASM -DSHA256_ASM -DSHA512_ASM -DKECCAK1600_ASM -DAES_ASM -DBSAES_ASM -DGHASH_ASM -DECP_NISTZ256_ASM -DPOLY1305_ASM -DNDEBUG
The 'numbers' are in 1000s of bytes per second processed.
type             16 bytes     64 bytes    256 bytes    512 bytes   1024 bytes   2048 bytes   4096 bytes   8192 bytes  16384 bytes
aes-128 cbc      20807.46k    22017.86k    22632.53k    22704.64k    22750.21k    22796.29k    22799.70k    22833.83k    22801.07k

HW acceleration:
root@arty-zynq7:~# openssl speed  -evp aes-128-cbc -elapsed
You have chosen to measure elapsed time instead of user CPU time.
Doing aes-128-cbc for 3s on 16 size blocks: 83560 aes-128-cbc's in 3.00s
Doing aes-128-cbc for 3s on 64 size blocks: 79055 aes-128-cbc's in 3.00s
Doing aes-128-cbc for 3s on 256 size blocks: 80787 aes-128-cbc's in 3.00s
Doing aes-128-cbc for 3s on 512 size blocks: 71798 aes-128-cbc's in 3.00s
Doing aes-128-cbc for 3s on 1024 size blocks: 43796 aes-128-cbc's in 3.00s
Doing aes-128-cbc for 3s on 2048 size blocks: 29908 aes-128-cbc's in 3.00s
Doing aes-128-cbc for 3s on 4096 size blocks: 21926 aes-128-cbc's in 3.00s
Doing aes-128-cbc for 3s on 8192 size blocks: 12018 aes-128-cbc's in 3.00s
Doing aes-128-cbc for 3s on 16384 size blocks: 6485 aes-128-cbc's in 3.00s
OpenSSL 1.1.1a  20 Nov 2018
built on: Wed May 22 06:38:44 2019 UTC
options:bn(64,32) rc4(char) des(long) aes(partial) idea(int) blowfish(ptr)
compiler: arm-poky-linux-gnueabi-gcc  -march=armv7-a -mthumb -mfpu=neon -mfloat-abi=hard -mcpu=cortex-a9 -fstack-protector-strong  -D_FORTIFY_SOURCE=2 -Wformat -Wformat-security -Werror=format-security --sysroot=recipe-sysroot -O2 -pipe -g -feliminate-unused-debug-types -fdebug-prefix-map= -fdebug-prefix-map= -fdebug-prefix-map= -DOPENSSL_USE_NODELETE -DOPENSSL_PIC -DOPENSSL_CPUID_OBJ -DOPENSSL_BN_ASM_MONT -DOPENSSL_BN_ASM_GF2m -DSHA1_ASM -DSHA256_ASM -DSHA512_ASM -DKECCAK1600_ASM -DAES_ASM -DBSAES_ASM -DGHASH_ASM -DECP_NISTZ256_ASM -DPOLY1305_ASM -DNDEBUG
The 'numbers' are in 1000s of bytes per second processed.
type             16 bytes     64 bytes    256 bytes    512 bytes   1024 bytes   2048 bytes   4096 bytes   8192 bytes  16384 bytes
aes-128-cbc        445.65k     1686.51k     6893.82k    12253.53k    14949.03k    20417.19k    29936.30k    32817.15k    35416.75k
