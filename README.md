# AES hardware accelerator for Xilinx Zynq platform

- ECB/CBC support

### Benchmarks
#### ECB
```sh

Software-only:
root@arty-zynq7:~# openssl speed -evp aes-128-ecb -elapsed
Could not open /dev/crypto: No such file or directory
You have chosen to measure elapsed time instead of user CPU time.
Doing aes-128-ecb for 3s on 16 size blocks: 3869697 aes-128-ecb's in 3.00s
Doing aes-128-ecb for 3s on 64 size blocks: 1122983 aes-128-ecb's in 3.00s
Doing aes-128-ecb for 3s on 256 size blocks: 293083 aes-128-ecb's in 3.00s
Doing aes-128-ecb for 3s on 512 size blocks: 147615 aes-128-ecb's in 3.00s
Doing aes-128-ecb for 3s on 1024 size blocks: 74070 aes-128-ecb's in 3.00s
Doing aes-128-ecb for 3s on 2048 size blocks: 37097 aes-128-ecb's in 3.00s
Doing aes-128-ecb for 3s on 4096 size blocks: 18555 aes-128-ecb's in 3.00s
Doing aes-128-ecb for 3s on 8192 size blocks: 9269 aes-128-ecb's in 3.00s
Doing aes-128-ecb for 3s on 16384 size blocks: 4617 aes-128-ecb's in 3.00s
OpenSSL 1.1.1a  20 Nov 2018
built on: Wed May 22 06:38:44 2019 UTC
options:bn(64,32) rc4(char) des(long) aes(partial) idea(int) blowfish(ptr) 
compiler: arm-poky-linux-gnueabi-gcc  -march=armv7-a -mthumb -mfpu=neon -mfloat-abi=hard -mcpu=cortex-a9 -fstack-protector-strong  -D_FORTIFY_SOURCE=2 -Wformat -Wformat-security -Werror=format-security --sysroot=recipe-sysroot -O2 -pipe -g -feliminate-unused-debug-types -fdebug-prefix-map= -fdebug-prefix-map= -fdebug-prefix-map= -DOPENSSL_USE_NODELETE -DOPENSSL_PIC -DOPENSSL_CPUID_OBJ -DOPENSSL_BN_ASM_MONT -DOPENSSL_BN_ASM_GF2m -DSHA1_ASM -DSHA256_ASM -DSHA512_ASM -DKECCAK1600_ASM -DAES_ASM -DBSAES_ASM -DGHASH_ASM -DECP_NISTZ256_ASM -DPOLY1305_ASM -DNDEBUG
The 'numbers' are in 1000s of bytes per second processed.
type             16 bytes     64 bytes    256 bytes    512 bytes   1024 bytes   2048 bytes   4096 bytes   8192 bytes  16384 bytes
aes-128-ecb      20638.38k    23956.97k    25009.75k    25192.96k    25282.56k    25324.89k    25333.76k    25310.55k    25214.98k

HW acceleration:
root@arty-zynq7:~# openssl speed  -evp aes-128-ecb -elapsed
You have chosen to measure elapsed time instead of user CPU time.
Doing aes-128-ecb for 3s on 16 size blocks: 82932 aes-128-ecb's in 3.00s
Doing aes-128-ecb for 3s on 64 size blocks: 82507 aes-128-ecb's in 3.00s
Doing aes-128-ecb for 3s on 256 size blocks: 80045 aes-128-ecb's in 3.00s
Doing aes-128-ecb for 3s on 512 size blocks: 71853 aes-128-ecb's in 3.00s
Doing aes-128-ecb for 3s on 1024 size blocks: 43539 aes-128-ecb's in 3.00s
Doing aes-128-ecb for 3s on 2048 size blocks: 29582 aes-128-ecb's in 3.00s
Doing aes-128-ecb for 3s on 4096 size blocks: 21313 aes-128-ecb's in 3.00s
Doing aes-128-ecb for 3s on 8192 size blocks: 13271 aes-128-ecb's in 3.00s
Doing aes-128-ecb for 3s on 16384 size blocks: 7497 aes-128-ecb's in 3.00s
OpenSSL 1.1.1a  20 Nov 2018
built on: Wed May 22 06:38:44 2019 UTC
options:bn(64,32) rc4(char) des(long) aes(partial) idea(int) blowfish(ptr) 
compiler: arm-poky-linux-gnueabi-gcc  -march=armv7-a -mthumb -mfpu=neon -mfloat-abi=hard -mcpu=cortex-a9 -fstack-protector-strong  -D_FORTIFY_SOURCE=2 -Wformat -Wformat-security -Werror=format-security --sysroot=recipe-sysroot -O2 -pipe -g -feliminate-unused-debug-types -fdebug-prefix-map= -fdebug-prefix-map= -fdebug-prefix-map= -DOPENSSL_USE_NODELETE -DOPENSSL_PIC -DOPENSSL_CPUID_OBJ -DOPENSSL_BN_ASM_MONT -DOPENSSL_BN_ASM_GF2m -DSHA1_ASM -DSHA256_ASM -DSHA512_ASM -DKECCAK1600_ASM -DAES_ASM -DBSAES_ASM -DGHASH_ASM -DECP_NISTZ256_ASM -DPOLY1305_ASM -DNDEBUG
The 'numbers' are in 1000s of bytes per second processed.
type             16 bytes     64 bytes    256 bytes    512 bytes   1024 bytes   2048 bytes   4096 bytes   8192 bytes  16384 bytes
aes-128-ecb        442.30k     1760.15k     6830.51k    12262.91k    14861.31k    20194.65k    29099.35k    36238.68k    40943.62k


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
Doing aes-128-cbc for 3s on 16 size blocks: 81804 aes-128-cbc's in 3.00s
Doing aes-128-cbc for 3s on 64 size blocks: 81273 aes-128-cbc's in 3.00s
Doing aes-128-cbc for 3s on 256 size blocks: 78930 aes-128-cbc's in 3.00s
Doing aes-128-cbc for 3s on 512 size blocks: 70474 aes-128-cbc's in 3.00s
Doing aes-128-cbc for 3s on 1024 size blocks: 43179 aes-128-cbc's in 3.00s
Doing aes-128-cbc for 3s on 2048 size blocks: 29671 aes-128-cbc's in 3.00s
Doing aes-128-cbc for 3s on 4096 size blocks: 21178 aes-128-cbc's in 3.00s
Doing aes-128-cbc for 3s on 8192 size blocks: 13253 aes-128-cbc's in 3.00s
Doing aes-128-cbc for 3s on 16384 size blocks: 7477 aes-128-cbc's in 3.00s
OpenSSL 1.1.1a  20 Nov 2018
built on: Wed May 22 06:38:44 2019 UTC
options:bn(64,32) rc4(char) des(long) aes(partial) idea(int) blowfish(ptr) 
compiler: arm-poky-linux-gnueabi-gcc  -march=armv7-a -mthumb -mfpu=neon -mfloat-abi=hard -mcpu=cortex-a9 -fstack-protector-strong  -D_FORTIFY_SOURCE=2 -Wformat -Wformat-security -Werror=format-security --sysroot=recipe-sysroot -O2 -pipe -g -feliminate-unused-debug-types -fdebug-prefix-map= -fdebug-prefix-map= -fdebug-prefix-map= -DOPENSSL_USE_NODELETE -DOPENSSL_PIC -DOPENSSL_CPUID_OBJ -DOPENSSL_BN_ASM_MONT -DOPENSSL_BN_ASM_GF2m -DSHA1_ASM -DSHA256_ASM -DSHA512_ASM -DKECCAK1600_ASM -DAES_ASM -DBSAES_ASM -DGHASH_ASM -DECP_NISTZ256_ASM -DPOLY1305_ASM -DNDEBUG
The 'numbers' are in 1000s of bytes per second processed.
type             16 bytes     64 bytes    256 bytes    512 bytes   1024 bytes   2048 bytes   4096 bytes   8192 bytes  16384 bytes
aes-128-cbc        436.29k     1733.82k     6735.36k    12027.56k    14738.43k    20255.40k    28915.03k    36189.53k    40834.39k
```

