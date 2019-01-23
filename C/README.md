Clear, step-by-step implementation of AES encryption algorithm in C.

POC 128-bit plaintext encryption:
```sh
$ make test
$ ./test
plaintext:
54776f204f6e65204e696e652054776f

key:
5468617473206d79204b756e67204675

ciphertext:
29c3505f571420f6402299b31a02d73a
```
Print AES internal state matrix representation for each step:
```sh
$ make clean
$ make DEBUG=1 test
$ ./test
```
