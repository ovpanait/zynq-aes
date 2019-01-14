`ifndef AES_H
 `define AES_H

 `define BYTE_S 8
 `define WORD_S (4 * `BYTE_S)

 `define Nb 4
 `define Nk 4
 `define Nr 10
 `define KEY_S 128

 `define byte0(x) x[0*`BYTE_S +: `BYTE_S]
 `define byte1(x) x[1*`BYTE_S +: `BYTE_S]
 `define byte2(x) x[2*`BYTE_S +: `BYTE_S]
 `define byte3(x) x[3*`BYTE_S +: `BYTE_S]

 `define get_sbox(x) sbox[x*`BYTE_S +: `BYTE_S]
 `define get_rcon(x) rcon[x*`BYTE_S +: `BYTE_S]

`endif
