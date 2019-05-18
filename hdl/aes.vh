`ifndef AES_H
`define AES_H

`define BYTE_S 8
`define WORD_S (4 * `BYTE_S)

`define Nb 4
`define Nk 4
`define Nr 10

`define KEY_S 128
`define BLK_S 128

`define SET_KEY_128 32'h10
`define ECB_ENCRYPT_128 32'h20
`define ECB_DECRYPT_128 32'h30

`endif
