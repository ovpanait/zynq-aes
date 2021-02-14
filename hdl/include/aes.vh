`ifndef AES_H
`define AES_H

`define BYTE_S 8
`define WORD_S (4 * `BYTE_S)

`define Nb 4

`define Nk_128 4
`define Nr_128 10

`define Nk_256 8
`define Nr_256 14

`define CMD_BITS 32

`define ROUND_KEY_WORDS 4
`define ROUND_KEY_BITS (`ROUND_KEY_WORDS * `WORD_S)

`define AES128_KEY_BITS (`Nk_128 * `WORD_S)
`define AES256_KEY_BITS (`Nk_256 * `WORD_S)

`define KEY_S `AES256_KEY_BITS
`define BLK_S 128
`define IV_BITS 128

`endif
