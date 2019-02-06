`ifndef AES_H
`define AES_H

`define BYTE_S 8
`define WORD_S (4 * `BYTE_S)

`define Nb 4
`define Nk 4
`define Nr 10

`define KEY_S 128
`define BLK_S 128

`define CTRL_S `WORD_S
`define CTRL_ENCRYPT 32'hF3F3F3F3
`define CTRL_KEY 32'hA1A1A1A1

`define STATUS_S `WORD_S
`define S_KEY_BIT 1
`define S_CIPHER_BIT 2

`define S_KEY_MASK (32'h1 << (`S_KEY_BIT - 1))
`define S_CIPHER_MASK (32'h1 << (`S_CIPHER_BIT - 1))
`endif
