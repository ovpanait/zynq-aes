`ifndef AES_H
`define AES_H

`define BYTE_S 8
`define WORD_S (4 * `BYTE_S)

`define Nb 4
`define Nk 4
`define Nr 10

`define KEY_S 128
`define BLK_S 128
`define IV_BITS 128

`define KEY_EXPANSION_OP_BIT 0
`define ENCRYPTION_OP_BIT    1
`define DECRYPTION_OP_BIT    2
`define KEY_128_BIT          3
`define KEY_192_BIT          4
`define KEY_256_BIT          5
`define ECB_MODE_BIT         6
`define CBC_MODE_BIT         7

`endif
