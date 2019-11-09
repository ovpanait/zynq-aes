`ifndef AES_H
`define AES_H

`define BYTE_S 8
`define WORD_S (4 * `BYTE_S)

`define Nb 4

`define Nk_128 4
`define Nr_128 10

`define Nk_256 8
`define Nr_256 14

`define ROUND_KEY_WORDS 4
`define ROUND_KEY_BITS (`ROUND_KEY_WORDS * `WORD_S)

`define AES128_KEY_BITS (`Nk_128 * `WORD_S)
`define AES256_KEY_BITS (`Nk_256 * `WORD_S)

`define KEY_S `AES256_KEY_BITS
`define BLK_S 128
`define IV_BITS 128

// AES controller bit flags
`define KEY_EXPANSION_OP_BIT 0
`define ENCRYPTION_OP_BIT    1
`define DECRYPTION_OP_BIT    2
`define KEY_128_BIT          3
`define KEY_192_BIT          4
`define KEY_256_BIT          5
`define ECB_MODE_BIT         6
`define CBC_MODE_BIT         7
`define CTR_MODE_BIT         8
`define PCBC_MODE_BIT        9

`endif
