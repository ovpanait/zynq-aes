`include "aes.vh"

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
`define CFB_MODE_BIT         10
`define OFB_MODE_BIT         11
`define GCM_MODE_BIT         12

function is_128bit_key(input [`WORD_S-1:0] cmd);
	is_128bit_key = cmd[`KEY_128_BIT];
endfunction

function is_256bit_key(input [`WORD_S-1:0] cmd);
	is_256bit_key = cmd[`KEY_256_BIT];
endfunction

function is_encryption(input [`WORD_S-1:0] cmd);
	is_encryption = cmd[`ENCRYPTION_OP_BIT];
endfunction

function is_decryption(input [`WORD_S-1:0] cmd);
	is_decryption = cmd[`DECRYPTION_OP_BIT];
endfunction

function is_key_expansion(input [`WORD_S-1:0] cmd);
	is_key_expansion = cmd[`KEY_EXPANSION_OP_BIT];
endfunction

function is_CBC_op(input [`WORD_S-1:0] cmd);
	is_CBC_op = cmd[`CBC_MODE_BIT];
endfunction

function is_CTR_op(input [`WORD_S-1:0] cmd);
	is_CTR_op = cmd[`CTR_MODE_BIT];
endfunction

function is_CFB_op(input [`WORD_S-1:0] cmd);
	is_CFB_op = cmd[`CFB_MODE_BIT];
endfunction

function is_OFB_op(input [`WORD_S-1:0] cmd);
	is_OFB_op = cmd[`OFB_MODE_BIT];
endfunction

function is_ECB_op(input [`WORD_S-1:0] cmd);
	is_ECB_op = cmd[`ECB_MODE_BIT];
endfunction

function is_PCBC_op(input [`WORD_S-1:0] cmd);
	is_PCBC_op = cmd[`PCBC_MODE_BIT];
endfunction

function is_GCM_op(input [`WORD_S-1:0] cmd);
	is_GCM_op = cmd[`GCM_MODE_BIT];
endfunction

function [`WORD_S-1:0] set_key_expansion_bit(input [`WORD_S-1:0] cmd);
	set_key_expansion_bit = cmd | (1 << `KEY_EXPANSION_OP_BIT);
endfunction

function [`WORD_S-1:0] set_key_128_bit(input [`WORD_S-1:0] cmd);
	set_key_128_bit = cmd | (1 << `KEY_128_BIT);
endfunction

function [`WORD_S-1:0] set_key_256_bit(input [`WORD_S-1:0] cmd);
	set_key_256_bit = cmd | (1 << `KEY_256_BIT);
endfunction

function [`WORD_S-1:0] set_encryption_op_bit(input [`WORD_S-1:0] cmd);
	set_encryption_op_bit = cmd | (1 << `ENCRYPTION_OP_BIT);
endfunction

function [`WORD_S-1:0] set_decryption_op_bit(input [`WORD_S-1:0] cmd);
	set_decryption_op_bit = cmd | (1 << `DECRYPTION_OP_BIT);
endfunction

function [`WORD_S-1:0] set_ECB_mode_bit(input [`WORD_S-1:0] cmd);
	set_ECB_mode_bit = cmd | (1 << `ECB_MODE_BIT);
endfunction

function [`WORD_S-1:0] set_CBC_mode_bit(input [`WORD_S-1:0] cmd);
	set_CBC_mode_bit = cmd | (1 << `CBC_MODE_BIT);
endfunction

function [`WORD_S-1:0] set_CTR_mode_bit(input [`WORD_S-1:0] cmd);
	set_CTR_mode_bit = cmd | (1 << `CTR_MODE_BIT);
endfunction

function [`WORD_S-1:0] set_CFB_mode_bit(input [`WORD_S-1:0] cmd);
	set_CFB_mode_bit = cmd | (1 << `CFB_MODE_BIT);
endfunction

function [`WORD_S-1:0] set_OFB_mode_bit(input [`WORD_S-1:0] cmd);
	set_OFB_mode_bit = cmd | (1 << `OFB_MODE_BIT);
endfunction

function [`WORD_S-1:0] set_PCBC_mode_bit(input [`WORD_S-1:0] cmd);
	set_PCBC_mode_bit = cmd | (1 << `PCBC_MODE_BIT);
endfunction

function [`WORD_S-1:0] set_GCM_mode_bit(input [`WORD_S-1:0] cmd);
	set_GCM_mode_bit = cmd | (1 << `GCM_MODE_BIT);
endfunction

/*
  * blk_rev8: Reverse a block byte by byte
  *
  * AES standard:
  *  0x7d 0x92 0x4c 0xfd 0x37 0xb3 0xd0 0x46 0xa9 0x6e 0xb5 0xe1 0x32 0x04 0x24 0x05
  *
  * Linux Kernel Buffer:
  *  0x7d 0x92 0x4c 0xfd 0x37 0xb3 0xd0 0x46 0xa9 0x6e 0xb5 0xe1 0x32 0x04 0x24 0x05
  *
  *  Hardware Engine:
  *  0x05 0x24 0x04 0x32 0xe1 0xb5 0x6e 0xa9 0x46 0xd0 0xb3 0x37 0xfd 0x4c 0x92 0x7d
  *
  * As indicated above, due to the way data is transferred from the kernel, we
  * end up having the bytes in the opposite direction compared to the AES
  * specification.
  *
  * blk_rev8 is used to change the byte direction of input blocks to align with
  * the AES specification and also to reverse the blocks before sending them
  * out on the bus.
  *
 */
function [`BLK_S-1:0] blk_rev8(input [`BLK_S-1:0] blk);
	integer i;

	for (i = 0; i < `BLK_S / 8; i=i+1)
		blk_rev8[i*8 +: 8] = blk[(`BLK_S / 8 - i - 1)*8+: 8];
endfunction
