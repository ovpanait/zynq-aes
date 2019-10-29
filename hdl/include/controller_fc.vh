`ifndef CONTROLLER_FC_VH
`define CONTROLLER_FC_VH

`include "aes.vh"

function is_encryption;
	input [`WORD_S-1:0] cmd;

	is_encryption = cmd[`ENCRYPTION_OP_BIT];
endfunction

function is_decryption;
	input [`WORD_S-1:0] cmd;

	is_decryption = cmd[`DECRYPTION_OP_BIT];
endfunction

function is_key_expansion;
	input [`WORD_S-1:0] cmd;

	is_key_expansion = cmd[`KEY_EXPANSION_OP_BIT];
endfunction

function is_CBC_op;
	input [`WORD_S-1:0] cmd;

	is_CBC_op = cmd[`CBC_MODE_BIT];
endfunction

function is_CBC_enc;
	input [`WORD_S-1:0] cmd;

	is_CBC_enc = is_CBC_op(cmd) && is_encryption(cmd);
endfunction

function is_CBC_dec;
	input [`WORD_S-1:0] cmd;

	is_CBC_dec = is_CBC_op(cmd) && is_decryption(cmd);
endfunction

function [`WORD_S-1:0] set_key_expansion_bit;
	input [`WORD_S-1:0] cmd;

	set_key_expansion_bit = cmd | (1 << `KEY_EXPANSION_OP_BIT);
endfunction

function [`WORD_S-1:0] set_key_128_bit;
	input [`WORD_S-1:0] cmd;

	set_key_128_bit = cmd | (1 << `KEY_128_BIT);
endfunction

function [`WORD_S-1:0] set_encryption_op_bit;
	input [`WORD_S-1:0] cmd;

	set_encryption_op_bit = cmd | (1 << `ENCRYPTION_OP_BIT);
endfunction

function [`WORD_S-1:0] set_decryption_op_bit;
	input [`WORD_S-1:0] cmd;

	set_decryption_op_bit = cmd | (1 << `DECRYPTION_OP_BIT);
endfunction

function [`WORD_S-1:0] set_ECB_mode_bit;
	input [`WORD_S-1:0] cmd;

	set_ECB_mode_bit = cmd | (1 << `ECB_MODE_BIT);
endfunction

function [`WORD_S-1:0] set_CBC_mode_bit;
	input [`WORD_S-1:0] cmd;

	set_CBC_mode_bit = cmd | (1 << `CBC_MODE_BIT);
endfunction

`endif
