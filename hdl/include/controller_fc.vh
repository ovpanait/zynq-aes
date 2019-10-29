`ifndef CONTROLLER_FC_VH
`define CONTROLLER_FC_VH

`include "aes.vh"

function is_CBC_op(input [`WORD_S-1:0] cmd);
	begin
		is_CBC_op = (cmd == `CBC_ENCRYPT_128 || cmd == `CBC_DECRYPT_128);
	end
endfunction

function is_CBC_enc(input [`WORD_S-1:0] cmd);
	begin
		is_CBC_enc = (cmd == `CBC_ENCRYPT_128);
	end
endfunction

function is_CBC_dec(input [`WORD_S-1:0] cmd);
	begin
		is_CBC_dec = (cmd == `CBC_DECRYPT_128);
	end
endfunction

function is_cipher_op(input [`WORD_S-1:0] cmd);
	is_cipher_op = (cmd == `CBC_ENCRYPT_128) || (cmd == `ECB_ENCRYPT_128);
endfunction

function is_decipher_op(input [`WORD_S-1:0] cmd);
	is_decipher_op = (cmd == `CBC_DECRYPT_128) || (cmd == `ECB_DECRYPT_128);
endfunction

function is_key_exp_op(input [`WORD_S-1:0] cmd);
	is_key_exp_op = (cmd == `SET_KEY_128);
endfunction

`endif
