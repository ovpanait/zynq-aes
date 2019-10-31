`include "aes.vh"

module cipher(
	input                   clk,
	input                   reset,
	input                   en,

	input [`BLK_S-1:0]      plaintext,
	input [`Nb-1:0]         rounds_total,
	input [`KEY_S-1:0]      key,

	output reg [`BLK_S-1:0] ciphertext,
	output reg [`Nb-1:0]    round_key_no,
	output reg              en_o
);

`include "aes_common.vh"

// --------------------- AES Cipher functions ---------------------

function [`BLK_S-1:0] sub_bytes(input [`BLK_S-1:0] blk);
	integer i;

	for (i = 0; i < `BLK_S / `BYTE_S; i=i+1)
		sub_bytes[i*`BYTE_S +: `BYTE_S] = get_sbox(blk[i*`BYTE_S +: `BYTE_S]);
endfunction

function [`BLK_S-1:0] shift_rows(input [`BLK_S-1:0] blk);
	integer i, j, k;

	for (j = 0; j < `BLK_S / `BYTE_S; j=j+4) begin
		for (i=j, k=j; i < `BLK_S / `BYTE_S; i=i+1, k=k+5)
			shift_rows[i*`BYTE_S +: `BYTE_S] = blk_get_byte(blk, k % 16);
	end
endfunction

function [`WORD_S-1:0] mix_word(input [`WORD_S-1:0] word);
	reg [`BYTE_S-1:0] byte0;
	reg [`BYTE_S-1:0] byte1;
	reg [`BYTE_S-1:0] byte2;
	reg [`BYTE_S-1:0] byte3;
begin
	byte0 = get_byte(word, 0);
	byte1 = get_byte(word, 1);
	byte2 = get_byte(word, 2);
	byte3 = get_byte(word, 3);

	mix_word[0*`BYTE_S +: `BYTE_S] = gm2(byte0) ^ gm3(byte1) ^ byte2 ^ byte3;
	mix_word[1*`BYTE_S +: `BYTE_S] = byte0 ^ gm2(byte1) ^ gm3(byte2) ^ byte3;
	mix_word[2*`BYTE_S +: `BYTE_S] = byte0 ^ byte1 ^ gm2(byte2) ^ gm3(byte3);
	mix_word[3*`BYTE_S +: `BYTE_S] = gm3(byte0) ^ byte1 ^ byte2 ^gm2(byte3);
end
endfunction

function [`BLK_S-1:0] mix_cols(input [`BLK_S-1:0] blk);
	integer i;

	for (i = 0; i < `BLK_S / `WORD_S; i=i+1) begin
		mix_cols[i*`WORD_S +: `WORD_S] = mix_word(get_word(blk,i));
	end
endfunction

// --------------------- AES Cipher functions ---------------------

reg [`KEY_S-1:0] aes_state_sub_bytes;
reg [`KEY_S-1:0] aes_state_shift_rows;
reg [`KEY_S-1:0] aes_state_mix_cols;
reg [`KEY_S-1:0] aes_state_add_rkey;

always @(*) begin
	aes_state_sub_bytes = sub_bytes(ciphertext);
	aes_state_shift_rows = shift_rows(aes_state_sub_bytes);
	aes_state_mix_cols = mix_cols(aes_state_shift_rows);
	aes_state_add_rkey = aes_state_mix_cols ^ key;
end

reg [`Nb-1:0] round_no;
reg round_key_r_e;
reg cipher_round_en;

wire cipher_first_round;
wire cipher_last_round;
wire is_last_key;

assign cipher_first_round = (round_no == {`Nb{1'b0}});
assign cipher_last_round = (round_no == rounds_total);
assign is_last_key = (round_key_no == rounds_total);

always @(posedge clk) begin
	if (reset) begin
		round_key_r_e <= 1'b0;
		round_key_no <= {`Nb{1'b0}};
		cipher_round_en <= 1'b0;
	end else begin
		cipher_round_en <= round_key_r_e;
		round_key_r_e <= 1'b0;

		// ?!
		if (en || (round_key_no && !is_last_key))
			round_key_r_e <= 1'b1;

		if (round_key_r_e)
			round_key_no <= round_key_no + 1'b1;

		if (is_last_key)
			round_key_no <= {`Nb{1'b0}};
	end
end

always @(posedge clk) begin
	if (cipher_round_en) begin
		if (cipher_first_round)
			ciphertext <= plaintext ^ key;
		else if (cipher_last_round)
			ciphertext <= aes_state_shift_rows ^ key;
		else
			ciphertext <= aes_state_add_rkey;
	end
end

always @(posedge clk) begin
	if (reset) begin
		round_no <= {`Nb{1'b0}};
		en_o <= 1'b0;
	end else begin
		en_o <= cipher_round_en && cipher_last_round;

		if (cipher_round_en) begin
			round_no <= round_no + 1'b1;

			if (cipher_last_round)
				round_no <= {`Nb{1'b0}};
		end
	end
end

endmodule
