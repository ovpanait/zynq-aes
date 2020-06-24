`include "aes.vh"

module cipher(
	input                            clk,
	input                            reset,
	input                            en,

	input [`BLK_S-1:0]               plaintext,
	input [`Nb-1:0]                  rounds_total,
	input [`ROUND_KEY_BITS-1:0]      key,

	output reg [`BLK_S-1:0]          ciphertext,
	output reg [`Nb-1:0]             round_key_no,
	output reg                       en_o
);

`include "aes_common.vh"

// --------------------- AES Cipher functions ---------------------

/* ============================================================================
 *
 * The SubBytes transformation consists of:
 *  (i)   byte by byte substitution of the state array using the following rule
 *                            sij = sbox[sij]
 *
 * ========================================================================= */
function [`BLK_S-1:0] sub_bytes(input [`BLK_S-1:0] blk);
	integer i;
	for (i = 0; i < `BLK_S / `BYTE_S; i=i+1)
		sub_bytes[i*`BYTE_S +: `BYTE_S] = get_sbox(blk[i*`BYTE_S +: `BYTE_S]);
endfunction

/* ============================================================================
 *
 * The ShiftRows transformation consists of:
 *  (i)   not shifting the first row of the state array
 *  (ii)  circularly shifting the second row by one byte to the left
 *  (iii) circularly shifting the third row by two bytes to the left
 *  (iv)  circularly shifting the last row by three bytes to the left
 *
 * Input block:
 *  s00 s10 s20 s30  s01 s11 s21 s31  s02 s12 s22 s23  s03 s13 s23 s33
 *
 *   ----         ----             ----         ----
 *  | s00 s01 s02 s03 |           | s00 s01 s02 s03 |
 *  | s10 s11 s12 s13 |    ==>    | s11 s12 s13 s10 |
 *  | s20 s21 s22 s23 |           | s22 s23 s20 s21 |
 *  | s30 s31 s32 s33 |           | s33 s30 s31 s32 |
 *   ----         ----             ----         ----
 *
 * Output block:
 *  s00 s13 s22 s31  s01 s10 s23 s32  s02 s11 s20 s33  s03 s12 s21 s30
 *
 * ========================================================================= */
function [`BLK_S-1:0] shift_rows(input [`BLK_S-1:0] blk);
	reg [`WORD_S-1:0] w0, w1, w2, w3;
	reg [`WORD_S-1:0] ws0, ws1, ws2, ws3;
begin
	w0 = aes_word(blk, 0);
	w1 = aes_word(blk, 1);
	w2 = aes_word(blk, 2);
	w3 = aes_word(blk, 3);

	ws0 = {aes_byte(w0, 0), aes_byte(w1, 1), aes_byte(w2, 2), aes_byte(w3, 3)};
	ws1 = {aes_byte(w1, 0), aes_byte(w2, 1), aes_byte(w3, 2), aes_byte(w0, 3)};
	ws2 = {aes_byte(w2, 0), aes_byte(w3, 1), aes_byte(w0, 2), aes_byte(w1, 3)};
	ws3 = {aes_byte(w3, 0), aes_byte(w0, 1), aes_byte(w1, 2), aes_byte(w2, 3)};

	shift_rows = {ws0, ws1, ws2, ws3};
end
endfunction

/* ============================================================================
 *
 * The MixColumns transformation consists of:
 *  (i)   replacing each byte of a column by a function of all the bytes in the
 *        same column
 *
 * Input block:
 *  s00 s10 s20 s30  s01 s11 s21 s31  s02 s12 s22 s23  s03 s13 s23 s33
 *
 *   ----     ----     ----         ----     ----             ----
 *  | 02 03 01 01 |   | s00 s01 s02 s03 |   | 's00 's01 's02 's03 |
 *  | 01 02 03 01 | X | s10 s11 s12 s13 | = | 's10 's11 's12 's13 |
 *  | 01 01 02 03 |   | s20 s21 s22 s23 |   | 's20 's21 's22 's23 |
 *  | 03 01 01 02 |   | s30 s31 s32 s33 |   | 's30 's31 's32 's33 |
 *   ----     ----     ----         ----     ----             ----
 *
 * Output block:
 *  's00 's10 's20 's30  's01 's11 's21 's31  's02 's12 's22 's23  's03 's13 's23 's33
 *
 * NOTE: Multiplications and additions are in GF(2^128)
 *
 * ========================================================================= */
function [`WORD_S-1:0] mix_word(input [`WORD_S-1:0] word);
	reg [`BYTE_S-1:0] b0, b1, b2, b3;
	reg [`BYTE_S-1:0] mb0, mb1, mb2, mb3;
begin
	b0 = aes_byte(word, 0);
	b1 = aes_byte(word, 1);
	b2 = aes_byte(word, 2);
	b3 = aes_byte(word, 3);

	mb0 = gm2(b0) ^ gm3(b1) ^ b2 ^ b3;
	mb1 = b0 ^ gm2(b1) ^ gm3(b2) ^ b3;
	mb2 = b0 ^ b1 ^ gm2(b2) ^ gm3(b3);
	mb3 = gm3(b0) ^ b1 ^ b2 ^gm2(b3);

	mix_word = {mb0, mb1, mb2, mb3};
end
endfunction

function [`BLK_S-1:0] mix_cols(input [`BLK_S-1:0] blk);
	integer i;

	for (i = 0; i < `BLK_S / `WORD_S; i=i+1) begin
		mix_cols[i*`WORD_S +: `WORD_S] = mix_word(get_word(blk,i));
	end
endfunction

// --------------------- AES Cipher logic ---------------------

reg [`BLK_S-1:0] aes_state_sub_bytes;
reg [`BLK_S-1:0] aes_state_shift_rows;
reg [`BLK_S-1:0] aes_state_mix_cols;
reg [`BLK_S-1:0] aes_state_add_rkey;

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

		if (en)
			round_key_r_e <= 1'b1;

		if (round_key_r_e)
			round_key_no <= round_key_no + 1'b1;

		if (is_last_key) begin
			round_key_r_e <= 1'b0;
			round_key_no <= {`Nb{1'b0}};
		end
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
