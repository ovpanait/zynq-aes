`include "aes.vh"

module decipher (
	input                      clk,
	input                      reset,
	input                      en,

	input [`ROUND_KEY_BITS-1:0] round_key,
	input [`BLK_S-1:0]          ciphertext,
	input [`Nb-1:0]             rounds_total,

	output reg [`BLK_S-1:0]     plaintext,
	output reg [`Nb-1:0]        round_key_no,
	output reg                  en_o
);

`include "aes_common.vh"

// ------------------------- AES Decipher functions -------------------------

/* ============================================================================
 *
 * The InvSubBytes transformation consists of:
 *  (i)   byte by byte substitution of the state array using the following rule
 *                            sij = rsbox[sij]
 *
 * ========================================================================= */
localparam rsbox = {
        8'h7D, 8'h0C, 8'h21, 8'h55, 8'h63, 8'h14, 8'h69, 8'hE1,
        8'h26, 8'hD6, 8'h77, 8'hBA, 8'h7E, 8'h04, 8'h2B, 8'h17,
        8'h61, 8'h99, 8'h53, 8'h83, 8'h3C, 8'hBB, 8'hEB, 8'hC8,
        8'hB0, 8'hF5, 8'h2A, 8'hAE, 8'h4D, 8'h3B, 8'hE0, 8'hA0,
        8'hEF, 8'h9C, 8'hC9, 8'h93, 8'h9F, 8'h7A, 8'hE5, 8'h2D,
        8'h0D, 8'h4A, 8'hB5, 8'h19, 8'hA9, 8'h7F, 8'h51, 8'h60,
        8'h5F, 8'hEC, 8'h80, 8'h27, 8'h59, 8'h10, 8'h12, 8'hB1,
        8'h31, 8'hC7, 8'h07, 8'h88, 8'h33, 8'hA8, 8'hDD, 8'h1F,
        8'hF4, 8'h5A, 8'hCD, 8'h78, 8'hFE, 8'hC0, 8'hDB, 8'h9A,
        8'h20, 8'h79, 8'hD2, 8'hC6, 8'h4B, 8'h3E, 8'h56, 8'hFC,
        8'h1B, 8'hBE, 8'h18, 8'hAA, 8'h0E, 8'h62, 8'hB7, 8'h6F,
        8'h89, 8'hC5, 8'h29, 8'h1D, 8'h71, 8'h1A, 8'hF1, 8'h47,
        8'h6E, 8'hDF, 8'h75, 8'h1C, 8'hE8, 8'h37, 8'hF9, 8'hE2,
        8'h85, 8'h35, 8'hAD, 8'hE7, 8'h22, 8'h74, 8'hAC, 8'h96,
        8'h73, 8'hE6, 8'hB4, 8'hF0, 8'hCE, 8'hCF, 8'hF2, 8'h97,
        8'hEA, 8'hDC, 8'h67, 8'h4F, 8'h41, 8'h11, 8'h91, 8'h3A,
        8'h6B, 8'h8A, 8'h13, 8'h01, 8'h03, 8'hBD, 8'hAF, 8'hC1,
        8'h02, 8'h0F, 8'h3F, 8'hCA, 8'h8F, 8'h1E, 8'h2C, 8'hD0,
        8'h06, 8'h45, 8'hB3, 8'hB8, 8'h05, 8'h58, 8'hE4, 8'hF7,
        8'h0A, 8'hD3, 8'hBC, 8'h8C, 8'h00, 8'hAB, 8'hD8, 8'h90,
        8'h84, 8'h9D, 8'h8D, 8'hA7, 8'h57, 8'h46, 8'h15, 8'h5E,
        8'hDA, 8'hB9, 8'hED, 8'hFD, 8'h50, 8'h48, 8'h70, 8'h6C,
        8'h92, 8'hB6, 8'h65, 8'h5D, 8'hCC, 8'h5C, 8'hA4, 8'hD4,
        8'h16, 8'h98, 8'h68, 8'h86, 8'h64, 8'hF6, 8'hF8, 8'h72,
        8'h25, 8'hD1, 8'h8B, 8'h6D, 8'h49, 8'hA2, 8'h5B, 8'h76,
        8'hB2, 8'h24, 8'hD9, 8'h28, 8'h66, 8'hA1, 8'h2E, 8'h08,
        8'h4E, 8'hC3, 8'hFA, 8'h42, 8'h0B, 8'h95, 8'h4C, 8'hEE,
        8'h3D, 8'h23, 8'hC2, 8'hA6, 8'h32, 8'h94, 8'h7B, 8'h54,
        8'hCB, 8'hE9, 8'hDE, 8'hC4, 8'h44, 8'h43, 8'h8E, 8'h34,
        8'h87, 8'hFF, 8'h2F, 8'h9B, 8'h82, 8'h39, 8'hE3, 8'h7C,
        8'hFB, 8'hD7, 8'hF3, 8'h81, 8'h9E, 8'hA3, 8'h40, 8'hBF,
        8'h38, 8'hA5, 8'h36, 8'h30, 8'hD5, 8'h6A, 8'h09, 8'h52 };

function [`BYTE_S-1:0] get_rsbox(input [`BYTE_S-1:0] index);
	get_rsbox = rsbox[index*`BYTE_S +: `BYTE_S];
endfunction

function [`BLK_S-1:0] inv_sub_bytes(input [`BLK_S-1:0] blk);
	integer i;

	for (i = 0; i < `BLK_S / `BYTE_S; i=i+1)
		inv_sub_bytes[i*`BYTE_S +: `BYTE_S] = get_rsbox(blk[i*`BYTE_S +: `BYTE_S]);
endfunction

/* ============================================================================
 *
 * The InvShiftRows transformation consists of:
 *  (i)   replacing each byte of a column by a function of all the bytes in the
 *        same column
 *
 * Input block:
 *  s00 s10 s20 s30  s01 s11 s21 s31  s02 s12 s22 s23  s03 s13 s23 s33
 *
 *   ----     ----     ----         ----     ----             ----
 *  | 0E 0B 0D 09 |   | s00 s01 s02 s03 |   | 's00 's01 's02 's03 |
 *  | 09 0E 0B 0D | X | s10 s11 s12 s13 | = | 's10 's11 's12 's13 |
 *  | 0D 09 0E 0B |   | s20 s21 s22 s23 |   | 's20 's21 's22 's23 |
 *  | 0B 0D 09 0E |   | s30 s31 s32 s33 |   | 's30 's31 's32 's33 |
 *   ----     ----     ----         ----     ----             ----
 *
 * Output block:
 *  's00 's10 's20 's30  's01 's11 's21 's31  's02 's12 's22 's23  's03 's13 's23 's33
 *
 * NOTE: Multiplications and additions are in GF(2^128)
 *
 * ========================================================================= */

function [`WORD_S-1:0] inv_mix_word(input [`WORD_S-1:0] word);
	reg [`BYTE_S-1:0]   byte0;
	reg [`BYTE_S-1:0]   byte1;
	reg [`BYTE_S-1:0]   byte2;
	reg [`BYTE_S-1:0]   byte3;
begin
	byte0 = get_byte(word, 0);
	byte1 = get_byte(word, 1);
	byte2 = get_byte(word, 2);
	byte3 = get_byte(word, 3);

	inv_mix_word[0*`BYTE_S +: `BYTE_S] = gm14(byte0) ^ gm11(byte1) ^ gm13(byte2) ^ gm9(byte3);
	inv_mix_word[1*`BYTE_S +: `BYTE_S] = gm9(byte0) ^ gm14(byte1) ^ gm11(byte2) ^ gm13(byte3);
	inv_mix_word[2*`BYTE_S +: `BYTE_S] = gm13(byte0) ^ gm9(byte1) ^ gm14(byte2) ^ gm11(byte3);
	inv_mix_word[3*`BYTE_S +: `BYTE_S] = gm11(byte0) ^ gm13(byte1) ^ gm9(byte2) ^ gm14(byte3);
end
endfunction

function [`BLK_S-1:0] inv_mix_cols(input [`BLK_S-1:0] blk);
	integer i;

	for (i = 0; i < `BLK_S / `WORD_S; i=i+1)
		inv_mix_cols[i*`WORD_S +: `WORD_S] = inv_mix_word(get_word(blk,i));
endfunction

/* ============================================================================
 *
 * The InvShiftRows transformation consists of:
 *  (i)   not shifting the first row of the state array
 *  (ii)  circularly shifting the second row by one byte to the right
 *  (iii) circularly shifting the third row by two bytes to the right
 *  (iv)  circularly shifting the last row by three bytes to the right
 *
 * Input block:
 *  s00 s10 s20 s30  s01 s11 s21 s31  s02 s12 s22 s23  s03 s13 s23 s33
 *
 *   ----         ----             ----         ----
 *  | s00 s01 s02 s03 |           | s00 s01 s02 s03 |
 *  | s10 s11 s12 s13 |    ==>    | s13 s10 s11 s12 |
 *  | s20 s21 s22 s23 |           | s22 s23 s20 s21 |
 *  | s30 s31 s32 s33 |           | s31 s32 s33 s30 |
 *   ----         ----             ----         ----
 *
 * Output block:
 *  s00 s13 s22 s31  s01 s10 s23 s32  s02 s11 s20 s33  s03 s12 s21 s30
 *
 * ========================================================================= */
function [`BLK_S-1:0] inv_shift_rows(input [`BLK_S-1:0] blk);
	integer i, j, k;

	for (j = 0; j < `BLK_S / `BYTE_S; j=j+4)
		for (i=j, k=j; i < `BLK_S / `BYTE_S; i=i+1, k=k+13)
			inv_shift_rows[i*`BYTE_S +: `BYTE_S] = blk_get_byte(blk, k % 16);
endfunction

// ------------------------- Decipher logic  ----------------------------------

reg [`Nb-1:0] round_no;

reg [`BLK_S-1:0] decrypt_inv_shift_rows;
reg [`BLK_S-1:0] decrypt_inv_sub_bytes;
reg [`BLK_S-1:0] decrypt_add_round_key;
reg [`BLK_S-1:0] decrypt_inv_mix_columns;

wire is_last_key;

wire decipher_first_round;
wire decipher_last_round;

reg decipher_round_en;

reg round_key_r_e;

always @(*) begin
          decrypt_inv_shift_rows = inv_shift_rows(plaintext);
          decrypt_inv_sub_bytes = inv_sub_bytes(decrypt_inv_shift_rows);
          decrypt_add_round_key = decrypt_inv_sub_bytes ^ round_key;
          decrypt_inv_mix_columns = inv_mix_cols(decrypt_add_round_key);
end

always @(posedge clk) begin
	if (reset) begin
		decipher_round_en <= 1'b0;
		round_key_r_e <= 1'b0;
		round_key_no <= {`Nb{1'b0}};
	end else begin
		decipher_round_en <= round_key_r_e;
		round_key_r_e <= 1'b0;

		if (en) begin
			round_key_r_e <= 1'b1;
			round_key_no <= rounds_total;
		end

		if (round_key_no) begin
			round_key_no <= round_key_no - 1'b1;
			round_key_r_e <= 1'b1;
		end
	end
end

assign decipher_first_round = (round_no == {`Nb{1'b0}});
assign decipher_last_round = (round_no == rounds_total);

always @(posedge clk) begin
	if (decipher_round_en) begin
		if (decipher_first_round)
			plaintext <= ciphertext ^ round_key;
		else if (decipher_last_round)
			plaintext <= decrypt_add_round_key;
		else
			plaintext <= decrypt_inv_mix_columns;
	end
end

always @(posedge clk) begin
	if (reset) begin
		round_no <= {`Nb{1'b0}};
		en_o <= 1'b0;
	end else begin
		en_o <= 1'b0;

		if (decipher_round_en) begin
			round_no <= round_no + 1'b1;

			if (decipher_last_round) begin
				en_o <= 1'b1;
				round_no <= {`Nb{1'b0}};
			end
		end
	end
end

endmodule
