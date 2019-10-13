`include "aes.vh"

module decipher (
        input clk,
        input reset,
        input en,

        input [0:`BLK_S-1] ciphertext,
        input [0:`KEY_S-1] round_key,

        output reg [0:`BLK_S-1] plaintext,
        output [0:`Nk-1] round_no,
        output reg en_o
);

reg [`Nk:0] _round_no;

reg [0:`BLK_S-1] decrypt_inv_shift_rows;
reg [0:`BLK_S-1] decrypt_inv_sub_bytes;
reg [0:`BLK_S-1] decrypt_add_round_key;
reg [0:`BLK_S-1] decrypt_inv_mix_columns;

wire decipher_first_round;
wire decipher_last_round;

reg decipher_round_en;
reg round_key_r_e;

`include "aes_functions.vh"

assign round_no = _round_no[`Nk-1:0];
assign decipher_first_round = (_round_no == `Nr - 1'b1);
assign decipher_last_round = (_round_no[`Nk] == 1'b1);

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
		_round_no <= {`Nk+1{1'b1}};
	end else begin
		decipher_round_en <= round_key_r_e;
		round_key_r_e <= 1'b0;

		if (en) begin
			round_key_r_e <= 1'b1;
			_round_no <= `Nr;
		end

		if (!decipher_last_round) begin
			_round_no <= round_no - 1'b1;
			round_key_r_e <= 1'b1;
		end
	end
end

always @(posedge clk) begin
	if (reset) begin
		plaintext <= {`BLK_S{1'b0}};
	end else begin
		if (decipher_round_en) begin
			if (decipher_first_round)
				plaintext <= ciphertext ^ round_key;
			else if (decipher_last_round)
				plaintext <= decrypt_add_round_key;
			else
				plaintext <= decrypt_inv_mix_columns;
		end
	end
end

always @(posedge clk) begin
	if (reset) begin
		en_o <= 1'b0;
	end else begin
		en_o <= 1'b0;

		if (decipher_round_en && decipher_last_round)
			en_o <= 1'b1;
	end
end

endmodule
