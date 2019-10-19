`include "aes.vh"

module decipher (
        input clk,
        input reset,
        input en,

        input [0:`BLK_S-1] ciphertext,
        input [0:`KEY_S-1] round_key,

        output reg [0:`BLK_S-1] plaintext,
        output reg [0:`Nk-1] round_key_no,
        output reg en_o
);

reg [`Nk-1:0] round_no;

reg [0:`BLK_S-1] decrypt_inv_shift_rows;
reg [0:`BLK_S-1] decrypt_inv_sub_bytes;
reg [0:`BLK_S-1] decrypt_add_round_key;
reg [0:`BLK_S-1] decrypt_inv_mix_columns;

wire is_last_key;

wire decipher_first_round;
wire decipher_last_round;

reg decipher_round_en;
reg decipher_round_en_delay;

reg round_key_r_e;

`include "aes_functions.vh"

always @(*) begin
          decrypt_inv_shift_rows = inv_shift_rows(plaintext);
          decrypt_inv_sub_bytes = inv_sub_bytes(decrypt_inv_shift_rows);
          decrypt_add_round_key = decrypt_inv_sub_bytes ^ round_key;
          decrypt_inv_mix_columns = inv_mix_cols(decrypt_add_round_key);
end

always @(posedge clk) begin
	if (reset) begin
		decipher_round_en_delay <= 1'b0;
		decipher_round_en <= 1'b0;
		round_key_r_e <= 1'b0;
		round_key_no <= {`Nk{1'b0}};
	end else begin
		decipher_round_en_delay <= round_key_r_e;
		decipher_round_en <= decipher_round_en_delay;
		round_key_r_e <= 1'b0;

		if (en) begin
			round_key_r_e <= 1'b1;
			round_key_no <= `Nr;
		end

		if (round_key_no) begin
			round_key_no <= round_key_no - 1'b1;
			round_key_r_e <= 1'b1;
		end
	end
end

assign decipher_first_round = (round_no == {`Nk{1'b0}});
assign decipher_last_round = (round_no == `Nr);

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
		round_no <= {`Nk{1'b0}};
		en_o <= 1'b0;
	end else begin
		en_o <= 1'b0;

		if (decipher_round_en) begin
			round_no <= round_no + 1'b1;

			if (decipher_last_round) begin
				en_o <= 1'b1;
				round_no <= {`Nk{1'b0}};
			end
		end
	end
end

endmodule
