`include "aes.vh"

module cipher(
	input                   clk,
	input                   reset,
	input                   en,

	input [0:`BLK_S-1]      plaintext,
	input [0:`KEY_S-1]      key,

	output reg [0:`BLK_S-1] ciphertext,
	output reg [0:`Nk-1]    round_key_no,
	output reg              en_o
);

reg [0:`KEY_S-1] aes_state_sub_bytes;
reg [0:`KEY_S-1] aes_state_shift_rows;
reg [0:`KEY_S-1] aes_state_mix_cols;
reg [0:`KEY_S-1] aes_state_add_rkey;

`include "aes_functions.vh"

always @(*) begin
	aes_state_sub_bytes = sub_bytes(ciphertext);
	aes_state_shift_rows = shift_rows(aes_state_sub_bytes);
	aes_state_mix_cols = mix_cols(aes_state_shift_rows);
	aes_state_add_rkey = aes_state_mix_cols ^ key;
end

reg [`Nk-1:0] round_no;
reg round_key_r_e;
reg cipher_round_en;

wire cipher_first_round;
wire cipher_last_round;
wire is_last_key;

assign cipher_first_round = (round_no == {`Nk{1'b0}});
assign cipher_last_round = (round_no == `Nr);
assign is_last_key = (round_key_no == `Nr);

always @(posedge clk) begin
	if (reset) begin
		round_key_r_e <= 1'b0;
		round_key_no <= {`Nk{1'b0}};
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
			round_key_no <= {`Nk{1'b0}};
	end
end

always @(posedge clk) begin
	if (reset) begin
		ciphertext <= {`BLK_S{1'b0}};
	end else begin
		if (cipher_round_en) begin
			if (cipher_first_round)
				ciphertext <= plaintext ^ key;
			else if (cipher_last_round)
				ciphertext <= aes_state_shift_rows ^ key;
			else
				ciphertext <= aes_state_add_rkey;
		end
	end
end

always @(posedge clk) begin
	if (reset) begin
		round_no <= {`Nk{1'b0}};
		en_o <= 1'b0;
	end else begin
		en_o <= 1'b0;

		if (cipher_round_en)
			round_no <= round_no + 1'b1;

		if (cipher_last_round) begin
			en_o <= 1'b1;
			round_no <= {`Nk{1'b0}};
		end
	end
end

endmodule
