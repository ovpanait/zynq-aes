`include "aes.vh"

module round_key(
	 input                   clk,
	 input                   reset,
	 input                   en,

	 input [0:`KEY_S-1]      key,

	 output reg [0:`KEY_S-1] round_key,
	 output reg [0:3]        round_key_addr,
	 output reg              w_e,

	 output reg              en_o
 );

wire [0:`WORD_S - 1] prev_key_arr[0:`Nk];

reg [0:`WORD_S-1] round_key_tmp_arr[0:`Nk];
reg [0:`WORD_S-1] subbytes_tmp;
reg [0:`BYTE_S-1] g0;
reg [0:`WORD_S-1] g;

reg [0:3] round_no;
wire round_key_en;
genvar i;

`include "aes_functions.vh"

generate
for (i=0; i < `Nk; i=i+1) begin
	assign prev_key_arr[i] = round_key[i*`WORD_S +: `WORD_S];
end
endgenerate

always @(*) begin
	subbytes_tmp = {
		get_sbox(get_byte(prev_key_arr[`Nk-1], 1)),
		get_sbox(get_byte(prev_key_arr[`Nk-1], 2)),
		get_sbox(get_byte(prev_key_arr[`Nk-1], 3)),
		get_sbox(get_byte(prev_key_arr[`Nk-1], 0))
	};

	g0 = get_byte(subbytes_tmp, 0) ^ get_rcon(round_no);
	g = {
		g0,
		get_byte(subbytes_tmp, 1),
		get_byte(subbytes_tmp, 2),
		get_byte(subbytes_tmp, 3)
	};

	round_key_tmp_arr[0] = g ^ prev_key_arr[0];
	round_key_tmp_arr[1] = round_key_tmp_arr[0] ^ prev_key_arr[1];
	round_key_tmp_arr[2] = round_key_tmp_arr[1] ^ prev_key_arr[2];
	round_key_tmp_arr[3] = round_key_tmp_arr[2] ^ prev_key_arr[3];
end

assign round_key_en = (en || round_no);
assign first_round = (round_no == 1'b0);
assign last_round = (round_no == `Nr);

always @(posedge clk) begin
	if (reset) begin
		round_no <= {4{1'b0}};
		en_o <= 1'b0;
	end else begin
		en_o <= 1'b0;

		if (round_key_en)
			round_no <= round_no + 1'b1;

		if (last_round) begin
			round_no <= {4{1'b0}};
			en_o <= 1'b1;
		end
	end
end

always @(posedge clk) begin
	if (first_round)
		round_key <= key;
	else begin
		round_key <= {
			round_key_tmp_arr[0],
			round_key_tmp_arr[1],
			round_key_tmp_arr[2],
			round_key_tmp_arr[3]
		};
	end
end

always @(posedge clk) begin
	if (reset) begin
		w_e <= 1'b0;
		round_key_addr <= {4{1'b0}};
	end else begin
		w_e <= 1'b0;
		round_key_addr <= round_no;

		if (round_key_en)
			w_e <= 1'b1;
	end
end

endmodule
