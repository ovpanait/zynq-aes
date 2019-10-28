`include "aes.vh"

module round_key(
	input                   clk,
	input                   reset,
	input                   en,

	input      [`KEY_S-1:0] key,

	output reg [3:0]        round_key_addr,
	output reg [`KEY_S-1:0] round_key,
	output reg              w_e,

	output reg              en_o
);

wire [`WORD_S - 1:0] prev_key_arr[0:`Nk];

reg [`WORD_S-1:0] round_key_tmp_arr[0:`Nk];
reg [`WORD_S-1:0] subbytes_tmp;
reg [`BYTE_S-1:0] g0;
reg [`WORD_S-1:0] g;

reg [3:0] round_no;
wire round_key_en;
genvar i;

`include "aes_functions.vh"

localparam rcon = {
	8'h36, 8'h1B, 8'h80, 8'h40, 8'h20, 8'h10, 8'h08, 8'h04,
	8'h02, 8'h01, 8'h8D
};

function [`BYTE_S-1:0] get_rcon;
	input [`BYTE_S-1:0] index;

	get_rcon = rcon[index*`BYTE_S +: `BYTE_S];
endfunction

generate
for (i=0; i < `Nk; i=i+1) begin
	assign prev_key_arr[i] = round_key[i*`WORD_S +: `WORD_S];
end
endgenerate

always @(*) begin
	subbytes_tmp = {
		get_sbox(get_byte(prev_key_arr[`Nk-1], 0)),
		get_sbox(get_byte(prev_key_arr[`Nk-1], 3)),
		get_sbox(get_byte(prev_key_arr[`Nk-1], 2)),
		get_sbox(get_byte(prev_key_arr[`Nk-1], 1))
	};

	g0 = get_byte(subbytes_tmp, 0) ^ get_rcon(round_no);
	g = {
		get_byte(subbytes_tmp, 3),
		get_byte(subbytes_tmp, 2),
		get_byte(subbytes_tmp, 1),
		g0
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
			round_key_tmp_arr[3],
			round_key_tmp_arr[2],
			round_key_tmp_arr[1],
			round_key_tmp_arr[0]
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
