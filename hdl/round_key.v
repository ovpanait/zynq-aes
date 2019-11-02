`include "aes.vh"

module round_key(
	input                             clk,
	input                             reset,
	input                             en,

	input                             aes128_mode,
	input                             aes256_mode,

	input      [`Nb-1:0]              rounds_total,
	input      [`KEY_S-1:0]           key,

	output reg [`Nb-1:0]              round_key_addr,
	output reg [`ROUND_KEY_BITS-1:0]  round_key,
	output reg                        w_e,

	output reg                        en_o
);

wire [`WORD_S - 1:0] prev_key_arr[0:`ROUND_KEY_WORDS];
reg  [`ROUND_KEY_BITS-1:0] round_key_next;
wire [`WORD_S-1:0] prev_sched_word;
reg  [`KEY_S-1:0]  prev_key;
reg  [`BYTE_S-1:0] g0;
reg [`WORD_S-1:0] g;

reg [`Nb-1:0] rcon_index;
reg [`Nb-1:0] round_no;
wire copy_initial_key;
wire round_key_en;
wire compute_g;
genvar i;

`include "aes_common.vh"

localparam rcon = {
	8'h36, 8'h1B, 8'h80, 8'h40, 8'h20, 8'h10, 8'h08, 8'h04,
	8'h02, 8'h01
};

function [`BYTE_S-1:0] get_rcon(input [`BYTE_S-1:0] index);
	get_rcon = rcon[index*`BYTE_S +: `BYTE_S];
endfunction

generate
for (i=0; i < `ROUND_KEY_WORDS; i=i+1) begin
	assign prev_key_arr[i] = prev_key[i*`WORD_S +: `WORD_S];
end
endgenerate

assign round_key_en = (en || round_no);
assign first_round = (round_no == 1'b0);
assign second_round = (round_no == 1'b1);
assign last_round = (round_no == rounds_total);
assign copy_initial_key = (first_round || (second_round && aes256_mode));

assign prev_sched_word = aes256_mode ?
                         prev_key[`AES256_KEY_BITS-1 : `AES256_KEY_BITS-`WORD_S] :
                         prev_key[`AES128_KEY_BITS-1 : `AES128_KEY_BITS-`WORD_S] ;
assign compute_g = copy_initial_key ? 1'b0 :
                   aes256_mode ? ~round_no[0]: 1'b1;

always @(posedge clk) begin
	if (copy_initial_key)
		prev_key <= key;
	else if (aes256_mode)
		prev_key <= {round_key_next, prev_key[`AES256_KEY_BITS-1 : `AES128_KEY_BITS]};
	else
		prev_key <= {{128{1'b0}}, round_key_next};
end

always @(*) begin
	g = prev_sched_word;

	if (compute_g) begin
		g = word2sbox(word_rotr(g));
		g0 = get_byte(g, 0) ^ get_rcon(rcon_index);
		g = {g[`BYTE_S +: `WORD_S - `BYTE_S], g0};
	end
	else begin
		g = word2sbox(g);
	end

	round_key_next[`WORD_S * 0 +: `WORD_S] = g ^ prev_key_arr[0];
	round_key_next[`WORD_S * 1 +: `WORD_S] = round_key_next[`WORD_S * 0 +: `WORD_S] ^ prev_key_arr[1];
	round_key_next[`WORD_S * 2 +: `WORD_S] = round_key_next[`WORD_S * 1 +: `WORD_S] ^ prev_key_arr[2];
	round_key_next[`WORD_S * 3 +: `WORD_S] = round_key_next[`WORD_S * 2 +: `WORD_S] ^ prev_key_arr[3];
end

always @(posedge clk) begin
	if (reset) begin
		rcon_index = {`Nb{1'b0}};
		round_no <= {`Nb{1'b0}};
		en_o <= 1'b0;
	end else begin
		en_o <= last_round;

		if (round_key_en) begin
			round_no <= round_no + 1'b1;
			if (compute_g)
				rcon_index <= rcon_index + 1'b1;
		end

		if (last_round) begin
			round_no <= {`Nb{1'b0}};
			rcon_index <= {`Nb{1'b0}};
		end
	end
end

always @(posedge clk) begin
	if (first_round)
		round_key <= key[`AES128_KEY_BITS-1 : 0];
	else if (aes256_mode && second_round)
		round_key <= key[`AES256_KEY_BITS-1 : `AES128_KEY_BITS];
	else begin
		round_key <= round_key_next;
	end
end

always @(posedge clk) begin
	if (reset) begin
		w_e <= 1'b0;
		round_key_addr <= {`Nb{1'b0}};
	end else begin
		w_e <= round_key_en;
		round_key_addr <= round_no;
	end
end

endmodule
