`include "aes.vh"

/*
 * Generic Verilog module for Galois Field Multiplication.
 */
module gfm #(
	// GF(2^GFM_BITS) finite field
	parameter integer GFM_BITS = 128,

	// Latency in clock cycles for one multiplication
	parameter integer GFM_CYCLES = 8,

	/* The default polynomial for GHASH function of AES GCM mode is:
	 * x^128 + x^7 + x^2 + x + 1
	 * 1 0000 0000 ... 0000 1000 0111
	 * ^                            ^
	 * 128..........................0
	 *
	 * Reverse it to match LSB ----> MSB implementation.
	 */
	parameter reg [GFM_BITS-1:0] POLYNOMIAL = 'he1000000000000000000000000000000
)(
	input                      clk,
	input                      reset,
	input                      en,

	input [GFM_BITS-1:0]       a,
	input [GFM_BITS-1:0]       b,

	output reg [GFM_BITS-1:0]  result,
	output reg                 done
);

localparam ROUND_WIDTH = GFM_BITS;

integer i = 0;

reg compute;
reg [ROUND_WIDTH-1:0] round;

reg [GFM_BITS:0] op1;
reg [GFM_BITS:0] op2;
reg [GFM_BITS:0] op1_next;
reg [GFM_BITS:0] op2_next;
reg [GFM_BITS-1:0] result_next;

always @(*) begin
	result_next = result;
	op1_next = op1;
	op2_next = op2;

	for (i = 0; i < (GFM_BITS / GFM_CYCLES); i=i+1) begin
		result_next = result_next ^ (op2_next[GFM_BITS-1] ? op1_next : {GFM_BITS{1'b0}});
		op1_next = (op1_next >> 1) ^ (op1_next[0] ? POLYNOMIAL : {GFM_BITS{1'b0}});
		op2_next = op2_next << 1;
	end
end

always @(posedge clk) begin
	if (reset) begin
		done <= 1'b0;
		compute <= 1'b0;
		round <= {ROUND_WIDTH{1'b0}};
	end else begin
		done <= 1'b0;

		if (en) begin
			compute <= 1'b1;
			round <= {ROUND_WIDTH{1'b0}};
		end

		if (compute) begin
			round <= round + 'h1;

			if (round == GFM_CYCLES-1) begin
				done <= 1'b1;
				compute <= 1'b0;
			end
		end
	end
end

always @(posedge clk) begin
	if (reset) begin
		op1 <= {GFM_BITS{1'b0}};
		op2 <= {GFM_BITS{1'b0}};
		result <= {GFM_BITS{1'b0}};
	end else begin
		if (en) begin
			op2 <= b;
			op1 <= a;
			result <= {GFM_BITS{1'b0}};
		end

		if (compute) begin
			op1 <= op1_next;
			op2 <= op2_next;
			result <= result_next;
		end
	end
end
endmodule

/*
 * GHASH module
 */

module ghash #(
	parameter integer GFM_CYCLES = 8,
	parameter integer GHASH_BITS = 128,
	parameter integer SUBKEY_BITS = 128
)(
	input                          clk,
	input                          reset,
	input                          en,

	input [GHASH_BITS-1:0]         g_prev,
	input [GHASH_BITS-1:0]         data_block,
	input [SUBKEY_BITS-1:0]        subkey_H,

	output [GHASH_BITS-1:0]        ghash,
	output                         done
);

localparam integer GFM_BITS = 128;
localparam reg [GFM_BITS-1:0] POLYNOMIAL = 'he1000000000000000000000000000000;

wire [GFM_BITS-1:0] gfm_result;
reg  [GFM_BITS-1:0] g_i;
reg  [GFM_BITS-1:0] subkey_H_reg;
wire gfm_done;
reg  gfm_en;

assign ghash = gfm_result;
assign done = gfm_done;

always @(posedge clk) begin
	gfm_en <= en;

	if (en) begin
		g_i <= g_prev ^ data_block;
		subkey_H_reg <= subkey_H;
	end
end

gfm #(
	.GFM_BITS(GFM_BITS),
	.GFM_CYCLES(GFM_CYCLES),
	.POLYNOMIAL(POLYNOMIAL)
) DUT (
	.clk(clk),
	.reset(reset),
	.en(gfm_en),

	.a(g_i),
	.b(subkey_H_reg),

	.result(gfm_result),
	.done(gfm_done)
);

//`define GHASH_SIM_VERBOSE
`ifdef GHASH_SIM_VERBOSE
always @(posedge clk) begin
	if (en) begin
		$display("GHASH: Hashing");
		$display("       Subkey:  %H", subkey_H);
		$display("       G_PREV:  %H", g_prev);
		$display("       DATA  :  %H", data_block);
	end

	if (done) begin
		$display("GHASH: hash: %H", ghash);
	end
end
`endif

endmodule

/*
  * GCTR module
*/
module gctr(
	input                       clk,
	input                       reset,
	input                       en,

	input [`BLK_S-1:0]          icb,
	input [`BLK_S-1:0]          data_blk,

	input [`BLK_S-1:0]          aes_alg_out_blk,
	input                       aes_alg_done,
	output reg [`BLK_S-1:0]     aes_alg_in_blk,
	output reg                  aes_alg_start,

	output reg [`BLK_S-1:0]     gctr_out_blk,
	output reg [`BLK_S-1:0]     gctr_icb_next,
	output reg                  gctr_busy,
	output reg                  gctr_done
);

reg [`BLK_S-1:0] data_blk_reg;

always @(posedge clk) begin
	if (en) begin
		aes_alg_in_blk <= icb;
		data_blk_reg <= data_blk;

		gctr_icb_next <= icb + 1'b1;
	end

	aes_alg_start <= en;

	gctr_out_blk <= data_blk_reg ^ aes_alg_out_blk;
	gctr_done <= aes_alg_done && gctr_busy;
end

always @(posedge clk) begin
	if (reset) begin
		gctr_busy <= 1'b0;
	end else begin
		if (en)
			gctr_busy <= 1'b1;

		if (gctr_done) begin
			gctr_busy <= 1'b0;
		end
	end
end

//`define GCTR_SIM_VERBOSE
`ifdef GCTR_SIM_VERBOSE
always @(posedge clk) begin
	if (en) begin
		$display("GCTR: Starting GCTR operation:");
		$display("                        icb : %H", icb);
		$display("                        data: %H", data_blk);
	end

	if (gctr_done) begin
		$display("GCTR: Computed block: %H", gctr_out_blk);
		$display("            icb next: %H", gctr_icb_next);
	end
end
`endif

endmodule

