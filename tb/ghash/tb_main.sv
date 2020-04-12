`timescale 1ns/1ns
`define PERIOD 5

module tb_main();

// Include test helpers
`include "test_fc.vh"

// Module instantiation
localparam integer GFM_CYCLES = 8;
localparam integer GHASH_BITS = 128;
localparam integer SUBKEY_BITS = 128;

reg clk;
reg reset;
reg en;

reg [GHASH_BITS-1:0] g_prev;
reg [SUBKEY_BITS-1:0] subkey_H;
reg [GHASH_BITS-1:0] data_block;

wire [GHASH_BITS-1:0] ghash;
wire done;

ghash #(
	.GFM_CYCLES(GFM_CYCLES),
	.GHASH_BITS(GHASH_BITS),
	.SUBKEY_BITS(SUBKEY_BITS)
) DUT (
	.clk(clk),
	.reset(reset),
	.en(en),

	.g_prev(g_prev),
	.data_block(data_block),
	.subkey_H(subkey_H),

	.ghash(ghash),
	.done(done)
);

// Simulation inputs/outputs
reg [GHASH_BITS-1:0] data_arr[] = {
	'h7d924cfd37b3d046a96eb5e132042405
};

reg [GHASH_BITS-1:0] ghash_arr[] = {
	'h00000000000000000000000000000000
};

reg [GHASH_BITS-1:0] ghash_next_arr[] = {
	'h0c33e33e3288ca631ca47544293d03ee
};

// Simulation sequence
initial begin
	clk <= 0;
	forever #(`PERIOD) clk = ~clk;
end

initial begin
	reset <= 1;
	@(posedge clk);
	@(negedge clk) reset = 0;
end

initial begin
	wait(reset) @(posedge clk);
	@(negedge clk) reset = 0;

	@(negedge clk) begin
		g_prev = ghash_arr[0];
		subkey_H = 'hfe62256362600ac766636f962bb05f66;
		data_block = data_arr[0];
		en = 1'b1;
	end

	@(negedge clk) begin
		en = 1'b0;
	end

	@(posedge done);
	@(negedge clk) begin
		`VERIFY(ghash, ghash_next_arr[0]);
		$display("TEST PASSED!");
		$finish;
	end
end

endmodule
