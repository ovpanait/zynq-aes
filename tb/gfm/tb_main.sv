`timescale 1ns/1ns
`define PERIOD 5

module tb_main();

// Module instantiation
reg clk;
reg reset;
reg en;

localparam integer GFM_BITS = 128;
localparam integer GFM_CYCLES = 8;

localparam reg [GFM_BITS:0] op1 = 'h7d924cfd37b3d046a96eb5e132042405;
localparam reg [GFM_BITS:0] op2 = 'hfe62256362600ac766636f962bb05f66;
localparam reg [GFM_BITS-1:0] POLYNOMIAL = 'he1000000000000000000000000000000;

localparam EXPECTED_RESULT = 'h0c33e33e3288ca631ca47544293d03ee;

reg [GFM_BITS-1:0] a;
reg [GFM_BITS-1:0] b;
reg [GFM_BITS-1:0] result;

reg done;

gfm #(
	.GFM_BITS(GFM_BITS),
	.GFM_CYCLES(GFM_CYCLES),
	.POLYNOMIAL(POLYNOMIAL)
) DUT (
	.clk(clk),
	.reset(reset),
	.en(en),

	.a(a),
	.b(b),

	.result(result),
	.done(done)
);

`include "test_fc.vh"

integer i;

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
		a = op1;
		b = op2;
		en = 1'b1;
	end

	@(negedge clk) begin
		en = 1'b0;
	end

	@(posedge done);
	@(negedge clk) begin
		`VERIFY(result, EXPECTED_RESULT);
		$display("TEST PASSED!");
		$finish;
	end
end

endmodule
