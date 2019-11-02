`timescale 1ns/1ns
`define PERIOD 5

`include "aes.vh"

module tb_main();

reg clk;
reg reset;
reg en;

reg aes128_mode;
reg aes256_mode;

reg  [`Nb-1:0]             rounds_total;
reg  [`KEY_S-1:0]          aes_key;
wire [`ROUND_KEY_BITS-1:0] round_key;
wire [`Nb-1:0]             round_key_addr;

wire w_e;
wire en_o;

round_key DUT (
	.clk(clk),
	.reset(reset),
	.en(en),

	.aes128_mode(aes128_mode),
	.aes256_mode(aes256_mode),

	.rounds_total(rounds_total),
	.key(aes_key),
	.round_key(round_key),
	.round_key_addr(round_key_addr),
	.w_e(w_e),

	.en_o(en_o)
);

`include "test_fc.vh"

initial begin
	clk <= 0;
	forever #(`PERIOD) clk = ~clk;
end

initial begin
	reset <= 0;
	@(posedge clk);
	@(negedge clk) reset = 1;
end

initial begin
	wait(reset)
	@(posedge clk);
	@(negedge clk) reset = 0;

	@(negedge clk) begin
	aes128_mode = 1'b1;
	aes256_mode = 1'b0;
	en = 1;

	rounds_total = `Nr_128;
	aes_key =  {
		8'h00, 8'h00, 8'h00, 8'h00,
		8'h00, 8'h00, 8'h00, 8'h00,
		8'h00, 8'h00, 8'h00, 8'h00,
		8'h00, 8'h00, 8'h00, 8'h00,
		8'h0f, 8'h0e, 8'h0d, 8'h0c,
		8'h0b, 8'h0a, 8'h09, 8'h08,
		8'h07, 8'h06, 8'h05, 8'h04,
		8'h03, 8'h02, 8'h01, 8'h00
	};
	end

	@(negedge clk) en = 0;

	@(posedge en_o);
	$display("aes 128-bit key expansion: Test PASSED!");

	@(negedge clk) begin
	aes128_mode = 1'b0;
	aes256_mode = 1'b1;
	en = 1;

	rounds_total = `Nr_256;
	aes_key =  {
		8'h1f, 8'h1e, 8'h1d, 8'h1c,
		8'h1b, 8'h1a, 8'h19, 8'h18,
		8'h17, 8'h16, 8'h15, 8'h14,
		8'h13, 8'h12, 8'h11, 8'h10,
		8'h0f, 8'h0e, 8'h0d, 8'h0c,
		8'h0b, 8'h0a, 8'h09, 8'h08,
		8'h07, 8'h06, 8'h05, 8'h04,
		8'h03, 8'h02, 8'h01, 8'h00

	};
	end

	@(negedge clk) en = 0;

	@(posedge en_o);

	$display("aes 256-bit key expansion: Test PASSED!");

	@(negedge clk);
	@(negedge clk)
	tester #($size(en_o))::verify_output(en_o, 1'b0);

	@(negedge clk) reset = 1;
	@(negedge clk);

	$finish;
end

reg [`ROUND_KEY_BITS-1:0] expected_round_keys_128 [0:`Nr_128] = '{
	'h0f0e0d0c0b0a09080706050403020100,
	'hfe76abd6f178a6dafa72afd2fd74aad6,
	'hfeb3306800c59bbef1bd3d640bcf92b6,
	'h41bf6904bf0c596cbfc9c2d24e74ffb6,
	'hfd8d05fdbc326cf9033e3595bcf7f747,
	'haa22f6ad57aff350eb9d9fa9e8a3aa3c,
	'h6b1fa30ac13d55a79692a6f77d0f395e,
	'h26c0a94e4ddf0a448ce25fe31a70f914,
	'hd27abfaef4ba16e0b9651ca435874347,
	'h4e972cbe9ced9310685785f0d1329954,
	'hc5302b4d8ba707f3174a94e37f1d1113
};

reg [`ROUND_KEY_BITS-1:0] expected_round_keys_256 [0:`Nr_256] = '{
	'h0f0e0d0c0b0a09080706050403020100,
	'h1f1e1d1c1b1a19181716151413121110,
	'h9cc072a593ce7fa998c476a19fc273a5,
	'hdeba4006c1a45d1adabe4402cda85116,
	'h6715fc03fbd58ea6681bf10ff0df87ae,
	'h8d51b87353ebf875924fa56f48f1e16d,
	'h8b59d56cec4c296f1799a7c97f8256c6,
	'h39cf0754b49ebf27e7754752753ae23d,
	'h2f1c87c1a44552ad48097bc25f90dc0b,
	'h0a820a64334d0d3087d3b21760a6f545,
	'hdfa761d2f0bbe61354feb4be1cf7cf7c,
	'h40e6afb34a64a5d77929a8e7fefa1af0,
	'h0a1c725ad5bb13882500f59b71fe4125,
	'heacdf8cdaa2b577ee04ff2a999665a4e,
	'h36de686d3cc21a37e97909bfcc79fc24
};

always @(round_key) begin
	if (w_e == 1'b1 && aes128_mode) begin
		if (!tester #($size(round_key))::verify_output(round_key, expected_round_keys_128[round_key_addr])) begin
			$display("Test FAILED!");
			$finish;
		end
	end

	if (w_e == 1'b1 && aes256_mode) begin
		if (!tester #($size(round_key))::verify_output(round_key, expected_round_keys_256[round_key_addr])) begin
			$display("Test FAILED!");
			$finish;
		end
	end
end

endmodule
