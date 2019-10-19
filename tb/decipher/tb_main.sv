`timescale 1ns/1ns
`define PERIOD 5

`include "aes.vh"

module tb_main();

integer ret;

reg clk;
reg reset;
reg en;

reg [`ROUND_KEY_BITS-1:0] round_key;
reg [`BLK_S-1:0]          ciphertext;
reg [`Nb-1:0]             rounds_total;

wire [`BLK_S-1:0] plaintext;
wire [`Nb-1:0]    round_key_no;
wire              en_o;

decipher DUT (
	.clk(clk),
	.reset(reset),
	.en(en),

	.rounds_total(rounds_total),
	.ciphertext(ciphertext),
	.round_key(round_key),

	.plaintext(plaintext),
	.round_key_no(round_key_no),
	.en_o(en_o)
);

`include "test_fc.vh"

integer i;

reg [`ROUND_KEY_BITS-1:0] keys_128 [0:`Nr_128] = '{
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

reg [`ROUND_KEY_BITS-1:0] keys_256 [0:`Nr_256] = '{
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

reg [`BLK_S-1:0] expected_plaintext = 'hffeeddccbbaa99887766554433221100;

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
	wait(reset) @(posedge clk);
	@(negedge clk) reset = 0;

	@(negedge clk) begin
		en = 1;
		rounds_total = `Nr_128;
		ciphertext = 'h5ac5b47080b7cdd830047b6ad8e0c469;
	end

	@(negedge clk) begin
	 en = 0;
	end

	@(posedge DUT.en_o);
	@(negedge clk);

	ret = tester #($size(expected_plaintext))::verify_output(DUT.plaintext, expected_plaintext);
	if (!ret) begin
		$display("Test decipher (128-bit key): FAIL");
		$finish;
	end

	@(negedge clk) begin
		en = 1;
		rounds_total = `Nr_256;
		ciphertext = 'h8960494b9049fceabf456751cab7a28e;
	end

	@(negedge clk) begin
	 en = 0;
	end

	@(posedge DUT.en_o);
	@(negedge clk);

	ret = tester #($size(expected_plaintext))::verify_output(DUT.plaintext, expected_plaintext);
	if (!ret) begin
		$display("Test decipher (256-bit key): FAIL");
		$finish;
	end

	$display("Test decipher: PASS");

	@(negedge clk) reset = 1;
	@(negedge clk);

	$stop;
end

// simulate key sram behavior
always @(posedge clk) begin
	if (rounds_total == `Nr_128)
		round_key <= keys_128[round_key_no];
	else
		round_key <= keys_256[round_key_no];
end

endmodule
