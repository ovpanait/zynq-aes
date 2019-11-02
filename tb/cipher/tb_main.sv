`timescale 1ns/1ns
`define PERIOD 5

`include "aes.vh"

module tb_main();

integer ret;

// Module instantiation
reg clk;
reg reset;
reg en;

reg [`ROUND_KEY_BITS-1:0] key;
reg [`BLK_S-1:0]          plaintext;
reg [`Nb-1:0]             rounds_total;

wire [`BLK_S-1:0] ciphertext;
wire [`Nb-1:0]    round_key_no;
wire              en_o;

cipher DUT (
	.clk(clk),
	.reset(reset),
	.en(en),

	.rounds_total(rounds_total),
	.plaintext(plaintext),
	.key(key),

	.ciphertext(ciphertext),
	.round_key_no(round_key_no),
	.en_o(en_o)
);

`include "test_fc.vh"

integer i;

reg [`ROUND_KEY_BITS-1:0] key_sram [0:`Nr_128] = '{
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

reg [`BLK_S-1:0] expected_ciphertext = 'h5ac5b47080b7cdd830047b6ad8e0c469;

initial begin
	clk <= 0;
	forever #(`PERIOD) clk = ~clk;
end

initial begin
	reset <= 0;
	@(posedge clk); //may need several cycles for reset
	@(negedge clk) reset = 1;
end

initial begin
	wait(reset) @(posedge clk);
	@(negedge clk) reset = 0;

	@(negedge clk) begin
		en = 1;
		rounds_total = `Nr_128;
		plaintext = 'hffeeddccbbaa99887766554433221100;
	end

	@(negedge clk) begin
	 en = 0;
	end

	@(posedge DUT.en_o);
	@(negedge clk);

	ret = tester #($size(expected_ciphertext))::verify_output(DUT.ciphertext, expected_ciphertext);

	if (ret)
		$display("Test cipher: PASS");
	else
		$display("Test cipher: FAIL");

	@(negedge clk) reset = 1;
	@(negedge clk);

	$stop;
end

// simulate key sram behavior
always @(posedge clk) begin
	 key <= key_sram[round_key_no];
end

endmodule
