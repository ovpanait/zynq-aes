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
	'h000102030405060708090a0b0c0d0e0f,
	'hD6AA74FDD2AF72FADAA678F1D6AB76FE,
	'hB692CF0B643DBDF1BE9BC5006830B3FE,
	'hB6FF744ED2C2C9BF6C590CBF0469BF41,
	'h47F7F7BC95353E03F96C32BCFD058DFD,
	'h3CAAA3E8A99F9DEB50F3AF57ADF622AA,
	'h5E390F7DF7A69296A7553DC10AA31F6B,
	'h14F9701AE35FE28C440ADF4D4EA9C026,
	'h47438735A41C65B9E016BAF4AEBF7AD2,
	'h549932D1F08557681093ED9CBE2C974E,
	'h13111D7FE3944A17F307A78B4D2B30C5
};

reg [`ROUND_KEY_BITS-1:0] keys_256 [0:`Nr_256] = '{
	'h000102030405060708090a0b0c0d0e0f,
	'h101112131415161718191a1b1c1d1e1f,
	'hA573C29FA176C498A97FCE93A572C09C,
	'h1651A8CD0244BEDA1A5DA4C10640BADE,
	'hAE87DFF00FF11B68A68ED5FB03FC1567,
	'h6DE1F1486FA54F9275F8EB5373B8518D,
	'hC656827FC9A799176F294CEC6CD5598B,
	'h3DE23A75524775E727BF9EB45407CF39,
	'h0BDC905FC27B0948AD5245A4C1871C2F,
	'h45F5A66017B2D387300D4D33640A820A,
	'h7CCFF71CBEB4FE5413E6BBF0D261A7DF,
	'hF01AFAFEE7A82979D7A5644AB3AFE640,
	'h2541FE719BF500258813BBD55A721C0A,
	'h4E5A6699A9F24FE07E572BAACDF8CDEA,
	'h24FC79CCBF0979E9371AC23C6D68DE36
};

reg [`BLK_S-1:0] expected_plaintext = 'h00112233445566778899aabbccddeeff;

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
		ciphertext = 'h69c4e0d86a7b0430d8cdb78070b4c55a;
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
		ciphertext = 'h8ea2b7ca516745bfeafc49904b496089;
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
