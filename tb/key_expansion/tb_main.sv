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
		'h000102030405060708090a0b0c0d0e0f,
		'h00000000000000000000000000000000
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
		'h000102030405060708090a0b0c0d0e0f,
		'h101112131415161718191a1b1c1d1e1f
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

reg [`ROUND_KEY_BITS-1:0] expected_round_keys_256 [0:`Nr_256] = '{
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
