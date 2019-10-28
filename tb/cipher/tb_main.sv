`timescale 1ns/1ns
`define PERIOD 5

`include "aes.vh"

module tb_main();

integer ret;

// Module instantiation
reg clk;
reg reset;
reg en;

reg [`BLK_S-1:0]  plaintext;
reg [`KEY_S-1:0]  key;

wire [3:0]        round_key_no;
wire [`BLK_S-1:0] ciphertext;
wire              en_o;

cipher DUT (
	.clk(clk),
	.reset(reset),
	.en(en),

	.plaintext(plaintext),
	.key(key),

	.ciphertext(ciphertext),
	.round_key_no(round_key_no),
	.en_o(en_o)
);

`include "test_fc.vh"

integer i;

reg [`KEY_S-1:0] key_sram [0:`Nr] = '{
	`KEY_S'h754620676e754b20796d207374616854,
	`KEY_S'h93a279d6e6e459b188911291f1fc32e2,
	`KEY_S'hfaf73aa0695543768fb11ac707200856,
	`KEY_S'hfb1e03c301e9396368bc7a15e70d60d2,
	`KEY_S'h5b495214a05751d7a1be68b4c90212a1,
	`KEY_S'h699b42c632d210d292854105333b29b1,
	`KEY_S'h4e0e2eac27956c6a15477cb887c23dbd,
	`KEY_S'h6a31a8b2243f861e03aaea7416ed96cc,
	`KEY_S'h6c4b9556067a3de42245bbfa21ef518e,
	`KEY_S'hd8cbf1f7b48064a1b2fa594590bfe2bf,
	`KEY_S'h266f313bfea4c0cc4a24a46df8defd28
};

reg [`BLK_S-1:0] expected_ciphertext = `BLK_S'h3ad7021ab3992240f62014575f50c329;

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
		plaintext =  {
			8'h6F, 8'h77, 8'h54, 8'h20,
			8'h65, 8'h6E, 8'h69, 8'h4E,
			8'h20, 8'h65, 8'h6E, 8'h4F,
			8'h20, 8'h6F, 8'h77, 8'h54
		};
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
