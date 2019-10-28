`timescale 1ns/1ns
`define PERIOD 5

`include "aes.vh"

module tb_main();

reg clk;
reg reset;
reg en;

reg  [`KEY_S-1:0] prev_key;
wire [`KEY_S-1:0] round_key;
wire [3:0] round_key_addr;

wire w_e;
wire en_o;

round_key DUT (
	.clk(clk),
	.reset(reset),
	.en(en),

	.key(prev_key),
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
	 en = 1;
	 prev_key =  {
		8'h75, 8'h46, 8'h20, 8'h67,
		8'h6E, 8'h75, 8'h4B, 8'h20,
		8'h79, 8'h6D, 8'h20, 8'h73,
		8'h74, 8'h61, 8'h68, 8'h54
	};
	end

	@(negedge clk) en = 0;

	@(posedge en_o);

	$display("Test PASSED!");

	@(negedge clk);
	@(negedge clk)
	tester #($size(en_o))::verify_output(en_o, 1'b0);

	@(negedge clk) reset = 1;
	@(negedge clk);

	$finish;
end

reg [`KEY_S-1:0] expected_round_key [0:`Nr] = '{
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

always @(round_key) begin
	if (w_e == 1'b1) begin
		if (!tester #($size(round_key))::verify_output(round_key, expected_round_key[round_key_addr])) begin
			$display("Test FAILED!");
			$finish;
		end
	end
end

endmodule
