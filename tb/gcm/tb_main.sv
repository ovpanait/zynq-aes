`timescale 1ns/1ns
`define PERIOD 5

module tb_main();

// Include test helpers
`include "test_fc.vh"

// Module instantiation
localparam integer AES_BLK_BITS = 128;
localparam integer GCM_BLK_BITS = 128;
localparam integer SUBKEY_H_BITS = 128;
localparam integer AAD_BLK_BITS = 128;
localparam integer AES_IV_BITS = 128;
localparam integer GHASH_BITS = 128;
localparam integer TAG_BITS = 128;
localparam integer ICB_BITS = 128;

reg clk;
reg reset;
reg en;

reg [AES_IV_BITS-1:0] iv;
reg iv_en;

reg key_expanded;

reg  [AES_BLK_BITS-1:0] aes_alg_out_blk;
wire [AES_BLK_BITS-1:0] aes_alg_in_blk;
wire                    aes_alg_start;
reg                     aes_alg_done;

reg [GCM_BLK_BITS-1:0] gcm_in_blk;
reg                    gcm_valid;
wire                   gcm_ready;

wire [GCM_BLK_BITS-1:0] gcm_out_blk;
wire                    gcm_op_done;

wire [TAG_BITS-1:0] gcm_tag;
wire                gcm_tag_done;

// Simulation signals
integer iv_cnt = 0;
integer aad_cnt = 0;
integer aes_in_cnt = 0;
integer aes_out_cnt = 0;

reg  gcm_en;
reg  iv_send;
reg  aad_send;
reg  aes_send;

reg [31:0] aes_wait;

gcm DUT (
	.clk(clk),
	.reset(reset),

	.key_expanded(key_expanded),

	.aes_alg_out_blk(aes_alg_out_blk),
	.aes_alg_in_blk(aes_alg_in_blk),
	.aes_alg_done(aes_alg_done),
	.aes_alg_start(aes_alg_start),

	.gcm_in_blk(gcm_in_blk),
	.gcm_valid(gcm_valid),
	.gcm_ready(gcm_ready),

	.gcm_out_blk(gcm_out_blk),
	.gcm_tag(gcm_tag),
	.gcm_tag_done(gcm_tag_done),
	.gcm_op_done(gcm_op_done)
);

// Simulation inputs/outputs
reg [AES_BLK_BITS-1:0] aes_out_data_arr[] = {
	'hfe62256362600ac766636f962bb05f66,
	'h69488eec2890c5c6bd0781a54b252bdc,
	'h49b9736f9d82114b06a9ba85b6b5b4e4,
	'h71aa8c16a26a6a402b6876f24245301c,
	'hfe62256362600ac766636f962bb05f66,
	'h69488eec2890c5c6bd0781a54b252bdc,
	'h49b9736f9d82114b06a9ba85b6b5b4e4,
	'h71aa8c16a26a6a402b6876f24245301c

};

reg [AES_BLK_BITS-1:0] aes_in_data_arr[] = {
	'hbb2bac67a4709430c39c2eb9acfabc0d,
	'h456c80d30aa1734e57997d548a8f0603,
	'hbb2bac67a4709430c39c2eb9acfabc0d,
	'h456c80d30aa1734e57997d548a8f0603

};

reg [AAD_BLK_BITS-1:0] aad_arr[] = {
	'h00000000000001800000000000000100,
	'h7d924cfd37b3d046a96eb5e132042405,
	'hc8731e06509787bbeb41f25827574649,
	'h5e884d69871f77634c584bb007312234,
	'h00000000000001800000000000000100,
	'h7d924cfd37b3d046a96eb5e132042405,
	'hc8731e06509787bbeb41f25827574649,
	'h5e884d69871f77634c584bb007312234
};

reg [AES_IV_BITS-1:0] iv_arr[] = {
	'h3e894ebb16ce82a53c3e05b200000000,
	'h3e894ebb16ce82a53c3e05b200000000
};

// Simulation sequence

initial begin
	$dumpfile("gcm.vcd");
	$dumpvars(1, DUT);
end

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

	repeat(10) begin
		@(negedge clk);
		@(posedge clk);
	end

	aes_gcm();
	aes_gcm();

	$finish;
end

task aes_gcm();
	// Signal key expansion
	@(negedge clk);
	key_expanded = 1'b1;

	// Send IV
	@(negedge clk);
	key_expanded = 1'b0;
	iv_send = 1'b1;

	// Wait for IV to be retrieved
	@(negedge clk);
	wait (gcm_valid == 1'b0);

	// Send AAD
	@(negedge clk);
	iv_send = 1'b0;
	aad_send = 1'b1;

	// Wait for AAD data to be retrieved
	@(negedge clk);
	wait (gcm_valid == 1'b0);

	// Send AES blocks
	@(negedge clk);
	aad_send <= 1'b0;
	aes_send <= 1'b1;

	// Wait for AES blocks to be retrieved
	@(negedge clk);
	wait (gcm_valid == 1'b0);

	@(negedge clk);
	aes_send <= 1'b0;

	// Wait for tag to be generated
	@(negedge clk);
	wait(gcm_tag_done);
	$display("TAG: %H", gcm_tag);

	@(negedge clk);
endtask

always @(posedge clk) begin
	if (gcm_op_done) begin
		$display("C: %H", gcm_out_blk);
	end
end


always @(*) begin
	gcm_en = gcm_ready && gcm_valid;
end

always @(posedge clk) begin
	if (aad_send || aes_send || iv_send)
		gcm_valid <= 1'b1;

	if (iv_send) begin
		gcm_in_blk <= iv_arr[iv_cnt];
	end else if (aad_send) begin
		gcm_in_blk <= aad_arr[aad_cnt];
	end else if (aes_send) begin
		gcm_in_blk <= aes_in_data_arr[aes_in_cnt];
	end

	if (gcm_en) begin
		if (iv_send) begin
			iv_cnt++;
			gcm_valid <= 1'b0;
		end

		if (aad_send) begin
			if ((aad_cnt + 1) % 4 == 0) begin
				gcm_valid <= 1'b0;
			end

			aad_cnt++;
		end

		if (aes_send) begin
			if ((aes_in_cnt + 1) % 2 == 0)  begin
				gcm_valid <= 1'b0;
			end

			aes_in_cnt++;
		end
	end
end

/*
  * Simulate AES encryption behavior.
  *
 */
always @(posedge clk) begin
	if (reset) begin
		aes_alg_out_blk <= {AES_BLK_BITS{1'b0}};
		aes_wait <= {32{1'b0}};
		aes_alg_done <= 1'b0;
	end else begin
		aes_alg_done <= 1'b0;

		if (aes_alg_start || aes_wait) begin
			aes_wait <= aes_wait + 1'b1;
		end

		if (aes_wait == 16) begin
			aes_alg_out_blk <= aes_out_data_arr[aes_out_cnt];
			aes_alg_done <= 1'b1;
			aes_wait <= {32{1'b0}};

			aes_out_cnt++;
		end
	end
end

endmodule
