`timescale 1ns/1ns
`define PERIOD 5

`include "queue.vh"

module tb_main();

// Include test helpers
`include "test_fc.vh"

// GCM Module signals
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

reg [AES_IV_BITS-1:0] iv;
reg  gcm_en;

reg  [AES_BLK_BITS-1:0] aes_alg_out_blk;
wire [AES_BLK_BITS-1:0] aes_alg_in_blk;
wire                    aes_alg_start;
reg                     aes_alg_done;

reg [GCM_BLK_BITS-1:0] gcm_in_blk;
reg                    gcm_valid;
wire                   gcm_ready;

wire [GCM_BLK_BITS-1:0] gcm_out_blk;
wire                    gcm_out_store_blk;
wire                    gcm_done;

reg key_expanded;

queue#(GCM_BLK_BITS) gcm_in_q;
queue#(GCM_BLK_BITS) gcm_out_q;

// AES algorithm signals
integer aes_out_cnt = 0;

reg [31:0] aes_wait;

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
	.gcm_out_store_blk(gcm_out_store_blk),

	.gcm_done(gcm_done)
);


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
	gcm_in_q = new();
	gcm_out_q = new();

	gcm_in_q.fill_from_file("gcm_in.data");
	gcm_in_q.print_queue();

	gcm_out_q.fill_from_file("gcm_out.data");
	gcm_out_q.print_queue();

	wait(reset) @(posedge clk);
	@(negedge clk) reset = 0;

	repeat(10) begin
		@(negedge clk);
		@(posedge clk);
	end

	key_expanded <= 1'b1;
end



always @(*) begin
	gcm_en = gcm_ready && gcm_valid;
end

/*
   * Feed GCM module with input blocks stored in the input queue (populated
   * from gcm_in.data file).
   *
 */
always @(posedge clk) begin
	if (reset) begin
		gcm_valid <= 1'b0;
	end else begin
		if (gcm_en || !gcm_valid) begin
			gcm_valid <= gcm_in_q.size() ? 1'b1 : 1'b0;

			if (gcm_in_q.size())
				gcm_in_blk <= gcm_in_q.pop_front();
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

always @(posedge clk) begin
	if (gcm_out_store_blk)
		tester #($size(gcm_out_blk))::verify_output(gcm_out_blk, gcm_out_q.pop_front());

	if (gcm_out_q.size == 0) begin
		$display("PASS!");
		$finish;
	end
end

endmodule
