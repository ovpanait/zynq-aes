`timescale 1ns/1ns
`define PERIOD 5

`include "queue.vh"

module tb_main();

// Include test helpers
`include "test_fc.vh"

// Top simulation signals
reg clk;
reg reset;
reg init_done;

// GCM Module signals
localparam integer AES_MAX_KEY_BITS = 256;
localparam integer AES_BLK_BITS = 128;
localparam integer AES_IV_BITS = 128;

localparam integer GCM_BLK_BITS = 128;
localparam integer SUBKEY_H_BITS = 128;
localparam integer AAD_BLK_BITS = 128;
localparam integer GHASH_BITS = 128;
localparam integer TAG_BITS = 128;
localparam integer ICB_BITS = 128;

reg [AES_IV_BITS-1:0] iv;
reg  gcm_en;

reg [GCM_BLK_BITS-1:0] gcm_in_blk;
reg                    gcm_valid;
wire                   gcm_ready;

wire [GCM_BLK_BITS-1:0] gcm_out_blk;
wire                    gcm_out_store_blk;
wire                    gcm_done;

reg key_expanded;

queue#(GCM_BLK_BITS) gcm_in_q;
queue#(GCM_BLK_BITS) gcm_out_q;
queue#(GCM_BLK_BITS) aes_keys_q;

// AES algorithm signals

reg aes_alg_en_cipher;
reg aes_alg_en_decipher;
reg aes_alg_en_key;

reg aes128_mode;
reg aes256_mode;

wire                        aes_op_in_progress;
wire [AES_BLK_BITS-1:0]     aes_alg_out_blk;
wire [AES_BLK_BITS-1:0]     aes_alg_in_blk;
wire                        aes_alg_en_cipher;
wire                        aes_alg_en_decipher;
wire                        aes_alg_done;
reg  [AES_MAX_KEY_BITS-1:0] aes_alg_key;

aes_top aes_alg (
	.clk(clk),
	.reset(reset),

	.en_cipher(aes_alg_en_cipher),
	.en_decipher(aes_alg_en_decipher),
	.en_key(aes_alg_en_key),

	.aes128_mode(aes128_mode),
	.aes256_mode(aes256_mode),

	.aes_key(aes_alg_key),
	.aes_in_blk(aes_alg_in_blk),

	.aes_out_blk(aes_alg_out_blk),
	.aes_op_in_progress(aes_op_in_progress),
	.en_o(aes_alg_done)
);

gcm DUT (
	.clk(clk),
	.reset(reset),

	.key_expanded(key_expanded),

	.aes_alg_en_cipher(aes_alg_en_cipher),
	.aes_alg_en_decipher(aes_alg_en_decipher),
	.aes_alg_out_blk(aes_alg_out_blk),
	.aes_alg_in_blk(aes_alg_in_blk),
	.aes_alg_done(aes_alg_done),

	.gcm_in_blk(gcm_in_blk),
	.gcm_valid(gcm_valid),
	.gcm_ready(gcm_ready),

	.gcm_out_blk(gcm_out_blk),
	.gcm_out_store_blk(gcm_out_store_blk),

	.gcm_done(gcm_done)
);


// Simulation sequence

task setup_test_data(input string fn);
	integer fd;
	string key;
	reg [GCM_BLK_BITS-1:0] data;

	// Populate GCM input data queue and AES key queue
	fd = $fopen(fn, "r");
	if (!fd) begin
		$display("ERROR: File %s not found!", fn);
		$finish;
	end

	while (!$feof(fd)) begin
		$fscanf(fd, "%s %h\n", key, data);

		if (key == "K") // AES KEY
			aes_keys_q.push_back(data);
		else if (key == "DOUT" || key == "T") // DATA_OUT or TAG
			gcm_out_q.push_back(data);
		else // Input data (IV, AADLEN, AAD, DATA_IN)
			gcm_in_q.push_back(data);
	end
	$fclose(fd);

	// DEBUG
	aes_keys_q.print_queue();
	gcm_in_q.print_queue();
	gcm_out_q.print_queue();
endtask

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
	aes_keys_q = new();

	setup_test_data("gcm_vectors.data");

	wait(reset) @(posedge clk);
	@(negedge clk) reset = 0;

	repeat(10) begin
		@(negedge clk);
		@(posedge clk);
	end

	init_done <= 1'b1;
end


always @(*) begin
	gcm_en = gcm_ready && gcm_valid;
end

/*
   * Feed GCM module with input blocks stored in the input queue (populated
   * from gcm_in.data file).
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
   * AES algorithm control logic.
   * KEY needs to be expanded before any GCM operation.
 */
always @(posedge clk) begin
	if (reset) begin
		key_expanded <= 1'b0;
		aes_alg_en_key <= 1'b0;

		aes128_mode <= 1'b0;
		aes256_mode <= 1'b0;
	end else begin
		// Only 128-bit keys support for now
		aes128_mode <= 1'b1;
		aes256_mode <= 1'b0;

		aes_alg_en_key <= 1'b0;

		// TODO: simplify this?
		if (init_done && aes_keys_q.size() && !key_expanded &&
			!aes_alg_en_key && !aes_op_in_progress) begin
			// Only 128-bit keys support for now
			aes_alg_key <= {aes_keys_q.pop_front(), {128{1'b0}}};
			aes_alg_en_key <= 1'b1;
		end

		if (!key_expanded && aes_alg_done)
			key_expanded <= 1'b1;

		if (gcm_done)
			key_expanded <= 1'b0;
	end
end

/*
   * Check results against precomputed values in gcm_out_q queue.
 */
always @(posedge clk) begin
	if (gcm_out_store_blk)
		if (!tester #($size(gcm_out_blk))::verify_output(gcm_out_blk, gcm_out_q.pop_front()))
			$finish;

	if (gcm_out_q.size == 0) begin
		$display("PASS!");
		$finish;
	end
end

endmodule
