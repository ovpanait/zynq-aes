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

reg controller_out_ready;
reg key_expanded;

reg encrypt_flag;
reg decrypt_flag;

queue#(GCM_BLK_BITS) gcm_in_q;
queue#(GCM_BLK_BITS) gcm_out_q;
// Stores info that is not directly passed to the GCM module
// (encryption/decryption flags and key)
queue#(GCM_BLK_BITS) metadata_q;

// AES algorithm signals

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

	.encrypt_flag(encrypt_flag),
	.decrypt_flag(decrypt_flag),

	.controller_out_ready(controller_out_ready),
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
reg [GCM_BLK_BITS-1:0] op;

function op_get_encrypt_bit(input [GCM_BLK_BITS-1:0] op);
	op_get_encrypt_bit = op[0];
endfunction

function op_get_decrypt_bit(input [GCM_BLK_BITS-1:0] op);
	op_get_decrypt_bit = op[1];
endfunction

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

		if (key == "OP" || key == "K")
			metadata_q.push_back(data);
		else if (key == "DOUT" || key == "T") // DATA_OUT or TAG
			gcm_out_q.push_back(data);
		else // Input data (IV, AADLEN, AAD, DATA_IN)
			gcm_in_q.push_back(data);
	end
	$fclose(fd);
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
	gcm_in_q = new();
	gcm_out_q = new();
	metadata_q = new();

	setup_test_data("gcm_vectors.data");

	reset <= 1;
	@(posedge clk);
	@(negedge clk) reset = 0;
end

localparam GET_OP_TYPE = 2'b00;
localparam EXPAND_KEY  = 2'b01;
localparam SEND_DATA   = 2'b10;

reg [1:0] state;
reg [1:0] state_next;

always @(*) begin
	state_next = state;

	case (state)
	GET_OP_TYPE: begin
		state_next = EXPAND_KEY;
	end
	EXPAND_KEY: begin
		if (!key_expanded)
			state_next = SEND_DATA;
	end
	SEND_DATA: begin
		if (gcm_done)
			state_next = GET_OP_TYPE;
	end
	default:
		state_next = GET_OP_TYPE;
	endcase
end

always @(posedge clk) begin
	if (reset) begin
		state <= GET_OP_TYPE;
	end else begin
		state <= state_next;
	end
end

always @(*) begin
	gcm_en = gcm_ready && gcm_valid;
end

always @(posedge clk) begin
	if (reset) begin
		gcm_valid <= 1'b0;
	end else begin
		if (state == SEND_DATA && (gcm_en || !gcm_valid)) begin
			gcm_valid <= gcm_in_q.size() ? 1'b1 : 1'b0;

			if (gcm_in_q.size())
				gcm_in_blk <= gcm_in_q.pop_front();
		end
	end
end

always @(posedge clk) begin
	if (reset) begin
		controller_out_ready <= 1'b0;
		key_expanded <= 1'b0;
		aes_alg_en_key <= 1'b0;

		aes128_mode <= 1'b0;
		aes256_mode <= 1'b0;

		encrypt_flag <= 1'b0;
		decrypt_flag <= 1'b0;
	end else begin
		controller_out_ready <= 1'b1;

		// Only 128-bit keys support for now
		aes128_mode <= 1'b1;
		aes256_mode <= 1'b0;

		aes_alg_en_key <= 1'b0;

		if (state == GET_OP_TYPE) begin
			op = metadata_q.pop_front();
			encrypt_flag <= op_get_encrypt_bit(op);
			decrypt_flag <= op_get_decrypt_bit(op);
		end

		if (state == EXPAND_KEY && !key_expanded) begin
			aes_alg_key <= {metadata_q.pop_front(), {128{1'b0}}};
			aes_alg_en_key <= 1'b1;
		end

		if (!key_expanded && aes_alg_done) begin
			key_expanded <= 1'b1;
		end

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
