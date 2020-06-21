`include "aes.vh"

module aes_top(
	input                   clk,
	input                   reset,

	input                   en_cipher,
	input                   en_decipher,
	input                   en_key,

	input                   aes128_mode,
	input                   aes256_mode,

	input [`KEY_S-1:0]      aes_key,
	input [`BLK_S-1:0]      aes_in_blk,

	output [`BLK_S-1:0]     aes_out_blk,
	output reg              aes_op_in_progress,
	output                  en_o
);

reg  cipher_mode;
reg  decipher_mode;
reg  key_exp_mode;

wire [`ROUND_KEY_BITS-1:0] round_key_in;
reg  [`ROUND_KEY_BITS-1:0] round_key_out;

wire [`Nb-1:0] round_key_addr;
wire [`Nb-1:0] encrypt_round_no;
wire [`Nb-1:0] decrypt_round_no;

wire en_o_round_key;
wire en_o_cipher;
wire en_o_decipher;

wire [`BLK_S-1:0] __aes_out_blk_encrypt;
wire [`BLK_S-1:0] __aes_out_blk_decrypt;

wire [`Nb-1:0] rounds_total;

// BRAM signals
reg  [`ROUND_KEY_BITS-1:0] bram_w_data;
reg  [`Nb-1:0] bram_w_addr;
wire bram_w_e;

wire [`ROUND_KEY_BITS-1:0] bram_r_data;
reg  [`Nb-1:0] bram_r_addr;

always @(*) begin
	bram_r_addr = key_exp_mode ? round_key_addr    :
	              cipher_mode ? encrypt_round_no   :
	              decipher_mode ? decrypt_round_no :
	              {`Nb{1'b0}};
	bram_w_addr = bram_r_addr;

	round_key_out = bram_r_data;
	bram_w_data = round_key_in;
end

assign rounds_total = aes128_mode ? `Nr_128 : `Nr_256;

always @(posedge clk) begin
	if (reset) begin
		cipher_mode <= 1'b0;
		decipher_mode <= 1'b0;
		key_exp_mode <= 1'b0;
	end else begin
		if (en_cipher)
			cipher_mode <= 1'b1;

		if (en_decipher)
			decipher_mode <= 1'b1;

		if (en_key)
			key_exp_mode <= 1'b1;

		if (en_o) begin
			cipher_mode <= 1'b0;
			decipher_mode <= 1'b0;
			key_exp_mode <= 1'b0;
		end
	end
end

block_ram #(
        .ADDR_WIDTH(`Nb),
        .DATA_WIDTH(`ROUND_KEY_BITS)
) key_mem(
	.w_clk(clk),
	.r_clk(clk),

	.r_addr(bram_r_addr),
	.r_data(bram_r_data),

	.w_e(bram_w_e),
	.w_addr(bram_w_addr),
	.w_data(bram_w_data)
);

round_key round_key_gen(
        .clk(clk),
        .reset(reset),
        .en(en_key),

        .aes128_mode(aes128_mode),
        .aes256_mode(aes256_mode),

        .rounds_total(rounds_total),
        .key(aes_key),

        .round_key(round_key_in),
        .round_key_addr(round_key_addr),
        .w_e(bram_w_e),

        .en_o(en_o_round_key)
);

cipher encrypt_blk(
	.clk(clk),
	.reset(reset),
	.en(en_cipher),

	.rounds_total(rounds_total),
	.plaintext(aes_in_blk),
	.key(round_key_out),
	.round_key_no(encrypt_round_no),

	.ciphertext(__aes_out_blk_encrypt),
	.en_o(en_o_cipher)
);

decipher decrypt_blk(
        .clk(clk),
        .reset(reset),
        .en(en_decipher),

        .rounds_total(rounds_total),
        .ciphertext(aes_in_blk),
        .round_key(round_key_out),
        .round_key_no(decrypt_round_no),

        .plaintext(__aes_out_blk_decrypt),
        .en_o(en_o_decipher)
);

assign aes_out_blk =
	cipher_mode ? __aes_out_blk_encrypt :
	decipher_mode ? __aes_out_blk_decrypt : {`BLK_S{1'b0}};

assign en_o = en_o_cipher | en_o_decipher | en_o_round_key;

always @(posedge clk) begin
	if (reset) begin
		aes_op_in_progress <= 1'b0;
	end else begin
		if (en_cipher || en_decipher || en_key)
			aes_op_in_progress <= 1'b1;
		else if (en_o)
			aes_op_in_progress <= 1'b0;
	end
end

//`define AES_TOP_DEBUG
`ifdef AES_TOP_DEBUG
always @(posedge clk) begin
	if (en_cipher)
		$display("AES: Encrypting block %H", aes_in_blk);

	if (en_decipher)
		$display("AES: Decrypting block %H", aes_in_blk);

	if (en_key)
		$display("AES: Expanding key %H", aes_key);

	if (en_o_cipher)
		$display("AES: Encryption result: %H", aes_out_blk);

	if (en_o_decipher)
		$display("AES: Decryption result %H", aes_out_blk);

	if (en_o_round_key)
		$display("AES: Key expanded!");
end
`endif

endmodule
