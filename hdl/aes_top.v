`include "aes.vh"

module aes_top(
	input                   clk,
	input                   reset,
	input                   en,

	input                   aes128_mode,
	input                   aes256_mode,

	input                   cipher_mode,
	input                   decipher_mode,
	input                   key_exp_mode,

	input [`KEY_S-1:0]      aes_key,
	input [`BLK_S-1:0]      aes_in_blk,

	output [`BLK_S-1:0]     aes_out_blk,
	output reg              aes_op_in_progress,
	output                  en_o
);

wire [`ROUND_KEY_BITS-1:0]    round_key_in;
wire [`ROUND_KEY_BITS-1:0]    round_key_out;

wire [`Nb-1:0] round_key_addr;
wire [`Nb-1:0] encrypt_round_no;
wire [`Nb-1:0] decrypt_round_no;

wire en_cipher;
wire en_decipher;
wire en_key_exp;

wire en_o_round_key;
wire en_o_cipher;
wire en_o_decipher;

wire [`BLK_S-1:0] __aes_out_blk_encrypt;
wire [`BLK_S-1:0] __aes_out_blk_decrypt;

wire [`Nb-1:0] rounds_total;

// SRAM signals
wire            w_e;
wire [`Nb-1:0]  addr;

assign rounds_total = aes128_mode ? `Nr_128 : `Nr_256;

assign en_cipher = en && cipher_mode;
assign en_decipher = en && decipher_mode;
assign en_key_exp = en && key_exp_mode;

assign addr =
	key_exp_mode ? round_key_addr :
	cipher_mode ? encrypt_round_no :
	decipher_mode ? decrypt_round_no : {`Nb{1'b0}};

block_ram #(
        .ADDR_WIDTH(`Nb),
        .DATA_WIDTH(`ROUND_KEY_BITS),
        .DEPTH(`Nr_256 + 1)
) key_sram(
        .clk(clk),

        .addr(addr),
        .i_data(round_key_in),
        .w_e(w_e),

        .o_data(round_key_out)
);

round_key round_key_gen(
        .clk(clk),
        .reset(reset),
        .en(en_key_exp),

        .aes128_mode(aes128_mode),
        .aes256_mode(aes256_mode),

        .rounds_total(rounds_total),
        .key(aes_key),

        .round_key(round_key_in),
        .round_key_addr(round_key_addr),
        .w_e(w_e),

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
	if (en)
		aes_op_in_progress <= 1'b1;
	else if (en_o)
		aes_op_in_progress <= 1'b0;
end

//`define AES_TOP_DEBUG
`ifdef AES_TOP_DEBUG
always @(posedge clk) begin
	if (en) begin
		if (cipher_mode)
			$display("AES: Encrypting block %H", aes_in_blk);

		if (decipher_mode)
			$display("AES: Decrypting block %H", aes_in_blk);

		if (key_exp_mode)
			$display("AES: Expanding key %H", aes_key);
	end

	if (en_o) begin
		if (cipher_mode)
			$display("AES: Encryption result: %H", aes_out_blk);

		if (decipher_mode)
			$display("AES: Decryption result %H", aes_out_blk);

		if (key_exp_mode)
			$display("AES: Key expanded!");
	end

end
`endif

endmodule
