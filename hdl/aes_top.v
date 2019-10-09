`include "aes.vh"

module aes_top(
        input                   clk,
        input                   reset,
	input                   en,

	input                   cipher_mode,
	input                   decipher_mode,
	input                   key_exp_mode,

        input [0:`KEY_S-1]      aes_key,
        input [0:`BLK_S-1]      aes_in_blk,

        output [0:`BLK_S-1]     aes_out_blk,
	output reg              aes_op_in_progress,
        output                  en_o
);

wire [0:`KEY_S-1]       round_key_in;
wire [0:`KEY_S-1]       round_key_out;

wire [0:`Nk-1]       key_round_no;
wire [0:`Nk-1]       encrypt_round_no;
wire [0:`Nk-1]       decrypt_round_no;

wire en_cipher;
wire en_decipher;
wire en_key_exp;

wire en_o_round_key;
wire en_o_cipher;
wire en_o_decipher;

wire [0:`BLK_S-1] __aes_out_blk_encrypt;
wire [0:`BLK_S-1] __aes_out_blk_decrypt;

// SRAM signals
wire            w_e;
wire [0:3]      addr;

assign en_cipher = en && cipher_mode;
assign en_decipher = en && decipher_mode;
assign en_key_exp = en && key_exp_mode;

assign addr =
	key_exp_mode ? key_round_no :
	cipher_mode ? encrypt_round_no :
	decipher_mode ? decrypt_round_no : {4{1'b0}};

block_ram #(
        .ADDR_WIDTH(4),
        .DATA_WIDTH(128)
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

        .key(aes_key),

        .round_key(round_key_in),
        .round_no(key_round_no),
        .w_e(w_e),

        .en_o(en_o_round_key)
);

cipher encrypt_blk(
        .clk(clk),
        .reset(reset),
        .en(en_cipher),

        .plaintext(aes_in_blk),
        .key(round_key_out),
        .round_no(encrypt_round_no),

        .ciphertext(__aes_out_blk_encrypt),
        .en_o(en_o_cipher)
);

decipher decrypt_blk(
        .clk(clk),
        .reset(reset),
        .en(en_decipher),

        .ciphertext(aes_in_blk),
        .round_key(round_key_out),
        .round_no(decrypt_round_no),

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

endmodule
