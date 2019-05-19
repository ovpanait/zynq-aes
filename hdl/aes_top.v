`include "aes.vh"

module aes_top(
        input                   clk,
        input                   reset,
        input                   en,

        input [0:`WORD_S-1]     aes_cmd,
        input [0:`KEY_S-1]      aes_key,
        input [0:`BLK_S-1]      aes_in_blk,

        output [0:`BLK_S-1]     aes_out_blk,
        output                  en_o
);

wire [0:`KEY_S-1]       round_key_in;
wire [0:`KEY_S-1]       round_key_out;

wire [0:`Nk-1]       key_round_no;
wire [0:`Nk-1]       encrypt_round_no;
wire [0:`Nk-1]       decrypt_round_no;

wire            r_e_encrypt;
wire            r_e_decrypt;

wire            en_i_round_key;
wire            en_o_round_key;

wire            en_i_cipher;
wire            en_o_cipher;

wire            en_i_decipher;
wire            en_o_decipher;

wire [0:`BLK_S-1] __aes_out_blk_encrypt;
wire [0:`BLK_S-1] __aes_out_blk_decrypt;

// SRAM signals
wire            w_e;
wire [0:3]      addr;
wire            r_e;

// Key expansion
assign en_i_round_key = (en && aes_cmd == `SET_KEY_128);

round_key round_key_gen(
        .clk(clk),
        .reset(reset),
        .en(en_i_round_key),

        .key(aes_key),

        .round_key(round_key_in),
        .round_no(key_round_no),
        .w_e(w_e),

        .en_o(en_o_round_key)
);

// round keys SRAM block
assign addr = w_e ? key_round_no : (r_e_encrypt ? encrypt_round_no : decrypt_round_no);
assign r_e = r_e_encrypt | r_e_decrypt;

block_ram #(
        .ADDR_WIDTH(4),
        .DATA_WIDTH(128)
) key_sram(
        .clk(clk),

        .addr(addr),
        .i_data(round_key_in),
        .w_e(w_e),

        .o_data(round_key_out),
        .r_e(r_e)
);

// Encryption / Decryption blocks

assign en_i_cipher = (en && (aes_cmd == `ECB_ENCRYPT_128 || aes_cmd == `CBC_ENCRYPT_128));
assign en_i_decipher = (en && (aes_cmd == `ECB_DECRYPT_128 || aes_cmd == `CBC_DECRYPT_128));

cipher encrypt_blk(
        .clk(clk),
        .reset(reset),
        .en(en_i_cipher),

        .plaintext(aes_in_blk),
        .key(round_key_out),
        .round_no(encrypt_round_no),
        .r_e(r_e_encrypt),

        .ciphertext(__aes_out_blk_encrypt),
        .en_o(en_o_cipher)
);

decipher decrypt_blk(
        .clk(clk),
        .reset(reset),
        .en(en_i_decipher),

        .ciphertext(aes_in_blk),
        .round_key(round_key_out),
        .round_no(decrypt_round_no),
        .r_e(r_e_decrypt),

        .plaintext(__aes_out_blk_decrypt),
        .en_o(en_o_decipher)
);

assign aes_out_blk = en_o_cipher ? __aes_out_blk_encrypt :
                (en_o_decipher ? __aes_out_blk_decrypt : {`BLK_S{1'b0}});
assign en_o = en_o_cipher | en_o_decipher | en_o_round_key;

endmodule
