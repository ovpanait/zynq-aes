`include "aes.vh"

module aes_top(
        input                   clk,
        input                   reset,
        input                   en,

        input [0:`WORD_S-1]     aes_cmd,
        input [0:`KEY_S-1]      aes_key,
        input [0:`BLK_S-1]      aes_plaintext,

        output [0:`BLK_S-1]     aes_ciphertext,
        output                  en_o
);

wire [0:`KEY_S-1]       round_key_in;
wire [0:`KEY_S-1]       round_key_out;
wire [0:`Nk-1]          key_round_no;
wire [0:`Nk-1]          encrypt_round_no;

// SRAM signals
wire            w_e;
wire            r_e;
wire [0:3]      addr;

wire            en_i_round_key;
wire            en_o_round_key;
wire            en_i_cipher;
wire            en_o_cipher;

wire [0:`BLK_S-1] __aes_ciphertext;

// Key expansion
assign en_i_round_key = (en && aes_cmd == `SET_KEY);

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
assign addr = w_e ? key_round_no : encrypt_round_no;

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

// Encryption block
assign en_i_cipher = (en && aes_cmd == `ENCRYPT);

cipher encrypt_blk(
        .clk(clk),
        .reset(reset),
        .en(en_i_cipher),

        .plaintext(aes_plaintext),
        .key(round_key_out),
        .round_no(encrypt_round_no),
        .r_e(r_e),

        .ciphertext(__aes_ciphertext),
        .en_o(en_o_cipher)
);

assign aes_ciphertext = (en_o_round_key == 1'b1) ? {`BLK_S{1'b0}} : __aes_ciphertext;
assign en_o = en_o_cipher | en_o_round_key;

endmodule
