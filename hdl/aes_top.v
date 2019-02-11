`include "aes.vh"

module aes_top(
        input                   clk,
        input                   reset,
        input                   en,

        input                   aes_key_strobe, // key expansion is needed
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

// Key expansion
assign en_i_round_key = aes_key_strobe ? en : 1'b0;

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

key_sram sram(
        .clk(clk),

        .addr(addr),
        .i_data(round_key_in),
        .w_e(w_e),

        .o_data(round_key_out),
        .r_e(r_e)
);

// Encryption block
assign en_i_ciphertext = aes_key_strobe ? en_o_round_key : en;

cipher encrypt_blk(
        .clk(clk),
        .reset(reset),
        .en(en_i_ciphertext),

        .plaintext(aes_plaintext),
        .key(round_key_out),
        .round_no(encrypt_round_no),
        .r_e(r_e),

        .ciphertext(aes_ciphertext),
        .en_o(en_o_cipher)
);

assign en_o = en_o_cipher;

endmodule
