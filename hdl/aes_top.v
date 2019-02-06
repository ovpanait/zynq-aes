`include "aes.vh"

module aes_top(
        input                 clk,
        input                 reset,
        input                 en,

        // AES signals
        input [0:`KEY_S-1]      aes_key,
        input [0:`BLK_S-1]      aes_plaintext,
        output [0:`BLK_S-1]     aes_ciphertext,

        // Control/Status registers
        input [`CTRL_S-1:0]     ctrl,
        output [`STATUS_S-1:0]  status,

        output reg              en_o
);

wire [0:`KEY_S-1]       round_key_in;
wire [0:`KEY_S-1]       round_key_out;
wire [0:`Nk-1]          key_round_no;
wire [0:`Nk-1]          encrypt_round_no;

// SRAM signals
wire                          w_e;
wire                          r_e;
wire [0:3]                    addr;

// Enable signals
wire                          en_cipher;
wire                          en_round_key;

wire                          en_o_round_key;
wire                          en_o_cipher;


// SRAM holding round keys
assign addr = w_e ? key_round_no : encrypt_round_no;

key_sram sram(
        .clk(clk),

        .addr(addr),
        .i_data(round_key_in),
        .w_e(w_e),

        .o_data(round_key_out),
        .r_e(r_e)
);

// Key expansion module
round_key round_key_gen(
        .clk(clk),
        .reset(reset),
        .en(en_round_key),

        .key(aes_key),

        .round_key(round_key_in),
        .round_no(key_round_no),
        .w_e(w_e),

        .en_o(en_o_round_key)
);

// Encryption module
cipher encrypt_blk(
        .clk(clk),
        .reset(reset),
        .en(en_cipher),

        .plaintext(aes_plaintext),
        .key(round_key_out),
        .round_no(encrypt_round_no),
        .r_e(r_e),

        .ciphertext(aes_ciphertext),
        .en_o(en_o_cipher)
);

// Control register logic
assign en_cipher = (en == 1'b1) && (ctrl == `CTRL_ENCRYPT);
assign en_round_key = (en == 1'b1) && (ctrl == `CTRL_KEY);

// Status register logic
reg [`STATUS_S-1:0] status_reg;

always @(posedge clk) begin
        if (reset == 1'b1) begin
                status_reg <= {`STATUS_S{1'b0}};
                en_o <= 1'b0;
        end 
        else begin
                en_o <= 1'b0;

                if (en == 1'b1)
                        status_reg <= {`STATUS_S{1'b0}};

                if (en_o_round_key == 1'b1) begin
                        status_reg <= (status_reg | `S_KEY_MASK);
                        en_o <= 1'b1;
                end
                if (en_o_cipher == 1'b1) begin
                        status_reg <= (status_reg | `S_CIPHER_MASK);
                        en_o <= 1'b1;
                end
        end
end

assign status = status_reg;

endmodule
