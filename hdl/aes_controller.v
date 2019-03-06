`include "aes.vh"

module aes_controller #
(
        /* Defaults: 8192 bytes */
        IN_FIFO_DEPTH = 2048,
        OUT_FIFO_DEPTH = 2048
)
(
        input clk,
        input reset,
        input en,

        input [0:`WORD_S-1]                       aes_cmd,
        input [IN_FIFO_DEPTH * `WORD_S - 1 :0]    in_fifo,
        input [`WORD_S-1:0]                       in_fifo_last,

        output [OUT_FIFO_DEPTH * `WORD_S - 1 : 0] out_fifo,
        output reg                                en_o

);

localparam IN_FIFO_BITLEN = IN_FIFO_DEPTH * `WORD_S;
localparam OUT_FIFO_BITLEN = OUT_FIFO_DEPTH * `WORD_S;

localparam [1:0] IDLE = 2'b0; // Initial/idle state
localparam [1:0] AES_START  = 2'b1;
localparam [1:0] AES_WAIT = 2'b11;

localparam ENCRYPT_CMD = 32'h20;
localparam SET_KEY_CMD = 32'h10;

reg [1:0]               state;
reg [`WORD_S-1:0]       rw_ptr;

wire [0:`BLK_S-1]       aes_ciphertext;
wire                    aes_done;

reg                     aes_start;
wire [0:`BLK_S-1]       aes_plaintext;
wire [0:`KEY_S-1]       aes_key;

genvar i;

// Data passed by the kernel has the bytes swapped due to the way it is represented in the 16 byte
// buffer.
function [0:`WORD_S-1] swap_bytes(input [0:`WORD_S-1] data);
        integer i;
        begin
                for (i = 0; i < `WORD_S / `BYTE_S; i=i+1)
                        swap_bytes[i*`BYTE_S +: `BYTE_S] = data[(`WORD_S / `BYTE_S - i - 1)*`BYTE_S +: `BYTE_S];
        end
endfunction

aes_top aes_mod(
        .clk(clk),
        .reset(reset),
        .en(aes_start),

        .aes_cmd(aes_cmd),
        .aes_key(aes_key),
        .aes_plaintext(aes_plaintext),

        .aes_ciphertext(aes_ciphertext),
        .en_o(aes_done)
);

// Unpack FIFOs
wire [0:`WORD_S-1] in_fifo_arr[IN_FIFO_DEPTH-1 : 0];
reg  [0:`WORD_S-1] out_fifo_arr [OUT_FIFO_DEPTH-1 : 0];

generate for (i = 0; i < IN_FIFO_DEPTH; i=i+1)
        assign in_fifo_arr[i] = in_fifo[i*`WORD_S +: `WORD_S];
endgenerate

generate for (i = 0; i < IN_FIFO_DEPTH; i=i+1)
        assign out_fifo[i*`WORD_S +: `WORD_S] = out_fifo_arr[i];
endgenerate

// aes plaintext
generate for (i = 0; i < `Nb; i=i+1) begin
        assign aes_plaintext[i*`WORD_S +: `WORD_S] = 
        (aes_cmd == `ENCRYPT) ? swap_bytes(in_fifo_arr[rw_ptr + i]) : 32'h0;
end
endgenerate

// aes key
generate for (i = 0; i < `Nk; i=i+1) begin
        assign aes_key[i*`WORD_S +: `WORD_S] = 
        (aes_cmd == `SET_KEY) ? swap_bytes(in_fifo_arr[rw_ptr + i]) : 32'h0;
end
endgenerate

always @(posedge clk) begin
        if (reset == 1'b1) begin
                state <= IDLE;
                rw_ptr <= 1'b0;
                en_o <= 1'b0;
        end 
        else begin
                case (state)
                        IDLE:
                        begin
                                en_o <= 1'b0;
                                state <= IDLE;

                                aes_start <= 1'b0;
                                rw_ptr <= 1'b0;

                                if (en == 1'b1)
                                        state <= AES_START;                                
                        end
                        AES_START:
                        begin
                                en_o <= 1'b0;
                                state <= AES_WAIT;

                                aes_start <= 1'b1;

                                if (rw_ptr == in_fifo_last) begin
                                        aes_start <= 1'b0;
                                        state <= IDLE;
                                        en_o <= 1'b1;
                                end
                        end
                        AES_WAIT:
                        begin
                                en_o <= 1'b0;
                                state <= AES_WAIT;

                                aes_start <= 1'b0;

                                if (aes_done == 1'b1) begin
                                        out_fifo_arr[rw_ptr + 0] <= swap_bytes(aes_ciphertext[0*`WORD_S +: `WORD_S]);
                                        out_fifo_arr[rw_ptr + 1] <= swap_bytes(aes_ciphertext[1*`WORD_S +: `WORD_S]);
                                        out_fifo_arr[rw_ptr + 2] <= swap_bytes(aes_ciphertext[2*`WORD_S +: `WORD_S]);
                                        out_fifo_arr[rw_ptr + 3] <= swap_bytes(aes_ciphertext[3*`WORD_S +: `WORD_S]);

                                        rw_ptr <= rw_ptr + `Nb;

                                        state <= AES_START;
                                end
                        end
                        default:
                                state <= IDLE;
                endcase
        end
end
endmodule
