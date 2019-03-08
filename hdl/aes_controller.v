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

        // aes specific signals
        input [0:`WORD_S-1]                       aes_cmd,

        // input FIFO signals
        input [0:IN_SRAM_DATA_WIDTH-1]            in_fifo_data,
        input [IN_SRAM_ADDR_WIDTH-1:0]            in_fifo_blk_cnt,
        output reg                                in_fifo_r_e,
        output [IN_SRAM_ADDR_WIDTH-1:0]           in_fifo_addr,

        // output FIFO
        output [OUT_FIFO_DEPTH * `WORD_S - 1 : 0] out_fifo,

        output reg                                en_o

);

localparam IN_SRAM_ADDR_WIDTH = 9;
localparam IN_SRAM_DATA_WIDTH = `Nb * `WORD_S;
localparam IN_SRAM_DEPTH = 512;

localparam [1:0] IDLE = 2'b0; // Initial/idle state
localparam [1:0] AES_START  = 2'b1;
localparam [1:0] AES_WAIT = 2'b11;

reg [1:0]               state;
reg [`WORD_S-1:0]       read_ptr;
reg [`WORD_S-1:0]       write_ptr;

wire [0:`BLK_S-1]       aes_ciphertext;
wire                    aes_done;

reg                     aes_start;
wire [0:`BLK_S-1]       aes_plaintext;
wire [0:`KEY_S-1]       aes_key;

genvar i;

// Data passed by the kernel has the bytes swapped due to the way it is represented in the 16 byte
// buffer.
function [0:`WORD_S-1] swap_bytes32(input [0:`WORD_S-1] data);
        integer i;
        begin
                for (i = 0; i < `WORD_S / `BYTE_S; i=i+1)
                        swap_bytes32[i*`BYTE_S +: `BYTE_S] = data[(`WORD_S / `BYTE_S - i - 1)*`BYTE_S +: `BYTE_S];
        end
endfunction

function [0:IN_SRAM_DATA_WIDTH-1] swap_bytes128(input [0:IN_SRAM_DATA_WIDTH-1] data);
        integer i;
        begin
                for (i = 0; i < IN_SRAM_DATA_WIDTH / `WORD_S; i=i+1)
                        swap_bytes128[i*`WORD_S +: `WORD_S] = swap_bytes32(data[i*`WORD_S +: `WORD_S]);
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
reg  [0:`WORD_S-1] out_fifo_arr [OUT_FIFO_DEPTH-1 : 0];

generate for (i = 0; i < IN_FIFO_DEPTH; i=i+1)
        assign out_fifo[i*`WORD_S +: `WORD_S] = out_fifo_arr[i];
endgenerate

assign in_fifo_addr = read_ptr;

assign aes_plaintext = (aes_cmd == `ENCRYPT) ? swap_bytes128(in_fifo_data) : 32'h0;
assign aes_key = (aes_cmd == `SET_KEY) ? swap_bytes128(in_fifo_data) : 32'h0;

always @(posedge clk) begin
        if (reset == 1'b1) begin
                state <= IDLE;
                write_ptr <= 1'b0;
                en_o <= 1'b0;
        end 
        else begin
                case (state)
                        IDLE:
                        begin
                                en_o <= 1'b0;
                                state <= IDLE;

                                aes_start <= 1'b0;
                                read_ptr <= 1'b0;
                                write_ptr <= 1'b0;

                                in_fifo_r_e <= 1'b0;

                                if (en == 1'b1) begin
                                        state <= AES_START;
                                        in_fifo_r_e <= 1'b1;
                                end
                        end
                        AES_START:
                        begin
                                en_o <= 1'b0;
                                state <= AES_WAIT;

                                aes_start <= 1'b1;
                                in_fifo_r_e <= 1'b0;

                                if (read_ptr == in_fifo_blk_cnt) begin
                                        aes_start <= 1'b0;
                                        state <= IDLE;
                                        en_o <= 1'b1;
                                        read_ptr <= 1'b0;
                                end
                        end
                        AES_WAIT:
                        begin
                                en_o <= 1'b0;
                                state <= AES_WAIT;

                                aes_start <= 1'b0;
                                in_fifo_r_e <= 1'b0;

                                if (aes_done == 1'b1) begin
                                        // output FIFO
                                        write_ptr <= write_ptr + `Nb;
                                        out_fifo_arr[write_ptr + 0] <= swap_bytes32(aes_ciphertext[0*`WORD_S +: `WORD_S]);
                                        out_fifo_arr[write_ptr + 1] <= swap_bytes32(aes_ciphertext[1*`WORD_S +: `WORD_S]);
                                        out_fifo_arr[write_ptr + 2] <= swap_bytes32(aes_ciphertext[2*`WORD_S +: `WORD_S]);
                                        out_fifo_arr[write_ptr + 3] <= swap_bytes32(aes_ciphertext[3*`WORD_S +: `WORD_S]);

                                        // input FIFO
                                        read_ptr <= read_ptr + 1'b1;
                                        in_fifo_r_e <= 1'b1;

                                        state <= AES_START;
                                end
                        end
                        default:
                                state <= IDLE;
                endcase
        end
end
endmodule
