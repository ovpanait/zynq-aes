`include "aes.vh"

module aes_controller #
(
        IN_FIFO_ADDR_WIDTH = 9,
        IN_FIFO_DATA_WIDTH = 128,
        OUT_FIFO_ADDR_WIDTH = 9,
        OUT_FIFO_DATA_WIDTH = 128
)
(
        input clk,
        input reset,
        input en,

        // aes specific signals
        input [0:`WORD_S-1]                       aes_cmd,

        // input FIFO signals
        input [0:IN_FIFO_DATA_WIDTH-1]            in_fifo_data,
        input [IN_FIFO_ADDR_WIDTH-1:0]            in_fifo_blk_cnt,
        output reg                                in_fifo_r_e,
        output [IN_FIFO_ADDR_WIDTH-1:0]           in_fifo_addr,

        // output FIFO
        output reg [0:OUT_FIFO_DATA_WIDTH-1]       out_fifo_data,
        output reg                                 out_fifo_w_e,
        output reg [OUT_FIFO_ADDR_WIDTH-1:0]       out_fifo_addr,

        output reg                                en_o

);

localparam [1:0] IDLE = 2'b0; // Initial/idle state
localparam [1:0] AES_START  = 2'b1;
localparam [1:0] AES_WAIT = 2'b11;

reg [1:0]               state;
reg [`WORD_S-1:0]       read_ptr;
reg [`WORD_S-1:0]       write_ptr;

wire [0:`BLK_S-1]       aes_out_blk;
wire                    aes_done;

reg                     aes_start;
wire [0:`BLK_S-1]       aes_in_blk;
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

function [0:IN_FIFO_DATA_WIDTH-1] swap_bytes128(input [0:IN_FIFO_DATA_WIDTH-1] data);
        integer i;
        begin
                for (i = 0; i < IN_FIFO_DATA_WIDTH / `WORD_S; i=i+1)
                        swap_bytes128[i*`WORD_S +: `WORD_S] = swap_bytes32(data[i*`WORD_S +: `WORD_S]);
        end
endfunction

aes_top aes_mod(
        .clk(clk),
        .reset(reset),
        .en(aes_start),

        .aes_cmd(aes_cmd),
        .aes_key(aes_key),
        .aes_in_blk(aes_in_blk),

        .aes_out_blk(aes_out_blk),
        .en_o(aes_done)
);

assign in_fifo_addr = read_ptr;

assign aes_in_blk = (aes_cmd == `ENCRYPT || aes_cmd == `DECRYPT) ? swap_bytes128(in_fifo_data) : 32'h0;
assign aes_key = (aes_cmd == `SET_KEY) ? swap_bytes128(in_fifo_data) : 32'h0;

always @(posedge clk) begin
        if (reset == 1'b1) begin
                state <= IDLE;
                write_ptr <= 1'b0;
                en_o <= 1'b0;
        end 
        else begin
                en_o <= 1'b0;
                in_fifo_r_e <= 1'b0;
                out_fifo_w_e <= 1'b0;

                case (state)
                        IDLE:
                        begin
                                state <= IDLE;

                                aes_start <= 1'b0;
                                read_ptr <= 1'b0;
                                write_ptr <= 1'b0;

                                if (en == 1'b1) begin
                                        state <= AES_START;
                                        in_fifo_r_e <= 1'b1;
                                end
                        end
                        AES_START:
                        begin
                                state <= AES_WAIT;
                                aes_start <= 1'b1;

                                if (read_ptr == in_fifo_blk_cnt) begin
                                        aes_start <= 1'b0;
                                        state <= IDLE;
                                        en_o <= 1'b1;
                                        read_ptr <= 1'b0;
                                end
                        end
                        AES_WAIT:
                        begin
                                state <= AES_WAIT;

                                aes_start <= 1'b0;

                                if (aes_done == 1'b1) begin
                                        // output FIFO
                                        out_fifo_w_e <= 1'b1;
                                        out_fifo_addr <= write_ptr;
                                        out_fifo_data <= swap_bytes128(aes_out_blk);
                                        write_ptr <= write_ptr + 1'b1;

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
