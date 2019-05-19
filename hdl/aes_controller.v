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
        output reg [IN_FIFO_ADDR_WIDTH-1:0]        out_fifo_blk_no,
        output reg                                 out_fifo_w_e,
        output reg [OUT_FIFO_ADDR_WIDTH-1:0]       out_fifo_addr,

        output reg                                en_o

);

localparam [2:0] IDLE = 3'b000; // Initial/idle state
localparam [2:0] INIT_BLOCK_RAM  = 3'b001;
localparam [2:0] AES_GET_IV = 3'b010;
localparam [2:0] AES_START = 3'b011;
localparam [2:0] AES_PROCESS = 3'b100;

reg [2:0]               state;
reg [`WORD_S-1:0]       read_ptr;
reg [`WORD_S-1:0]       write_ptr;

wire [0:`BLK_S-1]       aes_out_blk;
wire                    aes_done;

reg                     aes_start;
reg [0: `BLK_S-1]	aes_iv;
wire [0:`BLK_S-1]       aes_ecb_in_blk;
wire [0:`BLK_S-1]       aes_cbc_in_blk;
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

function is_CBC_op(input [0:`WORD_S-1] cmd);
        begin
		is_CBC_op = (cmd == `CBC_ENCRYPT_128 || cmd == `CBC_DECRYPT_128);
        end
endfunction

function is_CBC_enc(input [0:`WORD_S-1] cmd);
        begin
		is_CBC_enc = (cmd == `CBC_ENCRYPT_128);
        end
endfunction

function is_CBC_dec(input [0:`WORD_S-1] cmd);
        begin
		is_CBC_dec = (cmd == `CBC_DECRYPT_128);
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

assign aes_ecb_in_blk = swap_bytes128(in_fifo_data);
assign aes_cbc_in_blk = aes_iv ^ aes_ecb_in_blk;
assign aes_in_blk = is_CBC_enc(aes_cmd) ?  aes_cbc_in_blk : aes_ecb_in_blk;
assign aes_key = swap_bytes128(in_fifo_data);

always @(posedge clk) begin
        if (reset == 1'b1) begin
                state <= IDLE;
                write_ptr <= 1'b0;
                en_o <= 1'b0;
                aes_iv <= 1'b0;
                out_fifo_blk_no <= 1'b0;
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
                                        state <= INIT_BLOCK_RAM;
                                        in_fifo_r_e <= 1'b1;
                                end
                        end
                        INIT_BLOCK_RAM:
                        begin
                        	// Clear this here in order to preserve its value
                        	// while transferring the blocks through the axi 
                        	// stream master interface
                        	out_fifo_blk_no <= 1'b0;

                                state <= AES_START;

				// First get the IV if performing CBC operations
                                if (is_CBC_op(aes_cmd)) begin
                                	state <= AES_GET_IV;
				end
                        end
                        AES_GET_IV:
                        begin
                        	aes_iv <= swap_bytes128(in_fifo_data);

                        	in_fifo_r_e <= 1'b1;
				read_ptr <= read_ptr + 1'b1;

                        	state <= AES_START;
                        end
                        AES_START:
                        begin
                                state <= AES_PROCESS;
                                aes_start <= 1'b1;

                                if (read_ptr == in_fifo_blk_cnt) begin
                                        aes_start <= 1'b0;
                                        state <= IDLE;
                                        en_o <= 1'b1;
                                        read_ptr <= 1'b0;
				end
			end
                        AES_PROCESS:
                        begin
                                state <= AES_PROCESS;

                                aes_start <= 1'b0;

                                if (aes_done == 1'b1) begin
                                        // output FIFO
                                        out_fifo_w_e <= 1'b1;
                                        out_fifo_addr <= write_ptr;
                                        out_fifo_data <= swap_bytes128(aes_out_blk);
					out_fifo_blk_no <= out_fifo_blk_no + 1'b1;

                                        if(is_CBC_enc(aes_cmd)) begin
                                        	aes_iv <= aes_out_blk;
                                        end

                                        if(is_CBC_dec(aes_cmd)) begin
                                        	out_fifo_data <= swap_bytes128(aes_iv ^ aes_out_blk);
                                        	aes_iv <= aes_ecb_in_blk;
                                        end

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
