`include "aes.vh"

module aes_controller #
(
	IN_FIFO_ADDR_WIDTH = 9,
	IN_FIFO_DATA_WIDTH = 128,
	OUT_FIFO_ADDR_WIDTH = 9,
	OUT_FIFO_DATA_WIDTH = 128
)
(
	input                                clk,
	input                                reset,

	input                                axis_slave_done,

	// aes specific
	input [0:`WORD_S-1]                  aes_cmd,

	// input FIFO
	input                                in_fifo_almost_full,
	input [0:IN_FIFO_DATA_WIDTH-1]       in_fifo_data,
	input                                in_fifo_empty,
	input                                in_fifo_full,
	input                                in_fifo_ready,
	output reg                           in_fifo_r_e,

	// output FIFO
	input                                out_fifo_almost_full,
	input                                out_fifo_empty,
	input                                out_fifo_full,
	input                                out_fifo_ready,
	output reg [0:OUT_FIFO_DATA_WIDTH-1] out_fifo_data,
	output reg                           out_fifo_w_e,

	output reg                           processing_done

);

localparam [2:0] IDLE = 3'b000;
localparam [2:0] INIT_BLOCK_RAM  = 3'b001;
localparam [2:0] AES_GET_KEY  = 3'b010;
localparam [2:0] AES_GET_IV = 3'b011;
localparam [2:0] AES_EXPAND_KEY = 3'b100;
localparam [2:0] AES_START = 3'b101;
localparam [2:0] AES_WAIT = 3'b110;
localparam [2:0] AES_STORE_BLOCK = 3'b111;

reg [2:0]         state;

wire [0:`BLK_S-1] aes_out_blk;
wire              aes_done;

reg [0:`BLK_S-1]  prev_aes_ecb_in_blk;
reg [0:`WORD_S-1] __aes_cmd;
reg [0: `BLK_S-1] aes_iv;
reg [0:`KEY_S-1]  aes_key;
reg               aes_start;
reg               aes_start_delayed;

wire [0:`BLK_S-1] aes_ecb_in_blk;
wire [0:`BLK_S-1] aes_cbc_in_blk;
wire [0:`BLK_S-1] aes_in_blk;

wire out_fifo_can_req;
wire in_fifo_can_req;

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
	.en(aes_start_delayed),

	.aes_cmd(__aes_cmd),
	.aes_key(aes_key),
	.aes_in_blk(aes_in_blk),

	.aes_out_blk(aes_out_blk),
	.en_o(aes_done)
);

assign aes_in_blk = is_CBC_enc(__aes_cmd) ?  aes_cbc_in_blk : aes_ecb_in_blk;
assign aes_ecb_in_blk = swap_bytes128(in_fifo_data);
assign aes_cbc_in_blk = aes_iv ^ aes_ecb_in_blk;

assign out_fifo_can_req = !out_fifo_w_e && !out_fifo_full && out_fifo_ready;
assign in_fifo_can_req = !in_fifo_r_e && !in_fifo_empty && in_fifo_ready;

always @(posedge clk) begin
	if (reset == 1'b1) begin
		prev_aes_ecb_in_blk <= 1'b0;
		processing_done <= 1'b0;
		__aes_cmd <= 1'b0;
		aes_key <= 1'b0;
		aes_iv <= 1'b0;
		state <= IDLE;
	end
	else begin
		out_fifo_w_e <= 1'b0;
		in_fifo_r_e <= 1'b0;
		aes_start <= 1'b0;

		case (state)
			IDLE:
			begin
				__aes_cmd <= 1'b0;
				state <= IDLE;

				if (in_fifo_can_req) begin
					processing_done <= 1'b0;
					state <= INIT_BLOCK_RAM;
					__aes_cmd <= aes_cmd;
					in_fifo_r_e <= 1'b1;
				end
			end
			INIT_BLOCK_RAM:
			begin
				state <= INIT_BLOCK_RAM;

				if (is_CBC_op(__aes_cmd)) begin
					if (in_fifo_can_req) begin
						state <= AES_GET_KEY;
						in_fifo_r_e <= 1'b1;
					end
				end else begin
					state <= AES_GET_KEY;
				end
			end
			AES_GET_KEY:
			begin
				aes_key <= swap_bytes128(in_fifo_data);
				__aes_cmd <= `SET_KEY_128;
				state <= AES_EXPAND_KEY;
				aes_start <= 1'b1;

				// Get the IV if performing CBC operations.
				if (is_CBC_op(__aes_cmd)) begin
					state <= AES_GET_IV;
					aes_start <= 1'b0;
				end
			end
			AES_GET_IV:
			begin
				aes_iv <= swap_bytes128(in_fifo_data);
				state <= AES_EXPAND_KEY;
				aes_start <= 1'b1;
			end
			AES_EXPAND_KEY:
			begin
				state <= AES_EXPAND_KEY;

				if (aes_done == 1'b1) begin
					__aes_cmd <= aes_cmd;
					state <= AES_START;
				end
			end
			AES_START:
			begin
				state <= AES_START;

				if (in_fifo_can_req) begin
					in_fifo_r_e <= 1'b1;
					state <= AES_WAIT;
					aes_start <= 1'b1;
				end

				if (axis_slave_done && in_fifo_empty) begin
					processing_done <= 1'b1;
					state <= IDLE;
				end
			end
			AES_WAIT:
			begin
				state <= AES_WAIT;

				if (aes_done == 1'b1) begin
					out_fifo_data <= swap_bytes128(aes_out_blk);
					state <= AES_STORE_BLOCK;

					if(is_CBC_enc(__aes_cmd)) begin
						aes_iv <= aes_out_blk;
					end

					if(is_CBC_dec(__aes_cmd)) begin
						out_fifo_data <= swap_bytes128(aes_iv ^ aes_out_blk);
						aes_iv <= swap_bytes128(in_fifo_data);
					end
				end
			end
			AES_STORE_BLOCK:
			begin
				state <= AES_STORE_BLOCK;

				if (out_fifo_can_req) begin
					out_fifo_w_e <= 1'b1;
					state <= AES_START;
				end
			end
			default:
				state <= IDLE;
		endcase
	end
end

// Delay aes_start by one clock to wait for data to be retrieved from FIFO
always @(posedge clk) begin
	if (reset == 1'b1) begin
		aes_start_delayed <= 1'b0;
	end else begin
		aes_start_delayed <= aes_start;
	end
end

endmodule
