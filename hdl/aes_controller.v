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
	input [`WORD_S-1:0]                  aes_cmd,

	// input FIFO
	input                                in_fifo_almost_full,
	input [IN_FIFO_DATA_WIDTH-1:0]       in_fifo_data,
	input                                in_fifo_empty,
	input                                in_fifo_full,
	input                                in_fifo_read_tvalid,
	output reg                           in_fifo_read_tready,

	// output FIFO
	input                                out_fifo_almost_full,
	input                                out_fifo_empty,
	input                                out_fifo_full,
	input                                out_fifo_write_tready,
	output reg                           out_fifo_write_tvalid,
	output reg [OUT_FIFO_DATA_WIDTH-1:0] out_fifo_data,

	output reg                           processing_done

);

`include "controller_fc.vh"

localparam [2:0] AES_GET_KEY  = 3'b010;
localparam [2:0] AES_GET_IV = 3'b011;
localparam [2:0] AES_START = 3'b101;
localparam [2:0] AES_WAIT = 3'b110;
localparam [2:0] AES_STORE_BLOCK = 3'b111;

reg [2:0]         state;

wire [`BLK_S-1:0] aes_out_blk;
wire              aes_done;

reg [`WORD_S-1:0] __aes_cmd;
reg [`KEY_S-1:0]  aes_key;
reg [`BLK_S-1:0]  aes_iv;

reg               aes_start;
wire              aes_cipher_mode;
wire              aes_decipher_mode;
wire              aes_key_exp_mode;

wire [`BLK_S-1:0] aes_ecb_in_blk;
wire [`BLK_S-1:0] aes_cbc_in_blk;
wire [`BLK_S-1:0] aes_in_blk;

wire out_fifo_write_req;
wire in_fifo_read_req;

reg [`BLK_S-1:0] aes_in_blk_reg;

genvar i;

assign aes_cipher_mode = is_cipher_op(__aes_cmd);
assign aes_start_cipher = aes_start && aes_cipher_mode;

assign aes_decipher_mode = is_decipher_op(__aes_cmd);
assign aes_start_decipher = aes_start && aes_decipher_mode;

assign aes_key_exp_mode = is_key_exp_op(__aes_cmd);
assign aes_start_key_exp = aes_start && aes_key_exp_mode;

aes_top aes_mod(
	.clk(clk),
	.reset(reset),

	.en(aes_start),
	.cipher_mode(aes_cipher_mode),
	.decipher_mode(aes_decipher_mode),
	.key_exp_mode(aes_key_exp_mode),

	.aes_op_in_progress(aes_op_in_progress),

	.aes_key(aes_key),
	.aes_in_blk(aes_in_blk_reg),

	.aes_out_blk(aes_out_blk),
	.en_o(aes_done)
);

assign aes_in_blk = is_CBC_enc(aes_cmd) ?  aes_cbc_in_blk : aes_ecb_in_blk;
assign aes_ecb_in_blk = in_fifo_data;
assign aes_cbc_in_blk = aes_iv ^ aes_ecb_in_blk;

assign out_fifo_write_req = out_fifo_write_tready && out_fifo_write_tvalid;
assign in_fifo_read_req = in_fifo_read_tready && in_fifo_read_tvalid;

always @(posedge clk) begin
	if (reset == 1'b1) begin
		processing_done <= 1'b0;
		__aes_cmd <= 1'b0;
		aes_key <= 1'b0;
		aes_iv <= 1'b0;
		state <= AES_GET_KEY;

		aes_in_blk_reg <= 1'b0;
		in_fifo_read_tready <= 1'b0;
	end
	else begin
		in_fifo_read_tready <= 1'b0;
		aes_start <= 1'b0;

		case (state)
			AES_GET_KEY:
			begin
				in_fifo_read_tready <= 1'b1;

				if (in_fifo_read_req) begin
					processing_done <= 1'b0;
					in_fifo_read_tready <= 1'b0;

					aes_key <= in_fifo_data;
					__aes_cmd <= `SET_KEY_128;
					state <= AES_START;
					aes_start <= 1'b1;

					// Get the IV if performing CBC operations.
					if (is_CBC_op(aes_cmd)) begin
						state <= AES_GET_IV;
					end
				end
			end
			AES_GET_IV:
			begin
				in_fifo_read_tready <= 1'b1;

				if (in_fifo_read_req) begin
					in_fifo_read_tready <= 1'b0;
					aes_iv <= in_fifo_data;
					state <= AES_START;
				end
			end
			AES_START:
			begin
				state <= AES_START;

				if (!aes_op_in_progress)
					in_fifo_read_tready <= 1'b1;

				if (in_fifo_read_req) begin
					__aes_cmd <= aes_cmd;
					in_fifo_read_tready <= 1'b0;
					aes_in_blk_reg <= aes_in_blk;
					state <= AES_WAIT;
					aes_start <= 1'b1;
				end

				if (axis_slave_done && in_fifo_empty) begin
					processing_done <= 1'b1;
					state <= AES_GET_KEY;
				end
			end
			AES_WAIT:
			begin
				state <= AES_WAIT;

				if (aes_done == 1'b1) begin
					out_fifo_data <= aes_out_blk;
					state <= AES_STORE_BLOCK;

					if(is_CBC_enc(aes_cmd)) begin
						aes_iv <= aes_out_blk;
					end

					if(is_CBC_dec(aes_cmd)) begin
						out_fifo_data <= aes_iv ^ aes_out_blk;
						aes_iv <= aes_in_blk_reg;
					end

				end
			end
			AES_STORE_BLOCK:
			begin
				state <= AES_STORE_BLOCK;

				if (out_fifo_write_req) begin
					state <= AES_START;
				end
			end
			default:
				state <= AES_GET_KEY;
		endcase
	end
end

always @(posedge clk) begin
	if (reset)
		out_fifo_write_tvalid <= 1'b0;
	else begin
		if (aes_done && (aes_cipher_mode || aes_decipher_mode))
			out_fifo_write_tvalid <= 1'b1;

		if (out_fifo_write_req)
			out_fifo_write_tvalid <= 1'b0;
	end
end
endmodule
