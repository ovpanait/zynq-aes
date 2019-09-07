// AXI master implementation
/*
 * The AXI master control logic is:
 * - Read 1 x 128-bit AES block from out_fifo
 * - Split it in 4 x 32-bit words and push them on the AXI bus
 *
 *
 * The FIFO is implemented as 128-bit Block RAM:
 * - AES controller writes AES blocks to it
 * - AXI master controller reads from it
 */

`include "aes.vh"

module aes_axi_stream_master #
(
	// Width of master side bus
	parameter integer C_M_AXIS_TDATA_WIDTH = 32,

	parameter integer FIFO_SIZE = 16,
	parameter integer FIFO_ADDR_WIDTH = 4,
	parameter integer FIFO_DATA_WIDTH = 128
)
(
	/*
	* Master side ports
	*/
	input                                     m00_axis_aclk,
	input                                     m00_axis_aresetn,
	output                                    m00_axis_tvalid,
	output  [C_M_AXIS_TDATA_WIDTH-1 : 0]      m00_axis_tdata,
	output  [(C_M_AXIS_TDATA_WIDTH/8)-1 : 0]  m00_axis_tstrb,
	output                                    m00_axis_tlast,
	input                                     m00_axis_tready,

	input                                     processing_done,

	input                                     aes_controller_out_fifo_w_e,
	input  [FIFO_DATA_WIDTH-1:0]              aes_controller_out_fifo_data,

	output                                    out_fifo_almost_full,
	output                                    out_fifo_empty,
	output                                    out_fifo_full,
	output                                    out_fifo_ready,

	output reg                                axis_master_done
);

// FIFO signals

wire fifo_almost_full;
wire fifo_write_e;
wire fifo_read_e;
wire fifo_empty;
wire fifo_ready;
wire fifo_full;

wire [FIFO_DATA_WIDTH-1:0] fifo_wdata;
wire [FIFO_DATA_WIDTH-1:0] fifo_rdata;

wire out_fifo_can_read;
reg out_fifo_r_e;

// AXI signals

wire [FIFO_DATA_WIDTH-1:0] axis_blk_shift;
reg [FIFO_ADDR_WIDTH-1:0]  axis_word_cnt;
wire [FIFO_DATA_WIDTH-1:0] axis_blk;
wire axis_transaction;
wire axis_last_blk;
wire axis_last_word;
reg  axis_tvalid;
wire axis_tlast;

// FIFO logic

fifo #(
	.ADDR_WIDTH(FIFO_ADDR_WIDTH),
	.DATA_WIDTH(FIFO_DATA_WIDTH),
	.DEPTH(FIFO_SIZE)
) master_fifo (
	.clk(m00_axis_aclk),
	.reset(!m00_axis_aresetn),

	.fifo_write_e(fifo_write_e),
	.fifo_wdata(fifo_wdata),

	.fifo_read_e(fifo_read_e),
	.fifo_rdata(fifo_rdata),

	.fifo_almost_full(fifo_almost_full),
	.fifo_full(fifo_full),
	.fifo_empty(fifo_empty),
	.fifo_ready(fifo_ready)
);

assign fifo_write_e = aes_controller_out_fifo_w_e;
assign fifo_wdata = aes_controller_out_fifo_data;

assign out_fifo_almost_full = fifo_almost_full;
assign out_fifo_full = fifo_full;
assign out_fifo_empty = fifo_empty;
assign out_fifo_ready = fifo_ready;

assign fifo_read_e = out_fifo_r_e;
assign axis_blk = fifo_rdata;

// AXI logic

localparam AXIS_MASTER_IDLE = 2'b00;
localparam AXIS_MASTER_INIT_SRAM = 2'b01;
localparam AXIS_MASTER_INIT_TRANSFER = 2'b10;
localparam AXIS_MASTER_TRANSFER = 2'b11;

reg [0:1] axis_fsm_state;

assign m00_axis_tdata  = axis_blk_shift[FIFO_DATA_WIDTH-`WORD_S +: `WORD_S];
assign m00_axis_tstrb  = {(C_M_AXIS_TDATA_WIDTH/8){1'b1}};
assign m00_axis_tvalid = axis_tvalid;
assign m00_axis_tlast  = axis_tlast;

assign axis_last_word = axis_last_blk && (axis_word_cnt == `Nb - 1'b1);
assign axis_blk_shift = axis_blk << axis_word_cnt * `WORD_S;
assign axis_last_blk = processing_done && out_fifo_empty;
assign axis_transaction = m00_axis_tready && axis_tvalid;
assign axis_tlast =  axis_last_word;

assign out_fifo_can_read = !out_fifo_r_e && fifo_ready && !fifo_empty;

always @(posedge m00_axis_aclk) begin
	if(!m00_axis_aresetn) begin
		axis_fsm_state <= AXIS_MASTER_IDLE;
		axis_master_done <= 1'b0;
		out_fifo_r_e <= 1'b0;
		axis_word_cnt <= 1'b0;
		axis_tvalid <= 1'b0;
	end 
	else begin
		out_fifo_r_e <= 1'b0;
		axis_tvalid <= 1'b0;

		case (axis_fsm_state)
		AXIS_MASTER_IDLE:
		begin
			axis_fsm_state <= AXIS_MASTER_IDLE;
			axis_master_done <= 1'b0;

			if (out_fifo_can_read) begin
				axis_fsm_state <= AXIS_MASTER_INIT_SRAM;
				out_fifo_r_e <= 1'b1;
			end
		end
		AXIS_MASTER_INIT_SRAM:
		begin
			axis_fsm_state <= AXIS_MASTER_TRANSFER;
		end
		AXIS_MASTER_TRANSFER:
		begin
			axis_fsm_state <= AXIS_MASTER_TRANSFER;
			axis_tvalid <= 1'b1;

			if (axis_transaction) begin
				axis_word_cnt <= axis_word_cnt + 1'b1;

				if (axis_word_cnt == `Nb - 1'b1) begin
					axis_fsm_state <= AXIS_MASTER_IDLE;
					axis_word_cnt <= 1'b0;
					axis_tvalid <= 1'b0;
				end

				if (axis_last_word) begin
					axis_master_done <= 1'b1;
					axis_tvalid <= 1'b0;
				end
			end
		end
		endcase
	end
end
endmodule
