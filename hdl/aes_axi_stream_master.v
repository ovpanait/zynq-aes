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

	input  [FIFO_DATA_WIDTH-1:0]              aes_controller_out_fifo_data,

	output                                    out_fifo_almost_full,
	output                                    out_fifo_empty,
	output                                    out_fifo_full,
	output                                    out_fifo_write_tready,
	input                                     out_fifo_write_tvalid,

	output reg                                axis_master_done
);

// FIFO signals

wire fifo_almost_full;
wire fifo_write_tready;
wire fifo_write_tvalid;
wire fifo_read_tready;
wire fifo_read_tvalid;
wire fifo_empty;
wire fifo_full;

wire [FIFO_DATA_WIDTH-1:0] fifo_wdata;
wire [FIFO_DATA_WIDTH-1:0] fifo_rdata;

wire out_fifo_read_req;

// AXI signals

wire [FIFO_DATA_WIDTH-1:0] axis_blk_shift;
reg  [FIFO_ADDR_WIDTH-1:0] axis_word_cnt;
reg  [FIFO_DATA_WIDTH-1:0] axis_blk;
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

	.fifo_write_tvalid(fifo_write_tvalid),
	.fifo_write_tready(fifo_write_tready),
	.fifo_wdata(fifo_wdata),

	.fifo_read_tvalid(fifo_read_tvalid),
	.fifo_read_tready(fifo_read_tready),
	.fifo_rdata(fifo_rdata),

	.fifo_almost_full(fifo_almost_full),
	.fifo_full(fifo_full),
	.fifo_empty(fifo_empty)
);

assign fifo_read_tready = fifo_read_tvalid;
assign fifo_write_tvalid = out_fifo_write_tvalid;
assign fifo_wdata = aes_controller_out_fifo_data;

assign out_fifo_write_tready = out_fifo_write_tvalid && !fifo_full;
assign out_fifo_almost_full = fifo_almost_full;
assign out_fifo_full = fifo_full;
assign out_fifo_empty = fifo_empty;

assign out_fifo_read_req = fifo_read_tready && fifo_read_tvalid;

// AXI logic

assign m00_axis_tdata  = axis_blk_shift[FIFO_DATA_WIDTH-`WORD_S +: `WORD_S];
assign m00_axis_tstrb  = {(C_M_AXIS_TDATA_WIDTH/8){1'b1}};
assign m00_axis_tvalid = axis_tvalid;
assign m00_axis_tlast  = axis_tlast;

assign axis_last_word = axis_last_blk && (axis_word_cnt == `Nb - 1'b1);
assign axis_blk_shift = axis_blk << axis_word_cnt * `WORD_S;
assign axis_last_blk = processing_done && out_fifo_empty;
assign axis_transaction = m00_axis_tready && axis_tvalid;
assign axis_tlast =  axis_last_word;

always @(posedge m00_axis_aclk) begin
	if(!m00_axis_aresetn) begin
		axis_blk <= 1'b0;
		axis_tvalid <= 1'b0;
	end 
	else begin
		if (out_fifo_read_req) begin
			axis_blk <= fifo_rdata;
			axis_tvalid <= 1'b1;
		end

		if (axis_transaction && axis_word_cnt == `Nb - 1'b1) begin
			axis_tvalid <= 1'b0;
		end
	end
end

always @(posedge m00_axis_aclk) begin
	if(!m00_axis_aresetn) begin
		axis_master_done <= 1'b0;
		axis_word_cnt <= 1'b0;
	end else begin
		axis_master_done <= 1'b0;

		if (axis_transaction) begin
			axis_word_cnt <= axis_word_cnt + 1'b1;

			if (axis_word_cnt == `Nb - 1'b1) begin
				axis_word_cnt <= 1'b0;
			end

			if (axis_last_word) begin
				axis_master_done <= 1'b1;
			end
		end
	end
end

endmodule
