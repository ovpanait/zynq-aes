// AXI slave implementation
/*
 * The AXI slave control logic is:
 * - Take 4 x 32-bit words from the AXI bus and fill the axis_blk variable
 * - Store axis_blk as 1 x 128-bit word in the FIFO so it can be retrieved later
 *   by the AES controller.
 *
 *
 * The input FIFO is implemented as 128-bit Block RAM:
 * - AXI slave logic writes to it
 * - AES controller reads from it
 */

module aes_axi_stream_slave #(
	// Width of slave side bus
	parameter integer C_S_AXIS_TDATA_WIDTH = 32,

	parameter integer FIFO_SIZE = 16,
	parameter integer FIFO_ADDR_WIDTH = 4,
	parameter integer FIFO_DATA_WIDTH = 128
)(
	/*
	* Slave side ports
	*/

	input                                   s00_axis_aclk,
	input                                   s00_axis_aresetn,
	output                                  s00_axis_tready,
	input                                   s00_axis_tlast,
	input                                   s00_axis_tvalid,
	input [C_S_AXIS_TDATA_WIDTH-1 : 0]      s00_axis_tdata,
	input [(C_S_AXIS_TDATA_WIDTH/8)-1 : 0]  s00_axis_tstrb,

	input                                   axis_master_done,
	input                                   aes_controller_in_fifo_r_e,

	output reg [`WORD_S-1:0]                axis_cmd,
	output reg                              axis_slave_done,

	output [FIFO_DATA_WIDTH-1:0]            in_fifo_rdata,
	output                                  in_fifo_read_tvalid,
	output                                  in_fifo_almost_full,
	output                                  in_fifo_empty,
	output                                  in_fifo_full
);

// AXI related signals
reg axis_packet_end;

wire axis_data_available;
wire aes_block_available;
wire axis_tlast;

wire [C_S_AXIS_TDATA_WIDTH - 1 : 0] axis_data;

wire [FIFO_DATA_WIDTH-1:0] axis_blk_shift;
wire [FIFO_DATA_WIDTH-1:0] axis_blk_next;
reg [FIFO_DATA_WIDTH-1:0]  axis_blk;

wire      axis_slave_in_fifo_addr_is_last;
reg [1:0] axis_word_cnt;
reg       axis_fsm_state;

// FIFO signals
wire fifo_write_tready;
reg  fifo_write_tvalid;
wire fifo_read_tready;
wire fifo_read_tvalid;

wire [FIFO_DATA_WIDTH-1:0] fifo_wdata;
wire [FIFO_DATA_WIDTH-1:0] fifo_rdata;

wire fifo_almost_full;
wire fifo_full;
wire fifo_empty;

wire in_fifo_busy;

// FIFO logic

fifo #(
	.ADDR_WIDTH(FIFO_ADDR_WIDTH),
	.DATA_WIDTH(FIFO_DATA_WIDTH),
	.DEPTH(FIFO_SIZE)
) slave_fifo (
	.clk(s00_axis_aclk),
	.reset(!s00_axis_aresetn),

	.fifo_write_tvalid(fifo_write_tvalid),
	.fifo_write_tready(fifo_write_tready),
	.fifo_wdata(fifo_wdata),

	.fifo_read_tready(fifo_read_tready),
	.fifo_read_tvalid(fifo_read_tvalid),
	.fifo_rdata(fifo_rdata),

	.fifo_almost_full(fifo_almost_full),
	.fifo_full(fifo_full),
	.fifo_empty(fifo_empty)
);

assign fifo_read_tready = aes_controller_in_fifo_r_e;
assign fifo_wdata = axis_blk;

assign in_fifo_read_tvalid = fifo_read_tvalid;
assign in_fifo_almost_full = fifo_almost_full;
assign in_fifo_rdata = fifo_rdata;
assign in_fifo_empty = fifo_empty;
assign in_fifo_full = fifo_full;

assign in_fifo_busy = axis_slave_done || in_fifo_full || fifo_write_tvalid;

// AXI logic

axi_stream_slave #(
	.C_S_AXIS_TDATA_WIDTH(C_S_AXIS_TDATA_WIDTH)
) axi_stream_slave_controller (
	.clk(s00_axis_aclk),
	.resetn(s00_axis_aresetn),
	.tready(s00_axis_tready),
	.tlast(s00_axis_tlast),
	.tvalid(s00_axis_tvalid),
	.tdata(s00_axis_tdata),
	.tstrb(s00_axis_tstrb),

	.fifo_busy(in_fifo_busy),
	.fifo_wren(axis_data_available),
	.fifo_data(axis_data),

	.stream_tlast(axis_tlast)
);

localparam AXIS_SLAVE_GET_CMD = 1'b0;
localparam AXIS_SLAVE_GET_PAYLOAD = 1'b1;

assign aes_block_available = axis_data_available && (axis_word_cnt == `Nb - 1'b1);

assign axis_blk_next = {axis_data, axis_blk_shift[`BLK_S-1-`WORD_S:0]};
assign axis_blk_shift = (axis_blk >> `WORD_S);

always @(posedge s00_axis_aclk) begin
	if(!s00_axis_aresetn) begin
		axis_fsm_state <= AXIS_SLAVE_GET_CMD;
		axis_word_cnt <= 1'b0;
		axis_blk <= 1'b0;
		axis_cmd <= 1'b0;
	end
	else begin
		case (axis_fsm_state)
			AXIS_SLAVE_GET_CMD:
			begin
				if (axis_data_available) begin
					axis_fsm_state <= AXIS_SLAVE_GET_PAYLOAD;
					axis_cmd <= axis_data;
				end
			end
			AXIS_SLAVE_GET_PAYLOAD:
			begin
				if (axis_data_available) begin
					axis_word_cnt <= axis_word_cnt + 1'b1;
					axis_blk <= axis_blk_next;

					if (aes_block_available) begin
						axis_word_cnt <= 1'b0;
					end

					if (axis_tlast) begin
						axis_fsm_state <= AXIS_SLAVE_GET_CMD;
					end
				end
		end
		endcase
	end
end

always @(posedge s00_axis_aclk) begin
	if (!s00_axis_aresetn) begin
		fifo_write_tvalid <= 1'b0;
	end else begin
		if (aes_block_available) begin
			fifo_write_tvalid <= 1'b1;
		end

		if (fifo_write_tvalid && fifo_write_tready) begin
			fifo_write_tvalid <= 1'b0;
		end
	end
end

always @(posedge s00_axis_aclk) begin
	if (!s00_axis_aresetn) begin
		axis_packet_end <= 1'b0;
	end else begin
		if (axis_tlast && aes_block_available) begin
			axis_packet_end <= 1'b1;
		end

		if (axis_master_done) begin
			axis_packet_end <= 1'b0;
		end
	end
end

always @(posedge s00_axis_aclk) begin
	if (!s00_axis_aresetn) begin
		axis_slave_done <= 1'b0;
	end else begin
		if (axis_packet_end && fifo_write_tvalid && fifo_write_tready) begin
			axis_slave_done <= 1'b1;
		end

		if (axis_master_done) begin
			axis_slave_done <= 1'b0;
		end
	end
end

endmodule
