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
	input                                     out_fifo_write_tvalid
);

// FIFO signals

wire fifo_write_tready;
wire fifo_write_tvalid;
wire fifo_read_tvalid;
wire fifo_almost_full;
wire fifo_read_tready;
wire fifo_empty;
wire fifo_full;

reg  [FIFO_DATA_WIDTH-1:0] fifo_data;
wire [FIFO_DATA_WIDTH-1:0] fifo_wdata;
wire [FIFO_DATA_WIDTH-1:0] fifo_rdata;

wire [FIFO_DATA_WIDTH-1:0] fifo_data_shift;

reg fifo_data_last;
reg data_loaded;

wire fifo_read_req;

// bus signals

reg [FIFO_ADDR_WIDTH-1:0] bus_word_cnt;

wire [C_M_AXIS_TDATA_WIDTH-1:0] bus_tdata;
wire bus_tready;
wire bus_tvalid;
wire bus_tlast;

wire bus_transaction;
wire bus_last_word;

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

assign fifo_read_tready = fifo_read_tvalid && !data_loaded;
assign fifo_write_tvalid = out_fifo_write_tvalid;
assign fifo_wdata = aes_controller_out_fifo_data;

assign fifo_read_req = fifo_read_tready && fifo_read_tvalid;

assign out_fifo_write_tready = fifo_write_tready;
assign out_fifo_almost_full = fifo_almost_full;
assign out_fifo_full = fifo_full;
assign out_fifo_empty = fifo_empty;

// AXI logic
axi_stream_master #(
	.AXIS_TDATA_WIDTH(C_M_AXIS_TDATA_WIDTH)
) axis_master (
	.clk(m00_axis_aclk),
	.resetn(m00_axis_aresetn),

	.fifo_tready(bus_tready),
	.fifo_tvalid(bus_tvalid),
	.fifo_tdata(bus_tdata),
	.fifo_tlast(bus_tlast),

	.tready(m00_axis_tready),
	.tvalid(m00_axis_tvalid),
	.tdata(m00_axis_tdata),
	.tlast(m00_axis_tlast)
);

assign m00_axis_tstrb  = {(C_M_AXIS_TDATA_WIDTH/8){1'b1}};

assign bus_last_word = fifo_data_last && (bus_word_cnt == `Nb - 1'b1);
assign fifo_data_shift = fifo_data >> bus_word_cnt * `WORD_S;

assign bus_tdata = fifo_data_shift[0 +: `WORD_S];
assign bus_tlast = bus_last_word;
assign bus_tvalid = data_loaded;

assign bus_transaction = bus_tready && bus_tvalid;

always @(posedge m00_axis_aclk) begin
	if(!m00_axis_aresetn) begin
		fifo_data <= {C_M_AXIS_TDATA_WIDTH{1'b0}};
		data_loaded <= 1'b0;
	end 
	else begin
		if (fifo_read_req) begin
			fifo_data <= fifo_rdata;
			data_loaded <= 1'b1;
		end

		if (bus_transaction && bus_word_cnt == `Nb - 1'b1) begin
			data_loaded <= 1'b0;
		end
	end
end

always @(posedge m00_axis_aclk) begin
	if(!m00_axis_aresetn) begin
		bus_word_cnt <= 1'b0;
	end else begin
		if (bus_transaction) begin
			bus_word_cnt <= bus_word_cnt + 1'b1;

			if (bus_word_cnt == `Nb - 1'b1) begin
				bus_word_cnt <= 1'b0;
			end
		end
	end
end

always @(posedge m00_axis_aclk) begin
	if (!m00_axis_aresetn) begin
		fifo_data_last <= 1'b0;
	end else begin
		if (processing_done && out_fifo_empty)
			fifo_data_last <= 1'b1;

		if (bus_last_word && bus_transaction)
			fifo_data_last <= 1'b0;
	end
end

endmodule
