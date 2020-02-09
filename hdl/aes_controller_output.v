`include "aes.vh"

module aes_controller_output #
(
	// Width of master side bus
	parameter integer BUS_TDATA_WIDTH = 32,

	parameter integer FIFO_SIZE = 16,
	parameter integer FIFO_ADDR_WIDTH = 4,
	parameter integer FIFO_DATA_WIDTH = 128
)
(
	input                                     clk,
	input                                     resetn,

	output                                    fifo_write_tready,
	input                                     fifo_write_tvalid,
	input  [FIFO_DATA_WIDTH-1:0]              fifo_wdata,

	output                                    fifo_almost_full,
	output                                    fifo_empty,
	output                                    fifo_full,

	output                                    bus_tvalid,
	input                                     bus_tready,
	output [BUS_TDATA_WIDTH-1:0]              bus_tdata,
	output                                    bus_tlast
);

// FIFO signals

wire fifo_read_tvalid;
wire fifo_read_tready;

wire [FIFO_DATA_WIDTH-1:0] fifo_data_shift;
reg  [FIFO_DATA_WIDTH-1:0] fifo_data;
wire [FIFO_DATA_WIDTH-1:0] fifo_rdata;

reg fifo_data_last;
reg data_loaded;

wire fifo_read_req;

// bus signals

reg [FIFO_ADDR_WIDTH-1:0] bus_word_cnt;

wire bus_transaction;
wire bus_last_word;

// FIFO logic

fifo #(
	.ADDR_WIDTH(FIFO_ADDR_WIDTH),
	.DATA_WIDTH(FIFO_DATA_WIDTH),
	.DEPTH(FIFO_SIZE)
) master_fifo (
	.clk(clk),
	.reset(!resetn),

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

assign fifo_read_req = fifo_read_tready && fifo_read_tvalid;
assign fifo_read_tready = fifo_read_tvalid && !data_loaded;

// Bus logic
assign bus_last_word = fifo_data_last && (bus_word_cnt == `Nb - 1'b1);
assign fifo_data_shift = fifo_data >> bus_word_cnt * `WORD_S;

assign bus_tdata = fifo_data_shift[0 +: `WORD_S];
assign bus_tlast = bus_last_word;
assign bus_tvalid = data_loaded;

assign bus_transaction = bus_tready && bus_tvalid;

always @(posedge clk) begin
	if(!resetn) begin
		fifo_data <= {BUS_TDATA_WIDTH{1'b0}};
		fifo_data_last <= 1'b0;
		data_loaded <= 1'b0;
	end 
	else begin
		if (fifo_read_req) begin
			fifo_data <= fifo_rdata[`BLK_S-1:0];
			fifo_data_last <= fifo_rdata[`BLK_S];
			data_loaded <= 1'b1;
		end

		if (bus_transaction && bus_word_cnt == `Nb - 1'b1) begin
			fifo_data_last <= 1'b0;
			data_loaded <= 1'b0;
		end
	end
end

always @(posedge clk) begin
	if(!resetn) begin
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

endmodule
