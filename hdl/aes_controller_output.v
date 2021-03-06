`include "aes.vh"

module aes_controller_output #
(
	// Width of master side bus
	parameter integer BUS_TDATA_WIDTH = 32,

	parameter integer FIFO_ADDR_WIDTH = 4,
	parameter integer FIFO_DATA_WIDTH = 128
)
(
	input wire                                bus_clk,
	input wire                                bus_reset,

	input wire                                aes_clk,
	input wire                                aes_reset,

	output                                    fifo_write_tready,
	input                                     fifo_write_tvalid,
	input  [FIFO_DATA_WIDTH-1:0]              fifo_wdata,

	output                                    bus_tvalid,
	input                                     bus_tready,
	output [BUS_TDATA_WIDTH-1:0]              bus_tdata,
	output                                    bus_tlast
);

`include "aes_controller.vh"

// FIFO signals

wire fifo_read_tvalid;
wire fifo_read_tready;

wire [FIFO_DATA_WIDTH-1:0] fifo_data_rev_shift;
wire [FIFO_DATA_WIDTH-1:0] fifo_data_rev;
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

async_fifo #(
	.ADDR_WIDTH(FIFO_ADDR_WIDTH),
	.DATA_WIDTH(FIFO_DATA_WIDTH)
) master_fifo (
	// Write side operates in "Controller" clock domain
	.w_clk(aes_clk),
	.w_reset(aes_reset),

	.write_tvalid(fifo_write_tvalid),
	.write_tready(fifo_write_tready),
	.write_data(fifo_wdata),

	// Read side operates in "Bus" clock domain
	.r_clk(bus_clk),
	.r_reset(bus_reset),

	.read_tvalid(fifo_read_tvalid),
	.read_tready(fifo_read_tready),
	.read_data(fifo_rdata)
);

assign fifo_read_req = fifo_read_tready && fifo_read_tvalid;
assign fifo_read_tready = fifo_read_tvalid && !data_loaded;

// Bus logic
assign bus_last_word = fifo_data_last && (bus_word_cnt == `Nb - 1'b1);
assign fifo_data_rev = blk_rev8(fifo_data);
assign fifo_data_rev_shift = fifo_data_rev >> bus_word_cnt * `WORD_S;

assign bus_tdata = fifo_data_rev_shift[0 +: `WORD_S];
assign bus_tlast = bus_last_word;
assign bus_tvalid = data_loaded;

assign bus_transaction = bus_tready && bus_tvalid;

always @(posedge bus_clk) begin
	if(bus_reset) begin
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

always @(posedge bus_clk) begin
	if(bus_reset) begin
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

//`define SIMULATION_VERBOSE_EXTREME
`ifdef SIMULATION_VERBOSE_EXTREME
integer s_fifo_blk_cnt = 0;

always @(posedge bus_clk) begin
	if (fifo_read_req) begin
		$display("AES OUTPUT: FIFO blk no: %0d: %H", s_fifo_blk_cnt, fifo_rdata[`BLK_S-1:0]);
		s_fifo_blk_cnt = s_fifo_blk_cnt + 1;
	end
end
`endif

endmodule
