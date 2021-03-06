// AES controller input block

/*
 * Bus independent AES controller input block, which does the following:
 * - retrieves one 32-bit AES controller command code from the bus
 * - retrieves 32-bit words from the bus, assembles them into 128-bit blocks
 *   and stores them into a FIFO.
 */

`include "aes.vh"

module aes_controller_input #(
	// Width of slave side bus
	parameter integer BUS_DATA_WIDTH = 32,

	parameter integer FIFO_ADDR_WIDTH = 4,
	parameter integer FIFO_DATA_WIDTH = 128
)(
	input wire                              aes_clk,
	input wire                              aes_reset,

	input wire                              bus_clk,
	input wire                              bus_reset,
	input                                   bus_data_wren,
	input                                   bus_tlast,
	input [BUS_DATA_WIDTH-1:0]              bus_data,

	output                                  in_fifo_read_tvalid,
	input                                   in_fifo_read_tready,
	output [FIFO_DATA_WIDTH-1:0]            in_fifo_rdata,

	output                                  controller_in_busy
);

`include "aes_controller.vh"

// AXI related signals
localparam GET_CMD = 1'b0;
localparam GET_PAYLOAD = 1'b1;

wire aes_block_available;

wire [`BLK_S-1:0] aes_blk_next_rev;
wire [`BLK_S-1:0] aes_blk_shift;
wire [`BLK_S-1:0] aes_blk_next;
wire [`BLK_S-1:0] aes_blk;

wire      bus_transaction;
reg [1:0] bus_word_cnt;
reg       fsm_state;

// FIFO signals
wire fifo_write_transaction;

wire fifo_write_tready;
reg  fifo_write_tvalid;
wire fifo_read_tready;
wire fifo_read_tvalid;

reg [FIFO_DATA_WIDTH-1:0] fifo_wdata;
wire [FIFO_DATA_WIDTH-1:0] fifo_rdata;

// Initial assignments
initial fifo_wdata = {FIFO_DATA_WIDTH{1'b0}};
initial fifo_write_tvalid = 1'b0;
initial bus_word_cnt = {2{1'b0}};
initial fsm_state = GET_CMD;

// FIFO logic
async_fifo #(
	.ADDR_WIDTH(FIFO_ADDR_WIDTH),
	.DATA_WIDTH(FIFO_DATA_WIDTH)
) slave_fifo (
	// Write side operates in "Bus" clock domain
	.w_clk(bus_clk),
	.w_reset(bus_reset),

	.write_tvalid(fifo_write_tvalid),
	.write_tready(fifo_write_tready),
	.write_data(fifo_wdata),

	// Read side operates in "Controller" clock domain
	.r_clk(aes_clk),
	.r_reset(aes_reset),

	.read_tready(fifo_read_tready),
	.read_tvalid(fifo_read_tvalid),
	.read_data(fifo_rdata)
);

assign fifo_write_transaction = fifo_write_tvalid && fifo_write_tready;
assign fifo_read_tready = in_fifo_read_tready;

assign in_fifo_read_tvalid = fifo_read_tvalid;
assign in_fifo_rdata = fifo_rdata;

// Controller input logic
assign bus_transaction = bus_data_wren && !controller_in_busy;
assign controller_in_busy = fifo_write_tvalid;

assign aes_block_available = bus_transaction && (bus_word_cnt == `Nb - 1'b1);
assign aes_cmd_available = bus_transaction && (fsm_state == GET_CMD);

assign aes_blk = fifo_wdata[`BLK_S-1:0];
assign aes_blk_shift = (aes_blk >> `WORD_S);
assign aes_blk_next = {bus_data, aes_blk_shift[`BLK_S-1-`WORD_S:0]};
assign aes_blk_next_rev = blk_rev8(aes_blk_next);

always @(posedge bus_clk) begin
	if(bus_reset) begin
		fifo_wdata <= {FIFO_DATA_WIDTH{1'b0}};
		fsm_state <= GET_CMD;
		bus_word_cnt <= 2'b0;
	end
	else begin
		case (fsm_state)
			GET_CMD:
			begin
				if (bus_transaction) begin
					fsm_state <= GET_PAYLOAD;
					fifo_wdata <= {{97'b0}, bus_data};
				end
			end
			GET_PAYLOAD:
			begin
				if (bus_transaction) begin
					bus_word_cnt <= bus_word_cnt + 1'b1;
					fifo_wdata <= {bus_tlast, aes_blk_next};

					if (aes_block_available) begin
						fifo_wdata <= {bus_tlast, aes_blk_next_rev};
						bus_word_cnt <= 1'b0;
					end

					if (bus_tlast) begin
						fsm_state <= GET_CMD;
					end
				end
		end
		endcase
	end
end

always @(posedge bus_clk) begin
	if (bus_reset) begin
		fifo_write_tvalid <= 1'b0;
	end else begin
		if (aes_block_available || aes_cmd_available) begin
			fifo_write_tvalid <= 1'b1;
		end

		if (fifo_write_tvalid && fifo_write_tready) begin
			fifo_write_tvalid <= 1'b0;
		end
	end
end

`ifdef SIMULATION_VERBOSE_EXTREME
integer s_blk_cnt = 0;
integer s_cmd_cnt = 0;

always @(posedge bus_clk) begin
	if (aes_block_available) begin
		$display("AES INPUT: input block no %0d: %H", s_blk_cnt, {bus_tlast, aes_blk_next_rev});
		s_blk_cnt = s_blk_cnt + 1;
	end

	if (aes_cmd_available) begin
		$display("AES_INPUT: cmd no %0d: %H", s_cmd_cnt, {{97'b0}, bus_data});
		s_cmd_cnt = s_cmd_cnt + 1;
	end
end
`endif

`ifdef FORMAL

`ifdef AES_CONTROLLER_INPUT_FORMAL
`define ASSUME assume
`else
`define ASSUME assert
`endif

reg f_past_valid = 1'b0;

initial f_past_valid = 1'b0;

always @(posedge bus_clk)
	f_past_valid <= 1'b1;

always @(*) begin
	if (!f_past_valid) begin
		`ASSUME(reset);
	end
end

always @(*) begin
	if (controller_in_busy)
		`ASSUME(!bus_data_wren);

	if (controller_in_busy)
		`ASSUME(!fifo_write_tvalid);

	// assume tlast will only be received for the last 32 bits of a
	// 128-bit AES block
	if ((bus_word_cnt != `Nb - 1) && !bus_data_wren)
		`ASSUME(!bus_tlast);
end

always @(posedge clk) begin
	if (f_past_valid) begin
		// tlast must be deasserted along with bus_data_wren
		if ($fell(bus_data_wren))
			`ASSUME($fell(bus_tlast));

		// tlast must be asserted along with bus_data_wren
		if ($rose(bus_tlast))
			`ASSUME($rose(bus_data_wren));

		/* TODO */
	end
end

`endif

endmodule
