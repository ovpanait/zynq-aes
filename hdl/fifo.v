/*
 ** FIFO abstraction over single port BRAM module.
 ** It supports concurrent r/w every other clock.
 *
 * @fifo_wdata   - data to be enqueued
 * @fifo_write_e - write enable
 * @fifo_read_e  - read enable
 * @fifo_rdata   - dequeued data
 * @fifo_full    - fifo is full
 * @fifo_empty   - fifo is empty
 * @fifo_ready   - fifo is ready to process a new transaction
 */

module fifo #(
	parameter ADDR_WIDTH = 9,
	parameter DATA_WIDTH = 128,
	parameter DEPTH = 512
)(
	input clk,
	input reset,

	// Write port
	input [DATA_WIDTH-1:0] fifo_wdata,
	input fifo_write_e,

	// Read port
	output [DATA_WIDTH-1:0] fifo_rdata,
	input fifo_read_e,

	// Control signals
	output fifo_full,
	output fifo_empty,
	output fifo_ready
);

wire [ADDR_WIDTH-1:0] read_ptr_next;
wire [ADDR_WIDTH-1:0] write_ptr_next;
reg [ADDR_WIDTH-1:0] write_ptr;
reg [ADDR_WIDTH-1:0] read_ptr;

reg [DATA_WIDTH-1:0] fifo_wdata_reg;
reg [ADDR_WIDTH-1:0] write_ptr_reg;
wire concurrent_rw;
reg fifo_busy;

wire is_last_write;
wire is_last_read;

wire [DATA_WIDTH-1:0] bram_o_data;
wire [DATA_WIDTH-1:0] bram_i_data;
wire [ADDR_WIDTH-1:0] bram_addr;
wire bram_w_e;
wire bram_r_e;

reg fifo_has_data;
reg is_full;

block_ram #(
	.ADDR_WIDTH(ADDR_WIDTH),
	.DATA_WIDTH(DATA_WIDTH),
	.DEPTH(DEPTH)
) out_fifo(
	.clk(clk),

	.addr(bram_addr),
	.i_data(bram_i_data),
	.w_e(bram_w_e),

	.o_data(bram_o_data),
	.r_e(bram_r_e)
);

assign bram_addr = (fifo_busy ? write_ptr_reg : (bram_r_e ? read_ptr : write_ptr));
assign bram_i_data = (fifo_busy ? fifo_wdata_reg : fifo_wdata);
assign fifo_rdata = bram_o_data;
assign bram_w_e = fifo_busy ? fifo_busy : (concurrent_rw ? 1'b0 : fifo_write_e);
assign bram_r_e = fifo_read_e;

assign is_last_write = (write_ptr == DEPTH - 1);
assign is_last_read = (read_ptr == DEPTH - 1);

assign write_ptr_next = is_last_write ? {ADDR_WIDTH{1'b0}} : (write_ptr + 1'b1);
assign read_ptr_next = is_last_read ? {ADDR_WIDTH{1'b0}} : (read_ptr + 1'b1);

assign fifo_empty = ~fifo_has_data;
assign fifo_full = is_full;
assign fifo_ready = !fifo_busy;

assign concurrent_rw = (fifo_write_e && fifo_read_e);

always @(posedge clk) begin
	if (reset) begin
		fifo_wdata_reg <= {DATA_WIDTH{1'b0}};
		write_ptr_reg <= {ADDR_WIDTH{1'b0}};
		write_ptr <= {ADDR_WIDTH{1'b0}};
		read_ptr <= {ADDR_WIDTH{1'b0}};
		fifo_has_data <= 1'b0;
		fifo_busy <= 1'b0;
		is_full <= 1'b0;
	end else begin
		fifo_wdata_reg <= fifo_wdata;
		write_ptr_reg <= write_ptr;
		fifo_busy <= concurrent_rw;

		if (fifo_write_e && !fifo_full) begin
			write_ptr <= write_ptr_next;

			if (!fifo_has_data)
				fifo_has_data <= 1'b1;

			if (write_ptr_next == read_ptr) begin
				is_full = 1'b1;
			end
		end

		if (fifo_read_e && ~fifo_empty) begin
			read_ptr <= read_ptr_next;

			if (is_full)
				is_full = 1'b0;

			if (read_ptr_next == write_ptr && !concurrent_rw)
				fifo_has_data = 1'b0;
		end

		`ifdef SIMULATION
		if (fifo_write_e && fifo_full) begin
			$display("ERROR: %s:%4d: Trying to write data to full FIFO! ", `__FILE__, `__LINE__);
			$finish;
		end

		if (fifo_read_e && fifo_empty) begin
			$display("ERROR: %s:%4d: Trying to read data from empty FIFO! ", `__FILE__, `__LINE__);
			$finish;
		end
		`endif
	end
end

endmodule
