/*
 ** FIFO abstraction over single port BRAM module.
 *
 ** It uses TVALID / TREADY handshake for both the read and write ports and
 ** allows concurrent r/w.
 *
 ** A successful read takes place when both fifo_read_tvalid and
 ** fifo_read_tready are HIGH.
 *
 ** A successful write takes place when both fifo_write_tavlid and
 ** fifo_write_tready are HIGH.
 *
 * @fifo_wdata
 * @fifo_write_tvalid
 * @fifo_write_tready
 * @fifo_read_tready
 * @fifo_read_tvalid
 * @fifo_rdata
 */

module fifo #(
	parameter ADDR_WIDTH = 2,
	parameter DATA_WIDTH = 128
)(
	input                          clk,
	input                          reset,

	// Write port
	input [DATA_WIDTH-1:0]         fifo_wdata,
	output reg                     fifo_write_tready,
	input                          fifo_write_tvalid,

	// Read port
	output reg [DATA_WIDTH-1:0]    fifo_rdata,
	output reg                     fifo_read_tvalid,
	input                          fifo_read_tready
);

reg [ADDR_WIDTH:0] write_ptr;
reg [ADDR_WIDTH:0] read_ptr;

wire fifo_read_transaction;
wire fifo_write_transaction;

reg  bram_w_e;
reg  [DATA_WIDTH-1:0] bram_w_data;
reg  [ADDR_WIDTH-1:0] bram_w_addr;
wire [DATA_WIDTH-1:0] bram_r_data;
reg  [ADDR_WIDTH-1:0] bram_r_addr;

reg  fifo_full;
reg  fifo_empty;

reg r_wait;
reg [DATA_WIDTH-1:0] r_skidbuf;

block_ram #(
	.ADDR_WIDTH(ADDR_WIDTH),
	.DATA_WIDTH(DATA_WIDTH)
) bram (
	.clk(clk),

	.r_data(bram_r_data),
	.r_addr(bram_r_addr),

	.w_e(bram_w_e),
	.w_data(bram_w_data),
	.w_addr(bram_w_addr)
);

initial write_ptr = {ADDR_WIDTH+1{1'b0}};
initial read_ptr = {ADDR_WIDTH+1{1'b0}};
initial r_skidbuf = {DATA_WIDTH{1'b0}};
initial fifo_read_tvalid = 1'b0;
initial r_wait = 1'b0;

always @(*) begin
	bram_w_e = fifo_write_transaction;
	bram_w_addr = write_ptr[ADDR_WIDTH-1:0];
	bram_w_data = fifo_wdata;

	bram_r_addr = read_ptr[ADDR_WIDTH-1:0];
end

assign fifo_write_transaction = fifo_write_tvalid && fifo_write_tready;
assign fifo_read_transaction = fifo_read_tvalid && fifo_read_tready;

always @(*) begin
	fifo_empty = (read_ptr == write_ptr);
	fifo_full  = (write_ptr[ADDR_WIDTH] != read_ptr[ADDR_WIDTH]) &&
		     (write_ptr[ADDR_WIDTH-1:0] == read_ptr[ADDR_WIDTH-1:0]);

	fifo_write_tready = !fifo_full;

	fifo_rdata = r_wait ? r_skidbuf : bram_r_data;
end

always @(posedge clk) begin
	if (reset) begin
		write_ptr <= {ADDR_WIDTH+1{1'b0}};
	end else begin
		if (fifo_write_transaction) begin
			write_ptr <= write_ptr + 1'b1;
		end
	end
end

// Read side logic
always @(posedge clk) begin
	if (reset) begin
		r_skidbuf <= {DATA_WIDTH{1'b0}};
		fifo_read_tvalid <= 1'b0;
		r_wait <= 1'b0;
	end else begin
		if (!fifo_empty) begin
			fifo_read_tvalid <= 1'b1;
		end

		if (~r_wait && fifo_read_tvalid && ~fifo_read_tready) begin
				r_skidbuf <= bram_r_data;
				r_wait <= 1'b1;
		end

		if (fifo_read_transaction) begin
			if (fifo_empty)
				fifo_read_tvalid <= 1'b0;
			r_wait <= 1'b0;
		end
	end
end

always @(posedge clk) begin
	if (reset) begin
		read_ptr <= {ADDR_WIDTH+1{1'b0}};
	end else begin
		if (~fifo_empty && (fifo_read_transaction || ~fifo_read_tvalid))
			read_ptr <= read_ptr + 1'b1;
	end
end

//`define SIMULATION_VERBOSE
`ifdef SIMULATION_VERBOSE
always @(posedge clk) begin
	if (fifo_write_transaction) begin
		$display("Writing %H to address %H", fifo_wdata,
				write_ptr[ADDR_WIDTH-1:0]);
	end

	if (fifo_read_transaction) begin
		$display("Reading %H", fifo_rdata);
	end
end
`endif

`ifdef FORMAL

`ifdef FIFO_FORMAL
`define ASSUME assume
`else
`define ASSUME assert
`endif

reg f_past_valid;
wire [ADDR_WIDTH:0] f_fill;

initial f_past_valid = 1'b0;
initial assert(f_fill == 0);

assign f_fill = write_ptr - read_ptr;

always @(posedge clk)
	f_past_valid <= 1'b1;

always @(*)
	if (!f_past_valid)
		`ASSUME(reset);
	else
		`ASSUME(!reset);

always @(posedge clk) begin
	if (f_past_valid) begin
		// fifo_write_tvalid gets deasserted only after a successful transfer
		if ($fell(fifo_write_tvalid))
			`ASSUME($past(fifo_write_tready));

		// write data must be stable if no transfer occurs
		if ($stable(fifo_write_tvalid && !fifo_write_tready))
			`ASSUME($stable(fifo_wdata));
	end
end

always @(*) begin
	// Make sure read/write pointers are within range
	assert(f_fill <= {1'b1, {ADDR_WIDTH{1'b0}}});

	if (fifo_write_transaction)
		assert(!fifo_full);

	if (fifo_empty) begin
		assert(!fifo_full);
		assert(read_ptr == write_ptr);
		assert(f_fill == 0);
	end

	// write TREADY should not be enabled when the fifo is full
	if (fifo_full) begin
		assert((read_ptr[ADDR_WIDTH] != write_ptr[ADDR_WIDTH]) &&
		       (read_ptr[ADDR_WIDTH-1:0] == write_ptr[ADDR_WIDTH-1:0]));
	assert(f_fill == {1'b1, {ADDR_WIDTH{1'b0}}});
		assert(!fifo_write_tready);
	end
end

always @(posedge clk) begin
	if (f_past_valid) begin
		// only deassert read tvalid after successful read or write
		// transaction
		if ($fell(fifo_read_tvalid)) begin
			assert($past(fifo_read_tready || reset));
		end

		// fifo_rdata must be stable if no transfer occurs
		if ($past(fifo_read_tvalid && !fifo_read_tready)) begin
			assert($stable(fifo_rdata));
		end

		if (fifo_write_transaction) begin
			assert(bram_w_e);
			assert(bram_w_data == fifo_wdata);
			assert(bram_w_addr == write_ptr[ADDR_WIDTH-1:0]);
		end

		// Internal signals assertions
		if ($rose(r_wait)) begin
			assert($stable(fifo_read_tvalid));
			assert(fifo_read_tvalid);

			assert($stable(fifo_rdata));
		end
	end
end

`endif

endmodule
