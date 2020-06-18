/*
   * AXI Stream async fifo with Yosys formal properties. Implemented as a
   * wrapper over dual-port block ram module.
   *
   * Inspired by:
   *   https://gist.github.com/promach/1854bb054bb751fdfe02a3e655266e8e
   *   https://github.com/ZipCPU/website/blob/master/examples/afifo.v
*/

//`default_nettype none

module async_fifo #(
	parameter integer DATA_WIDTH = 32,
	parameter integer ADDR_WIDTH = 5
)(

	// Read
	input                         r_clk,
	input                         r_reset,
	input                         read_tready,
	output reg                    read_tvalid,
	output [DATA_WIDTH - 1:0]     read_data,

	// Write
	input                        w_clk,
	input                        w_reset,
	input                        write_tvalid,
	output reg                   write_tready,
	input [DATA_WIDTH - 1:0]     write_data
);

localparam integer NUM_ENTRIES = (1'b1 << ADDR_WIDTH);

wire bram_w_e;
wire [DATA_WIDTH-1:0] bram_w_data;
wire [ADDR_WIDTH-1:0] bram_w_addr;
wire [DATA_WIDTH-1:0] bram_r_data;
wire [ADDR_WIDTH-1:0] bram_r_addr;

wire read_en;
reg  r_wait;
reg  [DATA_WIDTH-1:0] r_skidbuf;

wire [ADDR_WIDTH - 1:0] write_ptr_sync;
reg  [ADDR_WIDTH - 1:0] read_ptr;
reg  [ADDR_WIDTH - 1:0] read_ptr_gray;
wire [ADDR_WIDTH - 1:0] read_ptr_nxt;
wire [ADDR_WIDTH - 1:0] read_ptr_gray_nxt;
wire  reset_rsync;

wire write_en;
wire [ADDR_WIDTH - 1:0] read_ptr_sync;
reg  [ADDR_WIDTH - 1:0] write_ptr;
reg  [ADDR_WIDTH - 1:0] write_ptr_gray;
wire [ADDR_WIDTH - 1:0] write_ptr_nxt;
wire [ADDR_WIDTH - 1:0] write_ptr_nxt_nxt;
wire [ADDR_WIDTH - 1:0] write_ptr_gray_nxt;
wire [ADDR_WIDTH - 1:0] write_ptr_gray_nxt_nxt;
wire reset_wsync;

wire empty;
wire full;

assign read_ptr_nxt = read_ptr + 1'b1;
assign read_ptr_gray_nxt = read_ptr_nxt ^ (read_ptr_nxt >> 1);
assign write_ptr_nxt = write_ptr + 1'b1;
assign write_ptr_nxt_nxt = write_ptr_nxt + 1'b1;
assign write_ptr_gray_nxt = write_ptr_nxt ^ (write_ptr_nxt >> 1);
assign write_ptr_gray_nxt_nxt = write_ptr_nxt_nxt ^ (write_ptr_nxt_nxt >> 1);

//
// BLOCK RAM logic
//
assign bram_w_e = write_en;
assign bram_w_addr = write_ptr;
assign bram_w_data = write_data;

assign bram_r_addr = read_ptr;

block_ram #(
	.ADDR_WIDTH(ADDR_WIDTH),
	.DATA_WIDTH(DATA_WIDTH)
) bram (
	.r_clk(r_clk),
	.w_clk(w_clk),

	.r_data(bram_r_data),
	.r_addr(bram_r_addr),

	.w_e(bram_w_e),
	.w_data(bram_w_data),
	.w_addr(bram_w_addr)
);


//
// Read clock domain
//
assign read_en = read_tvalid && read_tready;
assign empty = write_ptr_sync == read_ptr_gray;

synchronizer #(.WIDTH(ADDR_WIDTH)) write_ptr_synchronizer(
	.clk(r_clk),
	.reset(reset_rsync),
	.data_o(write_ptr_sync),
	.data_i(write_ptr_gray)
);

synchronizer #(.RESET_STATE(1)) r_reset_synchronizer(
	.clk(r_clk),
	.reset(r_reset),
	.data_i(0),
	.data_o(reset_rsync)
);

always @(posedge r_clk, posedge reset_rsync) begin
	if (reset_rsync) begin
		read_ptr <= 0;
		read_ptr_gray <= 0;
	end else if (~empty && (read_en || ~read_tvalid)) begin
		read_ptr <= read_ptr_nxt;
		read_ptr_gray <= read_ptr_gray_nxt;
	end
end

always @(posedge r_clk, posedge reset_rsync) begin
	if (reset_rsync) begin
		r_wait <= 1'b0;
		read_tvalid <= 1'b0;
		r_skidbuf <= {DATA_WIDTH{1'b0}};
	end else begin
		if (!empty)
			read_tvalid <= 1'b1;

		if (~r_wait && read_tvalid && ~read_tready) begin
			r_skidbuf <= bram_r_data;
			r_wait <= 1'b1;
		end

		if (read_en) begin
			if (empty)
				read_tvalid <= 1'b0;
			r_wait <= 1'b0;
		end
	end
end

assign read_data = r_wait ? r_skidbuf : bram_r_data;

//
// Write clock domain
//
assign full = write_ptr_gray_nxt == read_ptr_sync;
assign write_en = write_tready && write_tvalid;

synchronizer #(.WIDTH(ADDR_WIDTH)) read_ptr_synchronizer(
	.clk(w_clk),
	.reset(reset_wsync),
	.data_o(read_ptr_sync),
	.data_i(read_ptr_gray)
);

synchronizer #(.RESET_STATE(1)) w_reset_synchronizer(
	.clk(w_clk),
	.reset(w_reset),
	.data_i(0),
	.data_o(reset_wsync)
);

integer i;

always @(posedge w_clk, posedge reset_wsync) begin
	if (reset_wsync) begin
		write_tready <= 1'b0;
	end else begin
		if (write_en && (write_ptr_gray_nxt_nxt == read_ptr_sync))
			write_tready <= 1'b0;
		else if (write_ptr_gray_nxt != read_ptr_sync)
			write_tready <= 1'b1;
	end
end

always @(posedge w_clk, posedge reset_wsync) begin
	if (reset_wsync) begin
		write_ptr <= 0;
		write_ptr_gray <= 0;
	end else if (write_en) begin
		write_ptr <= write_ptr_nxt;
		write_ptr_gray <= write_ptr_gray_nxt;
	end
end

`ifdef FORMAL
reg first_clock_had_passed;
reg first_write_clock_had_passed;
reg first_read_clock_had_passed;

initial first_clock_had_passed = 0;
initial first_write_clock_had_passed = 0;
initial first_read_clock_had_passed = 0;

always @($global_clock)
	first_clock_had_passed <= 1;

always @(posedge w_clk)
	first_write_clock_had_passed <= 1;

always @(posedge r_clk)
	first_read_clock_had_passed <= 1;

//always @($global_clock)
//	assert($rose(reset_wsync)==$rose(reset_rsync));  // comment this out for experiment

initial assume(w_reset);
initial assume(r_reset);
initial assert(empty);
initial assert(!full);
initial assert(!r_wait);
initial assert(!write_tready);

always @($global_clock) begin
	if(reset_wsync) begin
		assert(write_ptr == 0);
		assert(write_ptr_gray == 0);
		assert(!full);
	end else if(first_write_clock_had_passed) begin
		// fifo_write_tvalid gets deasserted only after a successful transfer
		if ($fell(write_tvalid))
			assume($past(write_tready));

		// write data must be stable if no transfer occurs
		if ($stable(write_tvalid && !write_tready))
			assume($stable(write_data));

		if (write_en) begin
			assert(bram_w_e);
			assert(bram_w_data == write_data);
			assert(bram_w_addr == write_ptr[ADDR_WIDTH-1:0]);
		end

		if ($rose(write_tready))
			assert($past(!write_tready && !full));

		if ($fell(write_tready))
			assert($past(write_en && (write_ptr_gray_nxt_nxt == read_ptr_sync)));

		if ($past(!write_tready && full)) begin
			assert(!write_tready);
			assert($stable(write_tready));
		end

		// TODO - fails induction due to read/write pointers not
		//        operating correctly
		//if (write_tready)
		//	assert(!full);

		// Write pointer
		if (!$stable(write_ptr)) begin
			assert(write_ptr == ($past(write_ptr) + 1'b1));
			assert($past(write_en));
		end
	end
end

always @(*) begin
	if (!reset_wsync)
		assert(write_ptr_gray == ((write_ptr >> 1) ^ write_ptr));
end

always @($global_clock) begin
	if(reset_rsync) begin
		assert(read_ptr == 0);
		assert(read_ptr_gray == 0);
		assert(empty);

		assert(r_wait == 0);
		assert(r_skidbuf == 0);
	end else if(first_read_clock_had_passed) begin
		// only deassert read tvalid after successful read or write
		// transaction
		if ($fell(read_tvalid)) begin
			assert($past(read_tready));
		end

		// fifo_rdata must be stable if no transfer occurs
		if ($past(read_tvalid && !read_tready)) begin
			assert($stable(read_data));
		end

		// Internal signals assertions
		if ($rose(r_wait)) begin
			assert($stable(read_tvalid));
			assert(read_tvalid);
			assert($stable(read_data));
		end

		// Read pointer
		if (!$stable(read_ptr)) begin
			assert($past(~empty && (read_en || ~read_tvalid)));
			assert(read_ptr == ($past(read_ptr) + 1'b1));
		end

	end
end

always @(*) begin
	if (!reset_rsync)
		assert(read_ptr_gray == ((read_ptr >> 1) ^ read_ptr));
end

always @($global_clock) begin
	if (first_clock_had_passed) begin
		if(reset_wsync) begin
			assert(!write_tready);
			assert(!full);
			//assert(read_data == 0);
		end else if (!$rose(w_clk)) begin
			assume($stable(write_tvalid));
			assume($stable(write_data));
			assert($stable(write_tready));
			assert($stable(full));
		end

		if(reset_rsync)
			assert(empty);
		else if (!$rose(r_clk)) begin
			assume($stable(read_tready));
			assert($stable(read_tvalid));
			assert($stable(empty));

			if(!reset_wsync && !$rose(w_clk) && !write_en)
				assert($stable(read_data));
		end
	end
end
`endif

// Generate clocks
`ifdef FORMAL
localparam F_CLKBITS=5;
wire [F_CLKBITS-1:0] f_wclk_step, f_rclk_step;

assign f_wclk_step = $anyconst;
assign f_rclk_step = $anyconst;

always @(*)
	assume(f_wclk_step != 0);
always @(*)
	assume(f_rclk_step != 0);
always @(*)
	assume(f_rclk_step != f_wclk_step); // so that we have two different clock speed

reg [F_CLKBITS-1:0] f_wclk_count, f_rclk_count;

always @($global_clock)
	f_wclk_count <= f_wclk_count + f_wclk_step;
always @($global_clock)
	f_rclk_count <= f_rclk_count + f_rclk_step;

always @(*) begin
	assume(w_clk == f_wclk_count[F_CLKBITS-1]);
	assume(r_clk == f_rclk_count[F_CLKBITS-1]);
	cover(w_clk);
	cover(r_clk);
end
`endif

`ifdef FORMAL
////////////////////////////////////////////////////
//
// Some cover statements, to make sure valuable states
// are even reachable
//
////////////////////////////////////////////////////
//

// Make sure a reset is possible in either domain
always @(posedge w_clk)
	cover(w_reset);

always @(posedge r_clk)
	cover(r_reset);


always @($global_clock)
	if (first_clock_had_passed)
		cover((empty)&&(!$past(empty)));

always @(*)
	if (first_clock_had_passed)
		cover(full);

always @(posedge w_clk)
	if (first_write_clock_had_passed)
		cover($past(full)&&(!full));

always @(posedge w_clk)
	cover(write_en);

always @(posedge r_clk)
	if (first_read_clock_had_passed)
		cover($past(!empty)&&($past(read_en))&&(empty));

// Check that write tready can get asserted/deasserted
always @(posedge w_clk) begin
	cover($rose(write_tready));
	cover($fell(write_tready));
end
`endif


`ifdef FORMAL
/* twin-write test */
// write two pieces of different data into the asynchronous fifo
// then read them back from the asynchronous fifo

wire [DATA_WIDTH - 1:0] first_data;
wire [DATA_WIDTH - 1:0] second_data;

assign first_data = $anyconst;
assign second_data = $anyconst;

reg first_data_is_written;
reg first_data_is_read;
reg second_data_is_written;
reg second_data_is_read;

initial first_data_is_read = 0;
initial second_data_is_read = 0;
initial first_data_is_written = 0;
initial second_data_is_written = 0;

always @(*) assume(first_data != 0);
always @(*) assume(second_data != 0);
always @(*) assume(first_data != second_data);

always @(posedge w_clk) begin
	if(reset_wsync) begin
		first_data_is_written <= 0;
		second_data_is_written <= 0;
	end else if(write_en && !first_data_is_written) begin
		assume(write_data == first_data);
		first_data_is_written <= 1;
	end else if(write_en && !second_data_is_written) begin
		assume(write_data == second_data);
		second_data_is_written <= 1;
	end
end

reg [DATA_WIDTH - 1:0] first_data_read_out;
reg [DATA_WIDTH - 1:0] second_data_read_out;

initial first_data_read_out = 0;
initial second_data_read_out = 0;

always @(posedge r_clk) begin
	if(reset_rsync) begin
		first_data_read_out <= 0;
		first_data_is_read <= 0;
		second_data_is_read <= 0;
	end else if(read_en && first_data_is_written && !first_data_is_read) begin
		first_data_read_out <= read_data;
		first_data_is_read <= 1;
	end else if(read_en && second_data_is_written && !second_data_is_read) begin
		second_data_read_out <= read_data;
		second_data_is_read <= 1;
		end
	end

always @($global_clock) begin
	cover(first_data_is_written);
	cover(second_data_is_written);
end

always @($global_clock) begin
	if(first_data_is_read) cover(first_data == first_data_read_out);
	if(second_data_is_read) cover(second_data == second_data_read_out);
end

`endif

endmodule
