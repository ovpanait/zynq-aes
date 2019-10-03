`timescale 1ns/1ns
`define PERIOD 10

module tb_main();

localparam ADDR_WIDTH = 9;
localparam DATA_WIDTH = 128;
localparam DEPTH = 11;

integer errors;

reg clk;
reg reset;
reg en;

reg fifo_write_e;
reg fifo_read_e;

reg [DATA_WIDTH-1:0] fifo_wdata;
wire [DATA_WIDTH-1:0] fifo_rdata;

wire fifo_full;
wire fifo_empty;
wire fifo_ready;

integer words_no = 50;

fifo #(
	.ADDR_WIDTH(ADDR_WIDTH),
	.DATA_WIDTH(DATA_WIDTH),
	.DEPTH(DEPTH)
) DUT (
	.clk(clk),
	.reset(reset),

	.fifo_write_e(fifo_write_e),
	.fifo_wdata(fifo_wdata),

	.fifo_read_e(fifo_read_e),
	.fifo_rdata(fifo_rdata),
	
	.fifo_full(fifo_full),
	.fifo_empty(fifo_empty),
	.fifo_ready(fifo_ready)
);

// Test functions
`include "test_fc.vh"
`include "queue_wrapper.vh"

initial begin
   clk <= 0;
   forever #(`PERIOD) clk = ~clk;
end

initial begin
   reset <= 0;
   @(posedge clk); //may need several cycles for reset
   @(negedge clk) reset = 1;
end

initial begin
	integer i;
	integer j;

	errors = 0;

	// Testcase init
	wait(reset)
	@(posedge clk);
	@(negedge clk) reset = 0;

	// Testcase
	`VERIFY(fifo_empty, 1'b1);

	rw_cycle(words_no);

	`VERIFY(fifo_empty, 1'b1);
	@(negedge clk);

	concurrent_rw_cycle(words_no);

	@(negedge clk);
	@(negedge clk);

	// Testcase end
	@(negedge clk) reset = 1;
	@(negedge clk);

	$display("\nSimulation completed without errors. \n");
	$finish;
end

task write_data(input queue_wrapper#(DATA_WIDTH) fifo_data);
		`VERIFY(fifo_ready, 1'b1);
		fifo_write_e = 1'b1;

		std::randomize(fifo_wdata);
		fifo_data.push_back(fifo_wdata);
endtask

task read_data(input queue_wrapper#(DATA_WIDTH) fifo_data, input bit is_last);
	reg [DATA_WIDTH-1:0] data;

	data = fifo_data.pop_front();
	`VERIFY(fifo_rdata, data);

	fifo_read_e = 1'b1;

	if (is_last)
		fifo_read_e = 1'b0;
endtask

task rw_cycle(integer words_no);
	integer i;
	bit read_pending;

	queue_wrapper#(DATA_WIDTH) fifo_data;
	fifo_data = new();

	// Reset queue state
	@(negedge clk);
	read_pending = 1'b0;
	fifo_write_e = 1'b0;
	fifo_read_e = 1'b0;

	// Perform words_no consecutive r/w operations
	for (i=0; i < words_no; i=i+1) begin
		@(negedge clk);
		if (read_pending) begin
			read_data(fifo_data, 1'b0);
			read_pending = 1'b0;
		end

		if (fifo_full) begin
			`VERIFY(fifo_ready, 1'b1);
			fifo_write_e = 1'b0;
			fifo_read_e = 1'b1;
			read_pending = 1'b1;
		end else begin
			fifo_read_e = 1'b0;

			write_data(fifo_data);
		end
	end

	@(negedge clk);
	if (read_pending) begin
		read_data(fifo_data, 1'b0);
		read_pending = 1'b0;
	end
	fifo_write_e = 1'b0;
	fifo_read_e = 1'b0;

	// Read until fifo is empty
	@(negedge clk);
	`VERIFY(fifo_ready, 1'b1);
	fifo_read_e = 1'b1;

	while (fifo_data.size() != 0) begin
		@(negedge clk);
			`VERIFY(fifo_ready, 1'b1);
			read_data(fifo_data, 1'b0);
	end

	// Cleanup
	read_pending = 1'b0;
	fifo_write_e = 1'b0;
	fifo_read_e = 1'b0;

endtask;

task concurrent_rw_cycle(integer words_no);
	integer i;
	queue_wrapper#(DATA_WIDTH) fifo_data;

	fifo_data = new();
	fifo_write_e = 1'b0;
	fifo_read_e = 1'b0;

	// Load 1 word into the FIFO to allow for concurrent r/w
	@(negedge clk);
	write_data(fifo_data);

	// Start concurrent r/w operations
	@(negedge clk);
	fifo_write_e = 1'b0;

	for (i=0 ;i < words_no; i=i+1) begin
		@(negedge clk);
		write_data(fifo_data);
		fifo_read_e = 1'b1;
		@(negedge clk);
                `VERIFY(fifo_ready, 1'b0);
		fifo_read_e = 1'b0;
		fifo_write_e = 1'b0;
		read_data(fifo_data, 1'b1);
	end

	// Clean fifo
	@(negedge clk);
	fifo_read_e = 1'b1;
	@(negedge clk);
	read_data(fifo_data, 1'b1);
	@(negedge clk);
	fifo_read_e = 1'b0;

        i = fifo_data.size();
	`VERIFY(i, 0);
endtask

endmodule
