`timescale 1ns/1ns
`define PERIOD 10

module tb_main();

`include "test_fc.vh"
`include "queue_wrapper.vh"

localparam ADDR_WIDTH = 2;
localparam DATA_WIDTH = 128;

integer errors;

reg clk;
reg reset;

reg fifo_write_tvalid;
wire fifo_read_tready;

reg [DATA_WIDTH-1:0] fifo_wdata;
wire [DATA_WIDTH-1:0] fifo_rdata;

wire fifo_write_tready;
wire fifo_read_tvalid;

integer words_no = 11000;

integer words_remaining = words_no;
integer words_read = 0;

bit read_pending;
bit read_allowed;

queue_wrapper#(DATA_WIDTH) fifo_data;

fifo #(
	.ADDR_WIDTH(ADDR_WIDTH),
	.DATA_WIDTH(DATA_WIDTH)
) DUT (
	.clk(clk),
	.reset(reset),

	.fifo_write_tvalid(fifo_write_tvalid),
	.fifo_write_tready(fifo_write_tready),
	.fifo_wdata(fifo_wdata),

	.fifo_read_tready(fifo_read_tready),
	.fifo_read_tvalid(fifo_read_tvalid),
	.fifo_rdata(fifo_rdata)
);

initial begin
	$dumpfile("fifo.vcd");
	$dumpvars(1, DUT);
end

initial begin
	fifo_data = new();

	clk <= 0;
	forever #(`PERIOD) clk = ~clk;
end

initial begin
	@(posedge clk); //may need several cycles for reset
	@(negedge clk) reset = 1;

	@(posedge clk);
	@(negedge clk) reset = 0;
end

task write_data(input queue_wrapper#(DATA_WIDTH) fifo_data);
		std::randomize(fifo_wdata);
		fifo_data.push_back(fifo_wdata);
endtask

task read_data(input queue_wrapper#(DATA_WIDTH) fifo_data);
	reg [DATA_WIDTH-1:0] data;

	data = fifo_data.pop_front();
	`VERIFY(fifo_rdata, data);
endtask

always @(posedge clk) begin
	if (reset) begin
		fifo_write_tvalid <= 1'b0;
	end else begin
		if (!fifo_write_tvalid && words_no) begin
			fifo_write_tvalid <= 1'b1;
			write_data(fifo_data);
		end

		if (fifo_write_tvalid && fifo_write_tready) begin
			words_remaining <= words_remaining + 1;
			fifo_write_tvalid <= 1'b0;
		end
	end
end

assign fifo_read_tready = fifo_read_tvalid && read_allowed;

always @(posedge clk) begin
	if (fifo_read_tvalid && fifo_read_tready) begin
		read_data(fifo_data);
		words_read <= words_read + 1;
	end
end

always @(posedge clk) begin
	std::randomize(read_allowed);

	if (words_read == words_no) begin
		$display("PASS!");
		$finish;
	end
end

endmodule
