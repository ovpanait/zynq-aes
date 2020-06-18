`define W_PERIOD 10
`define R_PERIOD 5

module tb_main();

`include "test_fc.vh"
`include "queue_wrapper.vh"

localparam ADDR_WIDTH = 2;
localparam DATA_WIDTH = 128;

reg r_clk;
reg w_clk;

reg r_reset;
reg w_reset;

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

async_fifo #(
	.ADDR_WIDTH(ADDR_WIDTH),
	.DATA_WIDTH(DATA_WIDTH)
) DUT (
	.r_clk(r_clk),
	.w_clk(w_clk),

	.r_reset(r_reset),
	.w_reset(w_reset),

	.write_tvalid(fifo_write_tvalid),
	.write_tready(fifo_write_tready),
	.write_data(fifo_wdata),

	.read_tready(fifo_read_tready),
	.read_tvalid(fifo_read_tvalid),
	.read_data(fifo_rdata)
);

initial begin
	$dumpfile("fifo.vcd");
	$dumpvars(1, DUT);

	fifo_data = new();
end

initial begin

	r_clk = 0;

	forever #(`R_PERIOD) r_clk = ~r_clk;
end

initial begin
	w_clk = 0;

	forever #(`W_PERIOD) w_clk = ~w_clk;
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

// Write side
initial begin
	@(posedge w_clk);
	@(negedge w_clk) w_reset = 1;

	@(posedge w_clk);
	@(negedge w_clk) w_reset = 0;
end

always @(posedge w_clk) begin
	if (w_reset) begin
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

// Read side
initial begin
	@(posedge r_clk);
	@(negedge r_clk) r_reset = 1;

	@(posedge r_clk);
	@(negedge r_clk) r_reset = 0;
end

assign fifo_read_tready = fifo_read_tvalid && read_allowed;

always @(posedge r_clk) begin
	if (fifo_read_tvalid && fifo_read_tready) begin
		read_data(fifo_data);
		words_read <= words_read + 1;
	end
end

always @(posedge r_clk) begin
	std::randomize(read_allowed);

	if (words_read == words_no) begin
		$display("PASS!");
		$finish;
	end
end

endmodule
