// AXI slave implementation

`include "aes.vh"

module axi_stream_slave_tb #(
	// Width of slave side bus
	parameter integer C_S_AXIS_TDATA_WIDTH = 32,
	parameter integer FIFO_SIZE = 2048
)(
	/*
	* Slave side ports
	*/

	input                                   s00_axis_aclk,
	input                                   s00_axis_aresetn,
	output                                  s00_axis_tready,
	input                                   s00_axis_tlast,
	input                                   s00_axis_tvalid,
	input [C_S_AXIS_TDATA_WIDTH-1 : 0]      s00_axis_tdata,
	input [(C_S_AXIS_TDATA_WIDTH/8)-1 : 0]  s00_axis_tstrb
);

localparam TREADY_DELAY = 16;

// AXI related signals
wire axis_data_available;
reg  [31:0] tready_cnt;
reg  axis_tready;

// FIFO signals
reg fifo_read_req;

// Queue
reg [31 + 1:0] arr[FIFO_SIZE];
int arr_size = 0;
int head_ptr = 0;

always @(posedge s00_axis_aclk) begin
	if (fifo_wren) begin
		if (s00_axis_tlast !== arr[head_ptr][32]) begin
			$display("TLAST wrong!");
			$display("Word no.       : %0d", head_ptr);
			$display("Simulated value: %H", s00_axis_tlast);
			$display("Expected value : %H", arr[head_ptr][32]);
			$finish;
		end

		if (s00_axis_tdata !== arr[head_ptr][31:0]) begin
			$display("Data mismatch!");
			$display("Word no. %d", head_ptr);
			$display("Simulated value: %H", s00_axis_tdata);
			$display("Expected value:  %H", arr[head_ptr]);
			$finish;
		end

		head_ptr++;
	end
end

// AXI logic
initial begin
	tready_cnt = 32'b0;
	axis_tready = 1'b0;
end

always @(posedge s00_axis_aclk) begin
	tready_cnt <= tready_cnt + 1'b1;
	axis_tready <= 1'b0;

	if (tready_cnt == TREADY_DELAY - 1) begin
		axis_tready <= 1'b1;
		tready_cnt <= 1'b0;
	end
end

assign axis_data_available = s00_axis_tvalid && axis_tready;
assign fifo_wren = axis_data_available;
assign s00_axis_tready = axis_tready;

endmodule
