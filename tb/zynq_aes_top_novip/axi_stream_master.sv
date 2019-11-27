// AXI master implementation

`include "aes.vh"
`include "queue_wrapper.vh"

module axi_stream_master #
(
	// Width of master side bus
	parameter integer C_M_AXIS_TDATA_WIDTH = 32,
	parameter integer FIFO_SIZE = 2048
)(
	/*
	* Master side ports
	*/
	input                                     m00_axis_aclk,
	input                                     m00_axis_aresetn,
	output                                    m00_axis_tvalid,
	output  [C_M_AXIS_TDATA_WIDTH-1 : 0]      m00_axis_tdata,
	output  [(C_M_AXIS_TDATA_WIDTH/8)-1 : 0]  m00_axis_tstrb,
	output                                    m00_axis_tlast,
	input                                     m00_axis_tready
);

reg [31:0] fifo_data;
reg fifo_empty;
reg fifo_read_req;

// AXI signals

wire axis_transaction;
wire axis_last_word;
reg  axis_tvalid;
wire axis_tlast;

// Queue
reg [31:0] arr[FIFO_SIZE];
int arr_size = 0;
int head_ptr = 0;

always @(*) begin
	fifo_empty = (head_ptr == arr_size);
	fifo_data = arr[head_ptr];
	fifo_read_req = !fifo_empty && !axis_tvalid;
end

always @(posedge m00_axis_aclk) begin
	if (m00_axis_tvalid && m00_axis_tready) begin
		head_ptr++;
	end
end

// AXI logic

assign m00_axis_tdata  = fifo_data;
assign m00_axis_tstrb  = {(C_M_AXIS_TDATA_WIDTH/8){1'b1}};
assign m00_axis_tvalid = axis_tvalid;
assign m00_axis_tlast  = axis_tlast;

assign axis_transaction = m00_axis_tready && axis_tvalid;
assign axis_tlast = (head_ptr == arr_size - 1);

always @(posedge m00_axis_aclk) begin
	if(!m00_axis_aresetn) begin
		axis_tvalid <= 1'b0;
	end 
	else begin
		if (fifo_read_req) begin
			axis_tvalid <= 1'b1;
		end

		if (axis_transaction) begin
			axis_tvalid <= 1'b0;
		end
	end
end

endmodule
