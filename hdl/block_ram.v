module block_ram #(
	parameter integer ADDR_WIDTH = 9,
	parameter integer DATA_WIDTH = 128,
	parameter integer DEPTH = 512          // 8192 bytes
)(
	input                       clk,

	input [DATA_WIDTH-1:0]      i_data,
	input [ADDR_WIDTH-1:0]      addr,
	input                       w_e,

	output reg [DATA_WIDTH-1:0] o_data
);

reg [DATA_WIDTH-1:0] sram [0:DEPTH-1];

always @ (posedge clk) begin
	o_data <= sram[addr];

	if (w_e)
		sram[addr] <= i_data;
end
endmodule
