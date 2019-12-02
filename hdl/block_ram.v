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

`ifdef FORMAL

`ifdef BRAM_FORMAL
`define ASSUME assume
`else
`define ASSUME assert
`endif

integer f_i;
reg f_past_valid;

initial o_data = {DATA_WIDTH{1'b0}};
initial f_past_valid = 1'b0;
initial f_i = 0;

initial begin
	for (f_i = 0; f_i < DEPTH; f_i++)
		sram[f_i] = {DATA_WIDTH{1'b0}};
end

always @(posedge clk)
	f_past_valid <= 1'b1;

always @(posedge clk) begin
	if (f_past_valid) begin
		assert(o_data == $past(sram[addr]));

		if ($past(w_e)) begin
			assert(sram[$past(addr)] == $past(i_data));
		end
	end
end

`endif

endmodule
