module block_ram #(
	parameter integer ADDR_WIDTH = 2,
	parameter integer DATA_WIDTH = 128
)(
	input                       w_clk,
	input                       r_clk,

	// Read port
	input [ADDR_WIDTH-1:0]      r_addr,
	output reg [DATA_WIDTH-1:0] r_data,

	// Write port
	input                       w_e,
	input [ADDR_WIDTH-1:0]      w_addr,
	input [DATA_WIDTH-1:0]      w_data
);

localparam integer DEPTH = (1'b1 << ADDR_WIDTH);

reg [DATA_WIDTH-1:0] mem[0:DEPTH-1];

always @(posedge r_clk) begin
	r_data <= mem[r_addr];
end

always @(posedge w_clk) begin
	if (w_e)
		mem[w_addr] <= w_data;
end


// TODO
// Couldn't get these properties adapted to dual clocks to pass induction
// Need to put more thoght into this
`ifdef FORMAL_DUMB

`ifdef BRAM_FORMAL
`define ASSUME assume
`else
`define ASSUME assert
`endif

integer f_i;
reg f_past_valid;

initial r_data = {DATA_WIDTH{1'b0}};
initial f_past_valid = 1'b0;
initial f_i = 0;

initial begin
	for (f_i = 0; f_i < DEPTH; f_i++)
		mem[f_i] = {DATA_WIDTH{1'b0}};
end

always @(posedge clk)
	f_past_valid <= 1'b1;

always @(posedge clk) begin
	if (f_past_valid) begin
		assert(r_data == $past(mem[r_addr]));

		if ($past(w_e)) begin
			assert(mem[$past(w_addr)] == $past(w_data));
		end
	end
end

`endif

endmodule
