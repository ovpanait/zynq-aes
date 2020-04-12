/*
 * Generic Verilog module for Galois Field Multiplication.
 */
module gfm #(
	// GF(2^GFM_BITS) finite field
	parameter integer GFM_BITS = 128,

	// Latency in clock cycles for one multiplication
	parameter integer GFM_CYCLES = 8,

	/* The default polynomial for GHASH function of AES GCM mode is:
	 * x^128 + x^7 + x^2 + x + 1
	 * 1 0000 0000 ... 0000 1000 0111
	 * ^                            ^
	 * 128..........................0
	 *
	 * Reverse it to match LSB ----> MSB implementation.
	 */
	parameter reg [GFM_BITS-1:0] POLYNOMIAL = 'he1000000000000000000000000000000
)(
	input                      clk,
	input                      reset,
	input                      en,

	input [GFM_BITS-1:0]       a,
	input [GFM_BITS-1:0]       b,

	output reg [GFM_BITS-1:0]  result,
	output reg                 done
);

localparam ROUND_WIDTH = GFM_BITS;

integer i = 0;

reg compute;
reg [ROUND_WIDTH-1:0] round;

reg [GFM_BITS:0] op1;
reg [GFM_BITS:0] op2;
reg [GFM_BITS:0] op1_next;
reg [GFM_BITS:0] op2_next;
reg [GFM_BITS-1:0] result_next;

/*
 * The GCM standard treats blocks LSB ----> MSB, which is the
 * opposite of how we treat them in Verilog code (MSB <---- LSB).
 * In order to avoid unnecessary complications in other parts of the
 * algorithm, reverse the shifts and polynomial here and treat the
 * input blocks and result LSB ----> MSB.
 */
always @(*) begin
	result_next = result;
	op1_next = op1;
	op2_next = op2;

	for (i = 0; i < (GFM_BITS / GFM_CYCLES); i=i+1) begin
		result_next = result_next ^ (op2_next[GFM_BITS-1] ? op1_next : {GFM_BITS{1'b0}});
		op1_next = (op1_next >> 1) ^ (op1_next[0] ? POLYNOMIAL : {GFM_BITS{1'b0}});
		op2_next = op2_next << 1;
	end
end

always @(posedge clk) begin
	if (reset) begin
		done <= 1'b0;
		compute <= 1'b0;
		round <= {ROUND_WIDTH{1'b0}};
	end else begin
		done <= 1'b0;

		if (en) begin
			compute <= 1'b1;
			round <= {ROUND_WIDTH{1'b0}};
		end

		if (compute) begin
			round <= round + 'h1;

			if (round == GFM_CYCLES-1) begin
				done <= 1'b1;
				compute <= 1'b0;
			end
		end

	end
end

always @(posedge clk) begin
	if (reset) begin
		op1 <= {GFM_BITS{1'b0}};
		op2 <= {GFM_BITS{1'b0}};
		result <= {GFM_BITS{1'b0}};
	end else begin
		if (en) begin
			op2 <= b;
			op1 <= a;
			result <= {GFM_BITS{1'b0}};
		end

		if (compute) begin
			op1 <= op1_next;
			op2 <= op2_next;
			result <= result_next;
		end
	end
end

endmodule

