// Generic AXI4-STREAM slave interface

// Received data is forwarded to a FIFO storage element. Synchronization with
// the FIFO is achieved through fifo_busy/fifo_wren pair.

module axi_stream_slave #(
	// Width of slave side bus
	parameter integer C_S_AXIS_TDATA_WIDTH = 32
)(
	input                                      clk,
	input                                      resetn,
	output                                     tready,
	input                                      tlast,
	input                                      tvalid,
	input [C_S_AXIS_TDATA_WIDTH - 1 : 0]       tdata,
	input [(C_S_AXIS_TDATA_WIDTH / 8) - 1 : 0] tstrb,

	input                                      fifo_busy,
	output                                     fifo_wren,
	output [C_S_AXIS_TDATA_WIDTH - 1 : 0]      fifo_data,

	output                                     stream_tlast
);

assign tready = tvalid && !fifo_busy;

assign fifo_wren = tvalid && tready;
assign fifo_data = tdata;
assign stream_tlast = tlast;

`ifdef FORMAL

`ifdef AXI_STREAM_SLAVE_FORMAL
`define ASSUME assume
`else
`define ASSUME assert
`endif

reg f_past_valid = 1'b0;

initial f_past_valid = 1'b0;

always @(posedge clk)
	f_past_valid <= 1'b1;

always @(*) begin
	if (!f_past_valid) begin
		`ASSUME(resetn);
	end
end

always @(posedge clk) begin
	if (f_past_valid) begin
		// only deassert "valid" after successful transfer
		if ($fell(tvalid)) begin
			`ASSUME($past(tready));
		end

		// only deassert "tlast" after a successful transfer
		if ($fell(tlast)) begin
			`ASSUME($past(tvalid && tready));
		end

		// (?) assert "tlast" at the same time as "valid"
		if ($rose(tlast)) begin
			`ASSUME($rose(tvalid));
		end

		// data must be stable while "valid" is active
		if ($past(tvalid && !tready)) begin
			`ASSUME($stable(tdata));
		end

		// only deassert "ready" after a successful transfer
		if ($fell(tready)) begin
			assert($past(tvalid));
		end
	end
end

always @(*) begin
	assert(fifo_wren == (tvalid && tready));
	assert(fifo_data == tdata);
	assert(stream_tlast == tlast);

	if (fifo_busy)
		assert(!tready);
end

`endif

endmodule
