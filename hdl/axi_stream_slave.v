// Generic AXI4-STREAM slave interface

// Generic AXI4-STREAM slave inteface implemented as a skid buffer.
//
// Received data is forwarded to a FIFO storage element. Synchronization with
// the FIFO is achieved through fifo_busy/fifo_wren pair.

module axi_stream_slave #(
	// Width of slave side bus
	parameter integer AXIS_TDATA_WIDTH = 32
)(
	input                                      clk,
	input                                      resetn,
	output reg                                 tready,
	input                                      tlast,
	input                                      tvalid,
	input [AXIS_TDATA_WIDTH - 1 : 0]           tdata,
	input [(AXIS_TDATA_WIDTH / 8) - 1 : 0]     tstrb,

	input                                      fifo_busy,
	output reg                                 fifo_wren,
	output reg [AXIS_TDATA_WIDTH - 1 : 0]      fifo_data,

	output reg                                 stream_tlast
);

localparam [1:0] IDLE = 2'b00;
localparam [1:0] BUSY = 2'b01;
localparam [1:0] FULL = 2'b10;

reg [AXIS_TDATA_WIDTH - 1 : 0] fifo_data_skidbuf;
reg stream_tlast_skidbuf;

reg [1:0] state;

wire insert, flow, fill, flush, remove;
wire fifo_transaction, axis_slave_transaction;

initial fifo_data_skidbuf = {AXIS_TDATA_WIDTH{1'b0}};
initial fifo_data = {AXIS_TDATA_WIDTH{1'b0}};
initial stream_tlast_skidbuf = 1'b0;
initial stream_tlast = 1'b0;
initial fifo_wren = 1'b0;
initial tready = 1'b0;

assign fifo_transaction = fifo_wren && !fifo_busy;
assign axis_slave_transaction = tvalid && tready;

assign insert = (state == IDLE) && axis_slave_transaction && !fifo_transaction;
assign flow = (state == BUSY) && axis_slave_transaction && fifo_transaction;
assign fill = (state == BUSY) && axis_slave_transaction && !fifo_transaction;
assign flush = (state == FULL) && !axis_slave_transaction && fifo_transaction;
assign remove = (state == BUSY) && !axis_slave_transaction && fifo_transaction;

// Data path
always @(posedge clk) begin
	if (!resetn) begin
		fifo_data_skidbuf <= {AXIS_TDATA_WIDTH{1'b0}};
		fifo_data <= {AXIS_TDATA_WIDTH{1'b0}};

		stream_tlast_skidbuf <= 1'b0;
		stream_tlast <= 1'b0;
	end else begin
		if (insert || flow) begin
			fifo_data <= tdata;
			stream_tlast <= tlast;
		end

		if (flush) begin
			fifo_data <= fifo_data_skidbuf;
			stream_tlast <= stream_tlast_skidbuf;
		end

		if (fill) begin
			fifo_data_skidbuf <= tdata;
			stream_tlast_skidbuf <= tlast;
		end
	end
end

// Control path
always @(posedge clk) begin
	if (!resetn) begin
		state <= IDLE;
	end else begin
		case (state)
		IDLE:
		begin
			if (insert)
				state <= BUSY;
		end
		BUSY:
		begin
			if (fill)
				state <= FULL;

			if (remove)
				state <= IDLE;

			if (flow)
				state <= BUSY;
		end
		FULL:
		begin
			if (flush)
				state <= BUSY;
		end
		endcase
	end
end

always @(posedge clk) begin
	if (!resetn) begin
		fifo_wren <= 1'b0;
	end else begin
		if (insert)
			fifo_wren <= 1'b1;

		if (remove)
			fifo_wren <= 1'b0;
	end
end

always @(posedge clk) begin
	if (!resetn) begin
		tready <= 1'b1;
	end else begin
		if (flush)
			tready <= 1'b1;

		if (fill)
			tready <= 1'b0;
	end
end

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

`endif

endmodule
