// Generic AXI4-STREAM master interface

// Generic AXI4-STREAM master inteface implemented as a skid buffer.
//
// Data is received from a fifo storage element and pushed on the axi bus.
// Synchronization with the fifo is achieved through the
// fifo_tvalid/fifo_tready pair.
//
// All outputs are registered.

module axi_stream_master #(
	// Width of slave side bus
	parameter integer AXIS_TDATA_WIDTH = 32
)(
	input                                      clk,
	input                                      resetn,

	output reg                                 fifo_tready,
	input                                      fifo_tvalid,
	input                                      fifo_tlast,
	input [AXIS_TDATA_WIDTH-1:0]               fifo_tdata,

	input                                      tready,
	output reg                                 tlast,
	output reg                                 tvalid,
	output reg [AXIS_TDATA_WIDTH/8-1:0]        tstrb,
	output reg [AXIS_TDATA_WIDTH - 1 : 0]      tdata
);

localparam [1:0] IDLE = 2'b00;
localparam [1:0] BUSY = 2'b01;
localparam [1:0] FULL = 2'b10;

reg [AXIS_TDATA_WIDTH - 1 : 0] tdata_skidbuf;
reg tlast_skidbuf;

reg [1:0] state;

wire insert, flow, fill, flush, remove;
wire fifo_transaction, out_transaction;

initial tdata_skidbuf = {AXIS_TDATA_WIDTH{1'b0}};
initial tdata = {AXIS_TDATA_WIDTH{1'b0}};
initial tlast_skidbuf = 1'b0;
initial fifo_tready = 1'b0;
initial tlast = 1'b0;
initial tvalid = 1'b0;

assign fifo_transaction = fifo_tready && fifo_tvalid;
assign out_transaction = tvalid && tready;

assign insert = (state == IDLE) && fifo_transaction && !out_transaction;
assign flow = (state == BUSY) && fifo_transaction && out_transaction;
assign fill = (state == BUSY) && fifo_transaction && !out_transaction;
assign flush = (state == FULL) && !fifo_transaction && out_transaction;
assign remove = (state == BUSY) && !fifo_transaction && out_transaction;

// Data path
always @(posedge clk) begin
	if (!resetn) begin
		tdata_skidbuf <= {AXIS_TDATA_WIDTH{1'b0}};
		tdata <= {AXIS_TDATA_WIDTH{1'b0}};

		tlast_skidbuf <= 1'b0;
		tlast <= 1'b0;
	end else begin
		if (insert || flow) begin
			tdata <= fifo_tdata;
			tlast <= fifo_tlast;
		end

		if (flush) begin
			tdata <= tdata_skidbuf;
			tlast <= tlast_skidbuf;
		end

		if (fill) begin
			tdata_skidbuf <= fifo_tdata;
			tlast_skidbuf <= fifo_tlast;
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
		default:
			state <= IDLE;
		endcase
	end
end

always @(posedge clk) begin
	if (!resetn) begin
		tvalid <= 1'b0;
	end else begin
		if (insert)
			tvalid <= 1'b1;

		if (remove)
			tvalid <= 1'b0;
	end
end

always @(posedge clk) begin
	if (!resetn) begin
		fifo_tready <= 1'b1;
	end else begin
		if (flush)
			fifo_tready <= 1'b1;

		if (fill)
			fifo_tready <= 1'b0;
	end
end

always @(posedge clk) begin
	tstrb  <= {(AXIS_TDATA_WIDTH/8){1'b1}};
end

`ifdef FORMAL

`ifdef AXI_STREAM_MASTER_FORMAL
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
	end else
		`ASSUME(!resetn);
end

// Master interface
always @(posedge clk) begin
	if (f_past_valid) begin
		// only deassert "tlast" after a successful transfer
		if ($fell(tlast)) begin
			assert($past(tvalid && tready));
		end

		// (?) assert "tlast" at the same time as "valid"
		if ($rose(tlast)) begin
			assert($rose(tvalid));
		end

		// data must be stable while "valid" is active
		if ($past(tvalid && !tready)) begin
			assert($stable(tdata));
		end
	end
end

// Slave interface
always @(posedge clk) begin
	if (f_past_valid) begin
		// only deassert "valid" after successful transfer
		if ($fell(fifo_tvalid)) begin
			`ASSUME($past(fifo_tready));
		end

		// only deassert "tlast" after a successful transfer
		if ($fell(fifo_tlast)) begin
			`ASSUME($past(fifo_tvalid && fifo_tready));
		end

		// (?) assert "tlast" at the same time as "valid"
		if ($rose(fifo_tlast)) begin
			`ASSUME($rose(fifo_tvalid));
		end

		// data must be stable while "valid" is active
		if ($past(fifo_tvalid && !fifo_tready)) begin
			`ASSUME($stable(fifo_tdata));
		end

		// only deassert "ready" after a successful transfer
		if ($fell(fifo_tready)) begin
			assert($past(fifo_tvalid));
		end
	end
end


`endif

endmodule
