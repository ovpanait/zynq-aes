module aes_axi_stream_slave #(
	// Width of slave side bus
	parameter integer C_S_AXIS_TDATA_WIDTH = 32,

	parameter integer FIFO_SIZE = 16,
	parameter integer FIFO_ADDR_WIDTH = 4,
	parameter integer FIFO_DATA_WIDTH = 128
)(
	/*
	* Slave side ports
	*/

	input   s00_axis_aclk,
	input   s00_axis_aresetn,
	output  s00_axis_tready,
	input   s00_axis_tlast,
	input   s00_axis_tvalid,
	input [C_S_AXIS_TDATA_WIDTH-1 : 0]      s00_axis_tdata,
	input [(C_S_AXIS_TDATA_WIDTH/8)-1 : 0]  s00_axis_tstrb,

	input                       processing_done,
	input                       axis_out_fifo_tx_done,
	input                       aes_controller_in_fifo_r_e,
	input [FIFO_ADDR_WIDTH-1:0] aes_controller_in_fifo_addr,

	output reg [`WORD_S-1:0]     axis_slave_in_fifo_cmd,
	output reg                   axis_slave_is_new_cmd,
	output reg                   axis_slave_in_fifo_writes_done,
	output reg                   axis_slave_tlast_reg,

	output reg [FIFO_ADDR_WIDTH-1:0]  axis_blk_cnt,
	output [FIFO_DATA_WIDTH-1:0]      in_sram_o_data,
	output                            start_processing,

	input slave_write_fifo
);

/*
 * The input FIFO is implemented as 128-bit Block RAM:
 * - AXI slave logic writes to it
 * - AES controller reads from it
 */

// AXI related signals
wire     axis_tready;
wire     fifo_wren;

reg [FIFO_ADDR_WIDTH-1:0] axis_slave_in_fifo_addr_reg;
reg [FIFO_DATA_WIDTH-1:0] axis_slave_in_fifo_blk;     // input FIFO block
reg [FIFO_ADDR_WIDTH-1:0] axis_slave_in_fifo_blk_cnt; // number of 128-bit blocks in the input FIFO

reg [1:0]         axis_slave_in_fifo_word_cnt;
reg               axis_slave_in_fifo_w_e;
wire              axis_slave_in_fifo_addr_is_last;
reg               axis_slave_fsm_state;


// SRAM signals
wire [FIFO_DATA_WIDTH-1:0] in_sram_i_data;
wire [FIFO_ADDR_WIDTH-1:0] in_sram_addr;
wire in_sram_w_e;
wire in_sram_r_e;

assign in_sram_r_e = aes_controller_in_fifo_r_e;
assign in_sram_addr = aes_controller_in_fifo_r_e ? aes_controller_in_fifo_addr : axis_slave_in_fifo_addr_reg;

block_ram #(
	.ADDR_WIDTH(FIFO_ADDR_WIDTH),
	.DATA_WIDTH(FIFO_DATA_WIDTH),
	.DEPTH(FIFO_SIZE)
) in_fifo(
	.clk(s00_axis_aclk),

	.addr(in_sram_addr),
	.i_data(in_sram_i_data),
	.w_e(in_sram_w_e),

	.o_data(in_sram_o_data),
	.r_e(in_sram_r_e)
);

// AXI slave implementation
/*
 * The AXI slave control logic is:
 * - Take 4 x 32bit words from the AXI bus and fill the axis_slave_in_fifo_blk variable
 * - Store axis_slave_in_fifo_blk as 1 x 128bit word in the in_fifo_sram block RAM
 *       so it can be retrieved later by the AES controller
 */
localparam AXIS_SLAVE_GET_CMD = 1'b0;
localparam AXIS_SLAVE_GET_PAYLOAD = 1'b1;

assign in_sram_i_data = axis_slave_in_fifo_blk;
assign in_sram_w_e = axis_slave_in_fifo_w_e;

assign s00_axis_tready = axis_tready;
assign axis_tready = (slave_write_fifo && !axis_slave_in_fifo_writes_done);
assign fifo_wren = s00_axis_tvalid && axis_tready;
assign axis_slave_in_fifo_addr_is_last = (axis_slave_in_fifo_addr_reg == FIFO_SIZE-1);

always @(posedge s00_axis_aclk) begin
	if(!s00_axis_aresetn) begin
		axis_slave_in_fifo_blk <= 1'b0;
		axis_slave_in_fifo_blk_cnt <= 1'b0;
		axis_slave_in_fifo_w_e <= 1'b0;
		axis_slave_in_fifo_word_cnt <= 1'b0;
		axis_slave_in_fifo_writes_done <= 1'b0;
		axis_slave_in_fifo_cmd <= 1'b0;
		axis_slave_in_fifo_addr_reg <= 1'b0;
		axis_slave_tlast_reg <= 1'b0;
		axis_slave_is_new_cmd <= 1'b0;

		axis_blk_cnt <= 1'b0;
		axis_slave_fsm_state <= AXIS_SLAVE_GET_CMD;
	end
	else begin
		case (axis_slave_fsm_state)
			AXIS_SLAVE_GET_CMD:
			begin
				axis_slave_in_fifo_addr_reg <= 1'b0;
				axis_slave_is_new_cmd <= 1'b1;

				if (axis_out_fifo_tx_done) begin
					axis_slave_tlast_reg <= 1'b0;
				end

				if (fifo_wren) begin
					//first received word is the command
					axis_slave_in_fifo_cmd <= s00_axis_tdata;
					axis_slave_fsm_state <= AXIS_SLAVE_GET_PAYLOAD;
				end
			end
			AXIS_SLAVE_GET_PAYLOAD:
			begin
				axis_slave_in_fifo_w_e <= 1'b0;

				if (fifo_wren) begin
					axis_slave_in_fifo_blk <= (axis_slave_in_fifo_blk << `WORD_S) | s00_axis_tdata;
					axis_slave_in_fifo_word_cnt <= axis_slave_in_fifo_word_cnt + 1'b1;

					if (axis_slave_in_fifo_word_cnt == `Nb - 1'b1) begin
						axis_slave_in_fifo_blk_cnt <= axis_slave_in_fifo_blk_cnt + 1'b1;
						axis_slave_in_fifo_w_e <= 1'b1;
						axis_slave_in_fifo_word_cnt <= 1'b0;

						if (!axis_slave_in_fifo_addr_is_last) begin
							axis_slave_in_fifo_addr_reg <= axis_slave_in_fifo_blk_cnt;
						end

						if (s00_axis_tlast) begin
						       axis_slave_tlast_reg <= 1'b1;
						end

						/*
						 * Use the two slots available for key/iv to store data if the payload is
						 * larger than DATA_FIFO_SIZE.
						 */
						if ((axis_slave_in_fifo_blk_cnt == FIFO_SIZE-1) || s00_axis_tlast) begin
							axis_slave_in_fifo_blk_cnt <= 1'b0;
							axis_blk_cnt <= axis_slave_in_fifo_blk_cnt + 1'b1;
							axis_slave_in_fifo_writes_done <= 1'b1;
						end
					end
				end

				if (processing_done) begin
					axis_slave_in_fifo_addr_reg <= 1'b0;
					axis_slave_in_fifo_writes_done <= 1'b0;
					axis_slave_is_new_cmd <= 1'b0;

					if (axis_slave_tlast_reg) begin
						axis_slave_fsm_state <= AXIS_SLAVE_GET_CMD;
					end
				end
			end
		endcase
	end
end

// One clock enable
assign start_processing = (slave_write_fifo && axis_slave_in_fifo_writes_done == 1'b1 && !processing_done);

endmodule
