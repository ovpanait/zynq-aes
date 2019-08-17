`include "aes.vh"

module aes_axi_stream_master #
(
	// Width of master side bus
	parameter integer C_M_AXIS_TDATA_WIDTH = 32,

	parameter integer FIFO_SIZE = 16,
	parameter integer FIFO_ADDR_WIDTH = 4,
	parameter integer FIFO_DATA_WIDTH = 128
)
(
	/*
	* Master side ports
	*/
	input                   m00_axis_aclk,
	input                   m00_axis_aresetn,
	output                  m00_axis_tvalid,
	output  [C_M_AXIS_TDATA_WIDTH-1 : 0]      m00_axis_tdata,
	output  [(C_M_AXIS_TDATA_WIDTH/8)-1 : 0]  m00_axis_tstrb,
	output                  m00_axis_tlast,
	input                   m00_axis_tready,

	input                   master_send,
	input                   processing_done,
	input                   axis_slave_tlast_reg,

	input                        aes_controller_out_fifo_w_e,
	input  [FIFO_ADDR_WIDTH-1:0] aes_controller_out_fifo_addr,
	input  [FIFO_DATA_WIDTH-1:0] aes_controller_out_fifo_data,
	input [FIFO_ADDR_WIDTH-1:0]  aes_controller_out_fifo_blk_no,

	output reg                  axis_out_fifo_tx_done
);

/*
 * The output FIFO is implemented as 128-bit Block RAM:
 * - AES controller writes ciphertexts to it
 * - AXI master reads from it
 */

// SRAM signals
wire [FIFO_DATA_WIDTH-1:0] out_sram_o_data;
wire [FIFO_DATA_WIDTH-1:0] out_sram_i_data;
wire [FIFO_ADDR_WIDTH-1:0] out_sram_addr;
wire out_sram_w_e;
reg out_sram_r_e;

block_ram #(
	.ADDR_WIDTH(FIFO_ADDR_WIDTH),
	.DATA_WIDTH(FIFO_DATA_WIDTH),
	.DEPTH(FIFO_SIZE)
) out_fifo(
	.clk(m00_axis_aclk),

	.addr(out_sram_addr),
	.i_data(out_sram_i_data),
	.w_e(out_sram_w_e),

	.o_data(out_sram_o_data),
	.r_e(out_sram_r_e)
);

assign out_sram_w_e = aes_controller_out_fifo_w_e;
assign out_sram_addr = aes_controller_out_fifo_w_e ? aes_controller_out_fifo_addr : axis_out_fifo_blk_addr;
assign out_sram_i_data = aes_controller_out_fifo_data;

// AXI master implementation
/*
 * The AXI master control logic is:
 * - Read 1 x 128bit ciphertext from out_fifo
 * - Split it in 4 x 32bit words and push them on the AXI bus
 */

reg  axis_tvalid;
wire axis_tlast;

wire [FIFO_DATA_WIDTH-1:0] axis_out_fifo_blk_shift;
reg [FIFO_DATA_WIDTH-1:0]  axis_out_fifo_blk;
wire [FIFO_DATA_WIDTH-1:0] axis_out_fifo_blk_next;
reg [FIFO_ADDR_WIDTH-1:0]  axis_out_fifo_blk_cnt;
reg [FIFO_ADDR_WIDTH-1:0]  axis_out_fifo_blk_addr;
reg [FIFO_ADDR_WIDTH-1:0]  axis_out_fifo_word_cnt;
wire axis_out_fifo_addr_is_last;
wire axis_out_fifo_tx_en;
wire axis_out_fifo_last_blk;
wire axis_out_fifo_last_word;

assign axis_out_fifo_blk_next = out_sram_o_data;

assign m00_axis_tvalid = axis_tvalid;
assign m00_axis_tdata  = axis_out_fifo_blk_shift[FIFO_DATA_WIDTH-`WORD_S +: `WORD_S];
assign m00_axis_tlast  = axis_tlast;
assign m00_axis_tstrb  = {(C_M_AXIS_TDATA_WIDTH/8){1'b1}};

assign axis_out_fifo_blk_shift = axis_out_fifo_blk << axis_out_fifo_word_cnt * `WORD_S;
assign axis_out_fifo_last_blk = (axis_out_fifo_blk_cnt == aes_controller_out_fifo_blk_no - 1'b1);
assign axis_out_fifo_last_word = axis_out_fifo_last_blk && 
		(axis_out_fifo_word_cnt == `Nb - 1'b1);
assign axis_out_fifo_addr_is_last = (axis_out_fifo_blk_addr == aes_controller_out_fifo_blk_no - 1'b1);
assign axis_tlast =  axis_out_fifo_last_word && axis_slave_tlast_reg;
assign axis_out_fifo_tx_en = m00_axis_tready;

localparam AXIS_MASTER_IDLE = 2'b0,
	AXIS_MASTER_INIT_SRAM = 2'b1,
	AXIS_MASTER_INIT_TRANSFER = 2'b10,
	AXIS_MASTER_TRANSFER = 2'b11;

reg [0:1] axis_master_fsm_state;

always @(posedge m00_axis_aclk) begin
	if(!m00_axis_aresetn) begin
		axis_out_fifo_blk <= 1'b0;
		axis_out_fifo_blk_addr <= 1'b0;
		axis_out_fifo_word_cnt <= 1'b0;
		axis_out_fifo_blk_cnt <= 1'b0;
		axis_out_fifo_tx_done <= 1'b0;

		axis_tvalid <= 1'b0;
		axis_master_fsm_state <= AXIS_MASTER_IDLE;
	end 
	else begin
		out_sram_r_e <= 1'b0;
		axis_out_fifo_tx_done <= 1'b0;
		axis_tvalid <= 1'b0;

		case (axis_master_fsm_state)
		AXIS_MASTER_IDLE:
		begin
			axis_out_fifo_blk <= 1'b0;

			// start reading from SRAM before state is MASTER_SEND, while processing_done is active
			if ((master_send | processing_done) && !axis_out_fifo_tx_done) begin
				out_sram_r_e <= 1'b1;
				axis_master_fsm_state <= AXIS_MASTER_INIT_SRAM;
			end
		end
		AXIS_MASTER_INIT_SRAM:
		begin
			out_sram_r_e <= 1'b1;
			axis_master_fsm_state <= AXIS_MASTER_INIT_TRANSFER;
			axis_out_fifo_blk_addr <= 1'b0;
			axis_out_fifo_blk <= 1'b0;
		end
		AXIS_MASTER_INIT_TRANSFER:
		begin
			out_sram_r_e <= 1'b1;
			axis_out_fifo_blk <= axis_out_fifo_blk_next;
			axis_tvalid <= 1'b1;
			axis_out_fifo_blk_addr <= axis_out_fifo_blk_addr + 1'b1;

			axis_master_fsm_state <= AXIS_MASTER_TRANSFER;
		end
		AXIS_MASTER_TRANSFER:
		begin
			out_sram_r_e <= 1'b1;
			axis_tvalid <= 1'b1;

			if (axis_out_fifo_tx_en) begin
				axis_out_fifo_word_cnt <= axis_out_fifo_word_cnt + 1'b1;

				if (axis_out_fifo_word_cnt == `Nb - 1'b1) begin
					axis_out_fifo_blk <= axis_out_fifo_blk_next;
					axis_out_fifo_word_cnt <= 1'b0;
					axis_out_fifo_blk_cnt <= axis_out_fifo_blk_cnt + 1'b1;

					if (!axis_out_fifo_addr_is_last) begin
						axis_out_fifo_blk_addr <= axis_out_fifo_blk_addr + 1'b1;
					end
				end

				if (axis_out_fifo_last_word) begin
					// cleanup
					axis_out_fifo_blk_addr <= 1'b0;
					axis_out_fifo_blk_cnt <= 1'b0;
					axis_out_fifo_word_cnt <= 1'b0;
					axis_out_fifo_tx_done <= 1'b1;

					axis_tvalid <= 1'b0;
					axis_master_fsm_state <= AXIS_MASTER_IDLE;
				end
			end
		end
		endcase
	end
end
endmodule
