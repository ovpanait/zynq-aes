`include "aes.vh"

module aes_axi_stream #
(
        /*
        * Master side parameters
        */
        // Width of master side bus
        parameter integer C_M_AXIS_TDATA_WIDTH = 32,

        /*
        * Slave side parameters
        */
        // Width of slave side bus
        parameter integer C_S_AXIS_TDATA_WIDTH = 32,

        /*
         * Max no. of 32-bit words of payload data,
         * that can be processed in one go.
         * 32 kB by default.
         * Must be a multiple of the AES block size (128 bits).
         */
        parameter integer DATA_FIFO_SIZE = 2048
)
(
        /*
        * Master side ports
        */

        input wire                                   m00_axis_aclk,
        input wire                                   m00_axis_aresetn,
        output wire                                  m00_axis_tvalid,
        output wire [C_M_AXIS_TDATA_WIDTH-1 : 0]     m00_axis_tdata,
        output wire [(C_M_AXIS_TDATA_WIDTH/8)-1 : 0] m00_axis_tstrb,
        output wire                                  m00_axis_tlast,
        input wire                                   m00_axis_tready,

        /*
        * Slave side ports
        */

        input wire                                   s00_axis_aclk,
        input wire                                   s00_axis_aresetn,
        output wire                                  s00_axis_tready,
        input wire [C_S_AXIS_TDATA_WIDTH-1 : 0]      s00_axis_tdata,
        input wire [(C_S_AXIS_TDATA_WIDTH/8)-1 : 0]  s00_axis_tstrb,
        input wire                                   s00_axis_tlast,
        input wire                                   s00_axis_tvalid
);

// function called clogb2 that returns an integer which has the
// value of the ceiling of the log base 2.
function integer clogb2 (input integer bit_depth);
        begin
                for(clogb2=0; bit_depth>0; clogb2=clogb2+1)
                        bit_depth = bit_depth >> 1;
        end
endfunction

// Control state machine states
parameter [1:0] IDLE = 1'b0, // Initial/idle state

WRITE_FIFO  = 1'b1, // Input FIFO is written with the input stream data S_AXIS_TDATA

PROCESS_STUFF = 2'b11, // Data is being processed and placed into the output FIFO

MASTER_SEND = 2'b10; // Master is sending processed data

/*
 * 32kB AES block + 2 x 128-bit slots for key and iv.
 * When the payload is larger than DATA_FIFO_SIZE, the two slots will be used to
 * store additional data if necessary.
 */
localparam FIFO_DEPTH = DATA_FIFO_SIZE + (`KEY_S + `IV_BITS) / IN_SRAM_DATA_WIDTH;

localparam OUT_SRAM_DATA_WIDTH = `Nb * `WORD_S;
localparam OUT_SRAM_DEPTH = FIFO_DEPTH;
localparam OUT_SRAM_ADDR_WIDTH = clogb2(OUT_SRAM_DEPTH);

localparam IN_SRAM_DATA_WIDTH = `Nb * `WORD_S;
localparam IN_SRAM_DEPTH = FIFO_DEPTH;
localparam IN_SRAM_ADDR_WIDTH = clogb2(IN_SRAM_DEPTH);

// AXI slave signals
wire slave_write_fifo;
wire start_processing;

wire [`WORD_S-1:0] axis_slave_in_fifo_cmd;
wire               axis_slave_tlast_reg;
wire               axis_slave_in_fifo_writes_done;
wire               axis_slave_is_new_cmd;

wire [IN_SRAM_ADDR_WIDTH-1:0] axis_blk_cnt;
wire [IN_SRAM_DATA_WIDTH-1:0] in_sram_o_data;

// input FIFO signals
wire                          aes_controller_in_fifo_r_e;
wire [IN_SRAM_ADDR_WIDTH-1:0] aes_controller_in_fifo_addr;
wire [IN_SRAM_DATA_WIDTH-1:0] aes_controller_in_fifo_data;
wire [IN_SRAM_ADDR_WIDTH-1:0] aes_controller_in_fifo_blk_cnt;

// aes signals
wire               aes_controller_done;
wire               aes_controller_start;
wire [0:`WORD_S-1] aes_controller_cmd;
wire               aes_controller_skip_key_expansion;
reg                processing_done;
// output FIFO signals
wire                           aes_controller_out_fifo_w_e;
wire [OUT_SRAM_ADDR_WIDTH-1:0] aes_controller_out_fifo_addr;
wire [OUT_SRAM_DATA_WIDTH-1:0] aes_controller_out_fifo_data;
wire [OUT_SRAM_ADDR_WIDTH-1:0] aes_controller_out_fifo_blk_no;

// AXI master signals
wire master_send;
wire [OUT_SRAM_ADDR_WIDTH-1:0] axis_out_fifo_blk_no;
wire                           axis_out_fifo_tx_done;

// Control state machine implementation
reg [1:0]                        state;

// =====================================================================

always @(posedge s00_axis_aclk)
begin
        if (!s00_axis_aresetn) begin
                state <= IDLE;
        end 
        else begin
                case (state)
                        IDLE:
                        if (s00_axis_tvalid) begin
                                state <= WRITE_FIFO;
                        end
                        else begin
                                state <= IDLE;
                        end
                        WRITE_FIFO:
                        if (axis_slave_in_fifo_writes_done) begin
                                state <= PROCESS_STUFF;
                        end
                        else begin
                                state <= WRITE_FIFO;
                        end
                        PROCESS_STUFF:
                        if (processing_done) begin
                                state <= MASTER_SEND;
                        end
                        else begin
                                state <= PROCESS_STUFF;
                        end
                        MASTER_SEND:
                        if (axis_out_fifo_tx_done) begin
                                state <= IDLE;
                        end
                        else begin
                                state <= MASTER_SEND;
                        end
                endcase
        end     
end

// =====================================================================
/*
* AXI slave
*/

assign slave_write_fifo = (state == WRITE_FIFO);

aes_axi_stream_slave #(
	.C_S_AXIS_TDATA_WIDTH(C_S_AXIS_TDATA_WIDTH),
	.FIFO_SIZE(OUT_SRAM_DEPTH),
	.FIFO_ADDR_WIDTH(OUT_SRAM_ADDR_WIDTH),
	.FIFO_DATA_WIDTH(OUT_SRAM_DATA_WIDTH)
) axi_stream_slave_controller (
	.s00_axis_aclk(s00_axis_aclk),
	.s00_axis_aresetn(s00_axis_aresetn),
	.s00_axis_tready(s00_axis_tready),
	.s00_axis_tlast(s00_axis_tlast),
	.s00_axis_tvalid(s00_axis_tvalid),
	.s00_axis_tdata(s00_axis_tdata),
	.s00_axis_tstrb(s00_axis_tstrb),

	.processing_done(processing_done),
	.axis_out_fifo_tx_done(axis_out_fifo_tx_done),
	.aes_controller_in_fifo_r_e(aes_controller_in_fifo_r_e),
	.aes_controller_in_fifo_addr(aes_controller_in_fifo_addr),

	.axis_slave_in_fifo_cmd(axis_slave_in_fifo_cmd),
	.axis_slave_is_new_cmd(axis_slave_is_new_cmd),
	.axis_slave_in_fifo_writes_done(axis_slave_in_fifo_writes_done),
	.axis_slave_tlast_reg(axis_slave_tlast_reg),
	.axis_blk_cnt(axis_blk_cnt),

	.in_sram_o_data(in_sram_o_data),
	.start_processing(start_processing),

	.slave_write_fifo(slave_write_fifo)
);

// =====================================================================
/*
* AES specific stuff
*/
assign aes_controller_cmd = axis_slave_in_fifo_cmd;
assign aes_controller_skip_key_expansion = !axis_slave_is_new_cmd;

assign aes_controller_in_fifo_data = in_sram_o_data;
assign aes_controller_in_fifo_blk_cnt = axis_blk_cnt;

/*
* Delay processing module "done" strobe by one clock to match fsm implementation
*/
assign __processing_done = aes_controller_done;
assign aes_controller_start = start_processing;

aes_controller #(
        .IN_FIFO_ADDR_WIDTH(IN_SRAM_ADDR_WIDTH),
        .IN_FIFO_DATA_WIDTH(IN_SRAM_DATA_WIDTH),
        .OUT_FIFO_ADDR_WIDTH(OUT_SRAM_ADDR_WIDTH),
        .OUT_FIFO_DATA_WIDTH(OUT_SRAM_DATA_WIDTH)
) controller(
        .clk(s00_axis_aclk),
        .reset(!s00_axis_aresetn),
        .en(aes_controller_start),

        .aes_cmd(aes_controller_cmd),
        .aes_skip_key_expansion(aes_controller_skip_key_expansion),
        .in_fifo_r_e(aes_controller_in_fifo_r_e),
        .in_fifo_addr(aes_controller_in_fifo_addr),
        .in_fifo_data(aes_controller_in_fifo_data),
        .in_fifo_blk_cnt(aes_controller_in_fifo_blk_cnt),

        .out_fifo_data(aes_controller_out_fifo_data),
        .out_fifo_blk_no(aes_controller_out_fifo_blk_no),
        .out_fifo_w_e(aes_controller_out_fifo_w_e),
        .out_fifo_addr(aes_controller_out_fifo_addr),

        .en_o(aes_controller_done)
);

always @(posedge s00_axis_aclk) begin
	processing_done <= __processing_done;
end

// =====================================================================
/*
* AXI master
*/

assign master_send = (state == MASTER_SEND);

aes_axi_stream_master #(
	.C_M_AXIS_TDATA_WIDTH(C_M_AXIS_TDATA_WIDTH),
	.FIFO_SIZE(OUT_SRAM_DEPTH),
	.FIFO_ADDR_WIDTH(OUT_SRAM_ADDR_WIDTH),
	.FIFO_DATA_WIDTH(OUT_SRAM_DATA_WIDTH)
) axi_stream_master_controller (
	.m00_axis_aclk(m00_axis_aclk),
	.m00_axis_aresetn(m00_axis_aresetn),
	.m00_axis_tvalid(m00_axis_tvalid),
	.m00_axis_tdata(m00_axis_tdata),
	.m00_axis_tstrb(m00_axis_tstrb),
	.m00_axis_tlast(m00_axis_tlast),
	.m00_axis_tready(m00_axis_tready),

	.master_send(master_send),
	.processing_done(processing_done),
	.axis_slave_tlast_reg(axis_slave_tlast_reg),

	.aes_controller_out_fifo_w_e(aes_controller_out_fifo_w_e),
	.aes_controller_out_fifo_addr(aes_controller_out_fifo_addr),
	.aes_controller_out_fifo_data(aes_controller_out_fifo_data),
	.aes_controller_out_fifo_blk_no(aes_controller_out_fifo_blk_no),

	.axis_out_fifo_tx_done(axis_out_fifo_tx_done)
);

endmodule
