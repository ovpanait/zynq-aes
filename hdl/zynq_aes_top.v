`include "aes.vh"

module zynq_aes_top #
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

/*
 * 32kB AES block + 2 x 128-bit slots for key and iv.
 * When the payload is larger than DATA_FIFO_SIZE, the two slots will be used to
 * store additional data if necessary.
 */
localparam FIFO_DEPTH = DATA_FIFO_SIZE + (`KEY_S + `IV_BITS) / IN_SRAM_DATA_WIDTH;

localparam OUT_SRAM_ADDR_WIDTH = clogb2(OUT_SRAM_DEPTH);
localparam OUT_SRAM_DATA_WIDTH = `Nb * `WORD_S;
localparam OUT_SRAM_DEPTH = FIFO_DEPTH;

localparam IN_SRAM_ADDR_WIDTH = clogb2(IN_SRAM_DEPTH);
localparam IN_SRAM_DATA_WIDTH = `Nb * `WORD_S;
localparam IN_SRAM_DEPTH = FIFO_DEPTH;

// AXI slave signals
wire start_processing;

wire               axis_slave_done;
wire [`WORD_S-1:0] axis_cmd;

// input FIFO signals
wire                          aes_controller_in_fifo_r_e;
wire [IN_SRAM_DATA_WIDTH-1:0] aes_controller_in_fifo_data;
wire [IN_SRAM_DATA_WIDTH-1:0] in_fifo_rdata;

wire in_fifo_almost_full;
wire in_fifo_full;
wire in_fifo_empty;
wire in_fifo_ready;

// aes signals
wire               aes_controller_done;
wire               aes_controller_start;
wire [0:`WORD_S-1] aes_controller_cmd;
wire               aes_controller_skip_key_expansion;
wire               processing_done;

// output FIFO signals
wire                           aes_controller_out_fifo_w_e;
wire [OUT_SRAM_DATA_WIDTH-1:0] aes_controller_out_fifo_data;

wire out_fifo_almost_full;
wire out_fifo_full;
wire out_fifo_empty;
wire out_fifo_ready;

// AXI master signals
wire axis_master_done;

// =====================================================================
/*
* AXI slave
*/

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

	.axis_master_done(axis_master_done),
	.aes_controller_in_fifo_r_e(aes_controller_in_fifo_r_e),

	.axis_cmd(axis_cmd),
	.axis_slave_done(axis_slave_done),

	.in_fifo_rdata(in_fifo_rdata),
	.in_fifo_ready(in_fifo_ready),
	.in_fifo_full(in_fifo_full),
	.in_fifo_empty(in_fifo_empty),
	.in_fifo_almost_full(in_fifo_almost_full)
);

// =====================================================================
/*
* AES specific stuff
*/
assign aes_controller_cmd = axis_cmd;

assign aes_controller_in_fifo_data = in_fifo_rdata;

aes_controller #(
	.IN_FIFO_ADDR_WIDTH(IN_SRAM_ADDR_WIDTH),
	.IN_FIFO_DATA_WIDTH(IN_SRAM_DATA_WIDTH),
	.OUT_FIFO_ADDR_WIDTH(OUT_SRAM_ADDR_WIDTH),
	.OUT_FIFO_DATA_WIDTH(OUT_SRAM_DATA_WIDTH)
) controller(
	.clk(s00_axis_aclk),
	.reset(!s00_axis_aresetn),

	.aes_cmd(aes_controller_cmd),

	.axis_slave_done(axis_slave_done),
	.in_fifo_r_e(aes_controller_in_fifo_r_e),
	.in_fifo_data(aes_controller_in_fifo_data),
	.in_fifo_ready(in_fifo_ready),
	.in_fifo_full(in_fifo_full),
	.in_fifo_empty(in_fifo_empty),
	.in_fifo_almost_full(in_fifo_almost_full),

	.out_fifo_data(aes_controller_out_fifo_data),
	.out_fifo_w_e(aes_controller_out_fifo_w_e),
	.out_fifo_ready(out_fifo_ready),
	.out_fifo_full(out_fifo_full),
	.out_fifo_empty(out_fifo_empty),
	.out_fifo_almost_full(out_fifo_almost_full),

	.processing_done(processing_done)
);

// =====================================================================
/*
* AXI master
*/

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

	.processing_done(processing_done),

	.aes_controller_out_fifo_w_e(aes_controller_out_fifo_w_e),
	.aes_controller_out_fifo_data(aes_controller_out_fifo_data),

	.out_fifo_ready(out_fifo_ready),
	.out_fifo_full(out_fifo_full),
	.out_fifo_empty(out_fifo_empty),
	.out_fifo_almost_full(out_fifo_almost_full),

	.axis_master_done(axis_master_done)
);

endmodule
