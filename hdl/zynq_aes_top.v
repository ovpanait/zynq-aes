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
        parameter integer DATA_FIFO_SIZE = 2048,

	parameter ECB_SUPPORT =  1,
	parameter CBC_SUPPORT =  1,
	parameter CTR_SUPPORT =  1,
	parameter CFB_SUPPORT =  1,
	parameter OFB_SUPPORT =  1,
	parameter PCBC_SUPPORT = 1
)(
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

`include "common.vh"

/*
 * 32kB AES block + 2 x 128-bit slots for key and iv.
 */
localparam OUT_BRAM_DEPTH = DATA_FIFO_SIZE + 2;
localparam IN_BRAM_DEPTH = DATA_FIFO_SIZE + 2;

/// =====================================================================
// Input interface signals

wire                            in_bus_data_wren;
wire [C_S_AXIS_TDATA_WIDTH-1:0] in_bus_data;
wire                            in_bus_tlast;

// =====================================================================
// AES Controller signals

wire aes_controller_done;
wire aes_controller_start;
wire aes_controller_skip_key_expansion;
wire processing_done;

wire controller_in_busy;

// =====================================================================
// Output interface signals

wire [C_M_AXIS_TDATA_WIDTH-1:0]  out_bus_tdata;
wire out_bus_tready;
wire out_bus_tvalid;
wire out_bus_tlast;

// =====================================================================
/*
* AXI streaming slave
*/
axi_stream_slave #(
	.AXIS_TDATA_WIDTH(C_S_AXIS_TDATA_WIDTH)
) axis_slave_controller (
	.clk(s00_axis_aclk),
	.resetn(s00_axis_aresetn),
	.tready(s00_axis_tready),
	.tvalid(s00_axis_tvalid),
	.tlast(s00_axis_tlast),
	.tdata(s00_axis_tdata),
	.tstrb(s00_axis_tstrb),

	.fifo_busy(controller_in_busy),

	.fifo_wren(in_bus_data_wren),
	.fifo_data(in_bus_data),

	.stream_tlast(in_bus_tlast)
);

// =====================================================================
/*
* AES controller
*/

aes_controller #(
	.IN_FIFO_DEPTH(IN_BRAM_DEPTH),
	.OUT_FIFO_DEPTH(OUT_BRAM_DEPTH),

	.ECB_SUPPORT(ECB_SUPPORT),
	.CBC_SUPPORT(CBC_SUPPORT),
	.CTR_SUPPORT(CTR_SUPPORT),
	.CFB_SUPPORT(CFB_SUPPORT)
//	.OFB_SUPPORT(OFB_SUPPORT),
//	.PCBC_SUPPORT(PCBC_SUPPORT)
) controller(
	.clk(s00_axis_aclk),
	.reset(!s00_axis_aresetn),

	.in_bus_data_wren(in_bus_data_wren),
	.in_bus_data(in_bus_data),
	.in_bus_tlast(in_bus_tlast),

	.controller_in_busy(controller_in_busy),

	.out_bus_tvalid(out_bus_tvalid),
	.out_bus_tready(out_bus_tready),
	.out_bus_tdata(out_bus_tdata),
	.out_bus_tlast(out_bus_tlast)
);

// =====================================================================
/*
* AXI streaming master
*/

axi_stream_master #(
	.AXIS_TDATA_WIDTH(C_M_AXIS_TDATA_WIDTH)
) axi_stream_master_controller (
	.clk(m00_axis_aclk),
	.resetn(m00_axis_aresetn),

	.fifo_tready(out_bus_tready),
	.fifo_tvalid(out_bus_tvalid),
	.fifo_tdata(out_bus_tdata),
	.fifo_tlast(out_bus_tlast),

	.tvalid(m00_axis_tvalid),
	.tstrb(m00_axis_tstrb),
	.tdata(m00_axis_tdata),
	.tlast(m00_axis_tlast),
	.tready(m00_axis_tready)
);

endmodule
