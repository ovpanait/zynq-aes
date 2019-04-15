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
        parameter integer C_S_AXIS_TDATA_WIDTH = 32
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

// =====================================================================

/*
* Master side signals
*/
reg              axis_tvalid;
wire              axis_tlast;

reg               axis_tvalid_delay;
reg               axis_tlast_delay;

/*
* Slave side signals
*/
wire                             axis_tready;
genvar                           byte_index;
wire                             fifo_wren;

reg                              processing_done;
wire                             start_processing;

// Control state machine implementation
reg [1:0]                        state;

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
* Master side logic
*/
localparam OUT_SRAM_ADDR_WIDTH = 9;
localparam OUT_SRAM_DATA_WIDTH = `Nb * `WORD_S;
localparam OUT_SRAM_DEPTH = 512;

/*
 * The output FIFO is implemented as 128-bit Block RAM:
 * - AES controller writes ciphertexts to it
 * - AXI master reads from it
 */

// SRAM signals
wire [OUT_SRAM_DATA_WIDTH-1:0] out_sram_o_data;
wire [OUT_SRAM_DATA_WIDTH-1:0] out_sram_i_data;
wire [OUT_SRAM_ADDR_WIDTH-1:0] out_sram_addr;
wire out_sram_w_e;
reg out_sram_r_e;

block_ram #(
        .ADDR_WIDTH(OUT_SRAM_ADDR_WIDTH),
        .DATA_WIDTH(OUT_SRAM_DATA_WIDTH),
        .DEPTH(OUT_SRAM_DEPTH)
) out_fifo(
        .clk(m00_axis_aclk),

        .addr(out_sram_addr),
        .i_data(out_sram_i_data),
        .w_e(out_sram_w_e),

        .o_data(out_sram_o_data),
        .r_e(out_sram_r_e)
);

// AXI master implementation
/*
 * The AXI master control logic is:
 * - Read 1 x 128bit ciphertext from out_fifo
 * - Split it in 4 x 32bit words and push them on the AXI bus
 */

wire [OUT_SRAM_DATA_WIDTH-1:0] axis_out_fifo_blk_shift;
reg [OUT_SRAM_DATA_WIDTH-1:0]  axis_out_fifo_blk;
wire [OUT_SRAM_DATA_WIDTH-1:0] axis_out_fifo_blk_next;
reg [OUT_SRAM_ADDR_WIDTH-1:0]  axis_out_fifo_blk_cnt;
reg [OUT_SRAM_ADDR_WIDTH-1:0]  axis_out_fifo_blk_addr;
reg [OUT_SRAM_ADDR_WIDTH-1:0]  axis_out_fifo_word_cnt;
wire                           axis_out_fifo_tx_en;
reg                            axis_out_fifo_tx_done;

assign axis_out_fifo_blk_next = out_sram_o_data;

assign m00_axis_tvalid       = axis_tvalid;
assign m00_axis_tdata        = axis_out_fifo_blk_shift[OUT_SRAM_DATA_WIDTH-`WORD_S +: `WORD_S];
assign m00_axis_tlast        = axis_tlast;
assign m00_axis_tstrb        = {(C_M_AXIS_TDATA_WIDTH/8){1'b1}};

assign axis_out_fifo_blk_shift = axis_out_fifo_blk << axis_out_fifo_word_cnt * `WORD_S;
assign axis_tlast = (axis_out_fifo_blk_cnt == axis_blk_cnt - 1'b1) && 
                                (axis_out_fifo_word_cnt == `Nb - 1'b1);
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
                        // start reading from SRAM before state is MASTER_SEND, while processing_done is active
                        if ((state == MASTER_SEND | processing_done) && !axis_out_fifo_tx_done) begin
                                out_sram_r_e <= 1'b1;
                                axis_master_fsm_state <= AXIS_MASTER_INIT_SRAM;
                        end
                end
                AXIS_MASTER_INIT_SRAM:
                begin
                        out_sram_r_e <= 1'b1;
                        axis_master_fsm_state <= AXIS_MASTER_INIT_TRANSFER;
                        axis_out_fifo_blk_addr <= 1'b0;
                end
                AXIS_MASTER_INIT_TRANSFER:
                begin
                        out_sram_r_e <= 1'b1;
                        axis_out_fifo_blk <= axis_out_fifo_blk_next;
                        axis_tvalid <= 1'b1;
                        axis_out_fifo_blk_addr <= axis_out_fifo_blk_cnt + 1'b1;

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
                                        axis_out_fifo_blk_addr <= axis_out_fifo_blk_addr + 1'b1;
                                        axis_out_fifo_word_cnt <= 1'b0;
                                        axis_out_fifo_blk_cnt <= axis_out_fifo_blk_cnt + 1'b1;
                                end

                                if (axis_tlast) begin
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

// =====================================================================

/*
* AXI slave side
*/
localparam IN_SRAM_ADDR_WIDTH = 9;
localparam IN_SRAM_DATA_WIDTH = `Nb * `WORD_S;
localparam IN_SRAM_DEPTH = 512;

/*
 * The input FIFO is implemented as 128-bit Block RAM:
 * - AXI slave logic writes to it
 * - AES controller reads from it
 */

// SRAM signals
wire [IN_SRAM_DATA_WIDTH-1:0] in_sram_o_data;
wire [IN_SRAM_DATA_WIDTH-1:0] in_sram_i_data;
wire [IN_SRAM_ADDR_WIDTH-1:0] in_sram_addr;
wire in_sram_w_e;
wire in_sram_r_e;

block_ram #(
        .ADDR_WIDTH(IN_SRAM_ADDR_WIDTH),
        .DATA_WIDTH(IN_SRAM_DATA_WIDTH),
        .DEPTH(IN_SRAM_DEPTH)
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

//AXI signals
reg [IN_SRAM_DATA_WIDTH-1:0] axis_slave_in_fifo_blk;      // input FIFO block
reg [IN_SRAM_ADDR_WIDTH-1:0] axis_slave_in_fifo_blk_cnt; // number of 128-bit blocks in the input FIFO
reg [1:0]                    axis_slave_in_fifo_word_cnt;
reg [`WORD_S-1:0]            axis_slave_in_fifo_cmd;
reg                          axis_slave_in_fifo_cmd_flag;
reg                          axis_slave_in_fifo_w_e;
reg [IN_SRAM_ADDR_WIDTH-1:0] axis_slave_in_fifo_addr_reg;
reg                          axis_slave_in_fifo_writes_done;

localparam AXIS_SLAVE_GET_CMD = 1'b0;
localparam AXIS_SLAVE_GET_PAYLOAD = 1'b1;
reg axis_slave_fsm_state;

assign in_sram_i_data = axis_slave_in_fifo_blk;
assign in_sram_w_e = axis_slave_in_fifo_w_e;

assign s00_axis_tready = axis_tready;
assign axis_tready = ((state == WRITE_FIFO) && !axis_slave_in_fifo_writes_done);
assign fifo_wren = s00_axis_tvalid && axis_tready;

reg [IN_SRAM_ADDR_WIDTH-1:0] axis_blk_cnt;

always @(posedge s00_axis_aclk) begin
        if(!s00_axis_aresetn) begin
                axis_slave_in_fifo_blk <= 1'b0;
                axis_slave_in_fifo_blk_cnt <= 1'b0;
                axis_slave_in_fifo_w_e <= 1'b0;
                axis_slave_in_fifo_word_cnt <= 1'b0;
                axis_slave_in_fifo_writes_done <= 1'b0;
                axis_slave_in_fifo_cmd <= 1'b0;
                axis_slave_in_fifo_addr_reg <= 1'b0;

                axis_blk_cnt <= 1'b0;
                axis_slave_fsm_state <= AXIS_SLAVE_GET_CMD;
        end
        else begin
                case (axis_slave_fsm_state)
                        AXIS_SLAVE_GET_CMD:
                        begin
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
                                                axis_slave_in_fifo_addr_reg <= axis_slave_in_fifo_blk_cnt;
                                                axis_slave_in_fifo_blk_cnt <= axis_slave_in_fifo_blk_cnt + 1'b1;
                                                axis_slave_in_fifo_w_e <= 1'b1;
                                                axis_slave_in_fifo_word_cnt <= 1'b0;

                                                if ((axis_slave_in_fifo_blk_cnt == IN_SRAM_DEPTH-1) || s00_axis_tlast) begin
                                                        axis_slave_in_fifo_blk_cnt <= 1'b0;
                                                        axis_blk_cnt <= axis_slave_in_fifo_blk_cnt + 1'b1;
                                                        axis_slave_in_fifo_writes_done <= 1'b1;
                                                end

                                        end
                                end

                                if (processing_done) begin
                                        axis_slave_fsm_state <= AXIS_SLAVE_GET_CMD;
                                        axis_slave_in_fifo_writes_done <= 1'b0;
                                end
                        end
                endcase
        end
end

// One clock enable
assign start_processing = (state == WRITE_FIFO && axis_slave_in_fifo_writes_done == 1'b1 && !processing_done);

always @(posedge s00_axis_aclk) begin
        processing_done <= __processing_done;
end

/*
* AES specific stuff
*/
genvar i;

// aes signals
wire                          aes_controller_done;
wire                          aes_controller_start;
wire [0:`WORD_S-1]            aes_controller_cmd;

assign aes_controller_cmd = axis_slave_in_fifo_cmd;

// input FIFO signals
wire                          aes_controller_in_fifo_r_e;
wire [IN_SRAM_ADDR_WIDTH-1:0] aes_controller_in_fifo_addr;
wire [IN_SRAM_DATA_WIDTH-1:0] aes_controller_in_fifo_data;
wire [IN_SRAM_ADDR_WIDTH-1:0] aes_controller_in_fifo_blk_cnt;

assign aes_controller_in_fifo_data = in_sram_o_data;
assign aes_controller_in_fifo_blk_cnt = axis_blk_cnt;
assign in_sram_r_e = aes_controller_in_fifo_r_e;
assign in_sram_addr = aes_controller_in_fifo_r_e ? aes_controller_in_fifo_addr : axis_slave_in_fifo_addr_reg;

// output FIFO signals
wire                          aes_controller_out_fifo_w_e;
wire [IN_SRAM_ADDR_WIDTH-1:0] aes_controller_out_fifo_addr;
wire [IN_SRAM_DATA_WIDTH-1:0] aes_controller_out_fifo_data;

assign out_sram_w_e = aes_controller_out_fifo_w_e;
assign out_sram_addr = aes_controller_out_fifo_w_e ? aes_controller_out_fifo_addr : axis_out_fifo_blk_addr;
assign out_sram_i_data = aes_controller_out_fifo_data;

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
        .in_fifo_r_e(aes_controller_in_fifo_r_e),
        .in_fifo_addr(aes_controller_in_fifo_addr),
        .in_fifo_data(aes_controller_in_fifo_data),
        .in_fifo_blk_cnt(aes_controller_in_fifo_blk_cnt),

        .out_fifo_data(aes_controller_out_fifo_data),
        .out_fifo_w_e(aes_controller_out_fifo_w_e),
        .out_fifo_addr(aes_controller_out_fifo_addr),

        .en_o(aes_controller_done)
);

endmodule
