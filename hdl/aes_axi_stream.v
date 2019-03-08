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

// Input FIFO size (slave side)
localparam NUMBER_OF_INPUT_WORDS  = 2048;
// Output FIFO size (master side)
localparam NUMBER_OF_OUTPUT_WORDS = 2048;

// bit_num gives the minimum number of bits needed to address 'NUMBER_OF_INPUT_WORDS' size of FIFO.
localparam bit_num  = clogb2(NUMBER_OF_INPUT_WORDS-1);

// Control state machine states
parameter [1:0] IDLE = 1'b0, // Initial/idle state

WRITE_FIFO  = 1'b1, // Input FIFO is written with the input stream data S_AXIS_TDATA

PROCESS_STUFF = 2'b11, // Data is being processed and placed into the output FIFO

MASTER_SEND = 2'b10; // Master is sending processed data

// =====================================================================

/*
* Master side signals
*/
reg [bit_num-1:0] read_pointer;

// AXI Stream internal signals
wire              axis_tvalid;
wire              axis_tlast;

reg               axis_tvalid_delay;
reg               axis_tlast_delay;

wire [C_M_AXIS_TDATA_WIDTH-1 : 0] out_stream_data_fifo [0 : NUMBER_OF_OUTPUT_WORDS - 1];
reg [C_M_AXIS_TDATA_WIDTH-1 : 0] stream_data_out;
wire                             tx_en;

reg                              tx_done;

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
                        if (tx_done) begin
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

/*
* Master side I/O Connections assignments
*/
assign m00_axis_tvalid       = axis_tvalid;
assign m00_axis_tdata        = stream_data_out;
assign m00_axis_tlast        = axis_tlast;
assign m00_axis_tstrb        = {(C_M_AXIS_TDATA_WIDTH/8){1'b1}};

assign axis_tlast = (read_pointer == NUMBER_OF_OUTPUT_WORDS-1);
assign axis_tvalid = (state == MASTER_SEND) && !tx_done;

always @(posedge m00_axis_aclk) begin
        if(!m00_axis_aresetn) begin
                read_pointer <= 0;
                tx_done <= 1'b0;
        end 
        else begin
                tx_done <= 1'b0;

                if (tx_en) begin
                        if (read_pointer == axis_slave_in_fifo_blk_cnt * 3'h4 - 1'b1) begin // keep this workaround until output FIFO gets updated too
                                axis_slave_in_fifo_blk_cnt <= 1'b0;
                                read_pointer <= 1'b0;
                                tx_done <= 1'b1;
                        end
                        else begin
                                read_pointer <= read_pointer + 1'b1;
                                tx_done <= 1'b0;
                        end
                end // if (tx_en)
        end
end

assign tx_en = m00_axis_tready && axis_tvalid;

always @(posedge m00_axis_aclk) begin
        if(!m00_axis_aresetn) begin
                stream_data_out <= 1'b0;
        end
        else begin
                stream_data_out <= out_stream_data_fifo[read_pointer];
                if (tx_en) begin
                        stream_data_out <= out_stream_data_fifo[read_pointer + 1'b1];
                end
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
 * The AXI slave logic is:
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

assign in_sram_i_data = axis_slave_in_fifo_blk;
assign in_sram_w_e = axis_slave_in_fifo_w_e;

assign s00_axis_tready = axis_tready;
assign axis_tready = ((state == WRITE_FIFO) && !axis_slave_in_fifo_writes_done);

always @(posedge s00_axis_aclk) begin
        if(!s00_axis_aresetn) begin
                axis_slave_in_fifo_blk <= 1'b0;
                axis_slave_in_fifo_blk_cnt <= 1'b0;
                axis_slave_in_fifo_w_e <= 1'b0;
                axis_slave_in_fifo_word_cnt <= 1'b0;
                axis_slave_in_fifo_writes_done <= 1'b0;
                axis_slave_in_fifo_cmd <= 1'b0;
                axis_slave_in_fifo_cmd_flag <= 1'b0;
                axis_slave_in_fifo_addr_reg <= 1'b0;
        end
        else begin
                axis_slave_in_fifo_w_e <= 1'b0;
                if (fifo_wren && axis_slave_in_fifo_cmd_flag) begin
                        axis_slave_in_fifo_word_cnt <= axis_slave_in_fifo_word_cnt + 1'b1;

                        if (axis_slave_in_fifo_word_cnt == `Nb - 1'b1) begin
                                axis_slave_in_fifo_addr_reg <= axis_slave_in_fifo_blk_cnt;
                                axis_slave_in_fifo_blk_cnt <= axis_slave_in_fifo_blk_cnt + 1'b1;
                                axis_slave_in_fifo_w_e <= 1'b1;
                                axis_slave_in_fifo_word_cnt <= 1'b0;

                                if ((axis_slave_in_fifo_blk_cnt == IN_SRAM_DEPTH-1) || s00_axis_tlast) begin
                                        axis_slave_in_fifo_writes_done <= 1'b1;
                                        axis_slave_in_fifo_cmd_flag <= 1'b0;
                                end

                        end
                end

                if (processing_done) begin
                        axis_slave_in_fifo_writes_done <= 1'b0;
                end
        end
end

assign fifo_wren = s00_axis_tvalid && axis_tready;

always @(posedge s00_axis_aclk) begin
        if (fifo_wren)// && S_AXIS_TSTRB[byte_index])
        begin
                if (!axis_slave_in_fifo_cmd_flag) begin
                        //first received word is the command
                        axis_slave_in_fifo_cmd <= s00_axis_tdata;
                        axis_slave_in_fifo_cmd_flag <= 1'b1;
                end 
                else begin
                        axis_slave_in_fifo_blk <= (axis_slave_in_fifo_blk << `WORD_S) | s00_axis_tdata;
                end
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

wire                          aes_controller_done;
wire                          aes_controller_start;
wire [0:`WORD_S-1]            aes_controller_cmd;
wire                          aes_controller_in_fifo_r_e;
wire [IN_SRAM_ADDR_WIDTH-1:0] aes_controller_in_fifo_addr;
wire [IN_SRAM_DATA_WIDTH-1:0] aes_controller_in_fifo_data;
wire [IN_SRAM_ADDR_WIDTH-1:0] aes_controller_in_fifo_blk_cnt;

assign aes_controller_in_fifo_data = in_sram_o_data;
assign aes_controller_in_fifo_blk_cnt = axis_slave_in_fifo_blk_cnt;
assign in_sram_r_e = aes_controller_in_fifo_r_e;
assign in_sram_addr = aes_controller_in_fifo_r_e ? aes_controller_in_fifo_addr : axis_slave_in_fifo_addr_reg;
assign aes_controller_cmd = axis_slave_in_fifo_cmd;

/*
* Delay processing module "done" strobe by one clock to match fsm implementation
*/
assign __processing_done = aes_controller_done;
assign aes_controller_start = start_processing;

wire [NUMBER_OF_OUTPUT_WORDS * `WORD_S - 1 : 0] out_fifo;

generate for (i = 0; i < NUMBER_OF_OUTPUT_WORDS; i=i+1) begin
        assign out_stream_data_fifo[i] = out_fifo[i*`WORD_S +: `WORD_S];
end
endgenerate

aes_controller #(
        .IN_FIFO_ADDR_WIDTH(IN_SRAM_ADDR_WIDTH),
        .IN_FIFO_DATA_WIDTH(IN_SRAM_DATA_WIDTH),
        .OUT_FIFO_DEPTH(2048)
) controller(
        .clk(s00_axis_aclk),
        .reset(!s00_axis_aresetn),
        .en(aes_controller_start),

        .aes_cmd(aes_controller_cmd),
        .in_fifo_r_e(aes_controller_in_fifo_r_e),
        .in_fifo_addr(aes_controller_in_fifo_addr),
        .in_fifo_data(aes_controller_in_fifo_data),
        .in_fifo_blk_cnt(aes_controller_in_fifo_blk_cnt),

        .out_fifo(out_fifo),

        .en_o(aes_controller_done)
);

endmodule
