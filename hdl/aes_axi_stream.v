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
localparam NUMBER_OF_INPUT_WORDS  = 5;
// Output FIFO size (master side)
localparam NUMBER_OF_OUTPUT_WORDS = 4;

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
reg [bit_num-1:0]                write_pointer;
reg                              writes_done;

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
                        if (writes_done) begin
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
                        if (read_pointer == NUMBER_OF_OUTPUT_WORDS-1) begin
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
* Slave side logic
*/

/*
* Slave side I/O Connections assignments
*/
assign s00_axis_tready = axis_tready;
assign axis_tready = ((state == WRITE_FIFO) && !writes_done);

always @(posedge s00_axis_aclk) begin
        if(!s00_axis_aresetn) begin
                write_pointer <= 1'b0;
                writes_done <= 1'b0;
        end
        else begin
                if (fifo_wren) begin
                        if ((write_pointer == NUMBER_OF_INPUT_WORDS-1) ||
                        s00_axis_tlast) begin
                                writes_done <= 1'b1;
                        end
                        else begin
                                write_pointer <= write_pointer + 1'b1;
                        end
                end

                if (processing_done) begin
                        write_pointer <= 1'b0;
                        writes_done <= 1'b0;
                end
        end
end

assign fifo_wren = s00_axis_tvalid && axis_tready;

reg  [C_S_AXIS_TDATA_WIDTH-1:0] in_stream_data_fifo [0 : NUMBER_OF_INPUT_WORDS-1];

always @(posedge s00_axis_aclk) begin
        if (fifo_wren)// && S_AXIS_TSTRB[byte_index])
        begin
                in_stream_data_fifo[write_pointer] <= s00_axis_tdata;
        end
end

// One clock enable
assign start_processing = (state == WRITE_FIFO && writes_done == 1'b1 && !processing_done);

/* 
* Delay processing module "done" strobe by one clock to match fsm implementation
*/

always @(posedge s00_axis_aclk) begin
        processing_done <= __processing_done;
end

/*
* AES specific stuff
*/
wire [0:`BLK_S-1]       aes_ciphertext;
wire                    aes_done;

wire                    aes_start;
wire [0:`BLK_S-1]       aes_plaintext;
wire [0:`KEY_S-1]       aes_key;
wire [0:`WORD_S-1]      aes_cmd;

assign __processing_done = aes_done;
assign aes_start = start_processing;

// Map FIFO to output signals
genvar i;

assign aes_cmd = in_stream_data_fifo[0];

// aes plaintext
generate for (i = 0; i < `Nb; i=i+1) begin
        assign aes_plaintext[i*C_S_AXIS_TDATA_WIDTH +: C_S_AXIS_TDATA_WIDTH] = (aes_cmd == `ENCRYPT) ? in_stream_data_fifo[i+1] : 32'h0;
end
endgenerate

// aes key
generate for (i = 0; i < `Nk; i=i+1) begin
        assign aes_key[i*C_S_AXIS_TDATA_WIDTH +: C_S_AXIS_TDATA_WIDTH] = (aes_cmd == `SET_KEY) ? in_stream_data_fifo[i+1] : 32'h0;
end
endgenerate

// aes ciphertext
generate for (i = 0; i < NUMBER_OF_OUTPUT_WORDS; i=i+1) begin
        assign out_stream_data_fifo[i] = aes_ciphertext[i*C_S_AXIS_TDATA_WIDTH +: C_S_AXIS_TDATA_WIDTH];
end
endgenerate

aes_top aes_mod(
        .clk(s00_axis_aclk),
        .reset(!s00_axis_aresetn),
        .en(aes_start),

        .aes_cmd(aes_cmd),
        .aes_key(aes_key),
        .aes_plaintext(aes_plaintext),

        .aes_ciphertext(aes_ciphertext),
        .en_o(aes_done)
);

endmodule
