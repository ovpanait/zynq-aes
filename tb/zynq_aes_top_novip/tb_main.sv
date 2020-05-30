`include "aes.vh"
`include "controller_fc.vh"
`include "queue_wrapper.vh"

module tb_main();

localparam TESTCASE_BLOCKS_NO = 2048;
// Worst case scenario: cmd + 256-bit key + IV + 1 block per transaction
localparam AXI_MASTER_FIFO_SIZE = TESTCASE_BLOCKS_NO * 5 * 4;
localparam AXI_SLAVE_FIFO_SIZE = TESTCASE_BLOCKS_NO * 4;

localparam C_M_AXIS_TDATA_WIDTH = 32;
localparam C_S_AXIS_TDATA_WIDTH = 32;

localparam DATA_FIFO_SIZE = 4;

localparam ECB_SUPPORT  = 1;
localparam CBC_SUPPORT  = 1;
localparam CTR_SUPPORT  = 1;
localparam CFB_SUPPORT  = 1;
localparam OFB_SUPPORT  = 1;
localparam PCBC_SUPPORT = 1;

bit clk;
bit reset;

semaphore bus_sem = new(1);

reg [`WORD_S-1:0] cmd;
reg [`BLK_S-1:0]  block;
reg master_packet_end;

wire m00_axis_tvalid;
wire [C_M_AXIS_TDATA_WIDTH - 1 : 0]      m00_axis_tdata;
wire [(C_M_AXIS_TDATA_WIDTH / 8)-1 : 0]  m00_axis_tstrb;
wire m00_axis_tlast;
wire m00_axis_tready;

wire s00_axis_tvalid;
wire [C_S_AXIS_TDATA_WIDTH - 1 : 0]      s00_axis_tdata;
wire [(C_S_AXIS_TDATA_WIDTH / 8)-1 : 0]  s00_axis_tstrb;
wire s00_axis_tlast;
wire s00_axis_tready;

initial begin
	$timeformat(-9, 2, " us", 10);
end

// 125 MHz clk
always #4 clk <= ~clk;

initial begin
	master_packet_end = 1'b0;

	$dumpfile("zynqaes.vcd");
	$dumpvars(1, DUT);

	reset <= 0;
	@(posedge clk);
	@(negedge clk) reset <= 1;
end

axi_stream_master_tb #(
	.C_M_AXIS_TDATA_WIDTH(C_M_AXIS_TDATA_WIDTH),
	.FIFO_SIZE(AXI_MASTER_FIFO_SIZE)
) axi_master (
	.m00_axis_aclk(clk),
	.m00_axis_aresetn(reset),
	.m00_axis_tvalid(m00_axis_tvalid),
	.m00_axis_tdata(m00_axis_tdata),
	.m00_axis_tstrb(m00_axis_tstrb),
	.m00_axis_tlast(m00_axis_tlast),
	.m00_axis_tready(m00_axis_tready)
);

zynq_aes_top #(
	.C_M_AXIS_TDATA_WIDTH(C_M_AXIS_TDATA_WIDTH),
	.C_S_AXIS_TDATA_WIDTH(C_S_AXIS_TDATA_WIDTH),
	.DATA_FIFO_SIZE(DATA_FIFO_SIZE),

	.ECB_SUPPORT(ECB_SUPPORT),
	.CBC_SUPPORT(CBC_SUPPORT),
	.CTR_SUPPORT(CTR_SUPPORT),
	.CFB_SUPPORT(CFB_SUPPORT),
	.OFB_SUPPORT(OFB_SUPPORT),
	.PCBC_SUPPORT(PCBC_SUPPORT)
) DUT (
	.m00_axis_aclk(clk),
	.m00_axis_aresetn(reset),
	.m00_axis_tvalid(s00_axis_tvalid),
	.m00_axis_tdata(s00_axis_tdata),
	.m00_axis_tstrb(s00_axis_tstrb),
	.m00_axis_tlast(s00_axis_tlast),
	.m00_axis_tready(s00_axis_tready),

	.s00_axis_aclk(clk),
	.s00_axis_aresetn(reset),
	.s00_axis_tready(m00_axis_tready),
	.s00_axis_tdata(m00_axis_tdata),
	.s00_axis_tstrb(m00_axis_tstrb),
	.s00_axis_tlast(m00_axis_tlast),
	.s00_axis_tvalid(m00_axis_tvalid)
);

axi_stream_slave_tb #(
	.C_S_AXIS_TDATA_WIDTH(C_S_AXIS_TDATA_WIDTH),
	.FIFO_SIZE(AXI_SLAVE_FIFO_SIZE)
) axi_slave (
	.s00_axis_aclk(clk),
	.s00_axis_aresetn(reset),
	.s00_axis_tvalid(s00_axis_tvalid),
	.s00_axis_tdata(s00_axis_tdata),
	.s00_axis_tstrb(s00_axis_tstrb),
	.s00_axis_tlast(s00_axis_tlast),
	.s00_axis_tready(s00_axis_tready)
);

/*
   * reverse_blk8: Reverse a block of data byte by byte.
   *
   * 11 22 33 44 ----> 44 33 22 11
 */
function [`BLK_S-1:0] reverse_blk8(input [`BLK_S-1:0] blk);
	integer i;
	for (i = 0; i < `BLK_S / 8; i=i+1)
		reverse_blk8[i*8 +: 8] = blk[(`BLK_S / 8 - i - 1) * 8 +: 8];
endfunction

/*
   * Functions for manipulating the AXI slave queue (data from this queue is
   * compared with the data received from the AES engine to make sure it is
   * sending the expected blocks)
 */
task axis_slave_queue_add32(input [31:0] word, input last);
	axi_slave.arr[axi_slave.arr_size][32] = last;
	axi_slave.arr[axi_slave.arr_size][31:0] = word;

	axi_slave.arr_size++;
endtask

task axis_slave_queue_add128(input [127:0] block, input last);
	// Reverse block before pushing it on the results queue
	block = reverse_blk8(block);

	for (integer i = 0; i < 128 / 32; i++)
		axis_slave_queue_add32(block[i * 32 +: 32], (last && i == (128 / 32 - 1)));
endtask

/*
   * Routines for placing data into the AXI master queue. This data will be
   * sent to the AES engine for processing.
 */
task axis_send32(input [31:0] word);
	axi_master.arr[axi_master.arr_size] = word;
	axi_master.arr_size++;
endtask

task axis_send128(input [127:0] block);
	// Reverse blocks before sending them out
	block = reverse_blk8(block);

	for (integer i = 0; i < 128 / 32; i++)
		axis_send32(block[i * 32 +: 32]);
endtask

/*
   * aes_send_request - Send a full packet to the AES engine
   *
   * One packet consists of:
   * CMD + KEY + [IV] + PAYLOAD
 */
task aes_send_request(
	input reg [`WORD_S-1:0]      cmd,
	input reg [`KEY_S-1:0]       key,
	input reg [`WORD_S-1:0]      keylen,
	input reg [`IV_BITS-1:0]     iv,
	input bit                    send_iv,
	input queue_wrapper#(`BLK_S) payload_queue,
	input integer                blks_no
);
	integer i;
	reg [`BLK_S-1:0] block;

	axis_send32(cmd);

	if (keylen == 256) begin
		axis_send128(key[255:128]);
	end

	axis_send128(key[127:0]);

	if (send_iv)
		axis_send128(iv);

	for (i=0; i < blks_no; i++) begin
		block = payload_queue.get(i);
		axis_send128(block);
	end
endtask

task wait_for_transfer();
	wait(master_packet_end);
	@(posedge clk);
	@(negedge clk);
endtask

initial begin
forever begin
	@(posedge clk);
	if (m00_axis_tlast && m00_axis_tvalid && m00_axis_tready) begin
		master_packet_end = 1'b1;
	end

	@(negedge clk);
	if (master_packet_end) begin
		master_packet_end = 1'b0;
	end
end
end

initial begin
	wait (reset);

	fork
		forever begin
			@(negedge clk);
			test_128bit_key();
		end

		forever begin
			@(negedge clk);
			test_256bit_key();
		end
	join
end

initial begin
	wait (axi_slave.head_ptr == TESTCASE_BLOCKS_NO * 4);
	$finish;
end

`include "test_128bit_key.vh"
`include "test_256bit_key.vh"

endmodule
