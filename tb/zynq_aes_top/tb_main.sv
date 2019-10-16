import axi4stream_vip_pkg::*;
import design_1_axi4stream_vip_0_0_pkg::*;
import design_1_axi4stream_vip_1_0_pkg::*;

`include "test_fc.vh"
`include "aes_test.vh"
`include "aes.vh"

module tb_main(
);

integer errors = 0;

// Comparison count to check how many comparsion happened
xil_axi4stream_uint                            comparison_cnt = 0;

// Monitor transaction from master VIP
axi4stream_monitor_transaction                 mst_monitor_transaction;
// Monitor transaction queue for master VIP 
axi4stream_monitor_transaction                 master_moniter_transaction_queue[$];
// Size of master_moniter_transaction_queue
xil_axi4stream_uint                           master_moniter_transaction_queue_size =0;
// Scoreboard transaction from master monitor transaction queue
axi4stream_monitor_transaction                 mst_scb_transaction;
// Monitor transaction for slave VIP
axi4stream_monitor_transaction                 slv_monitor_transaction;
// Monitor transaction queue for slave VIP
axi4stream_monitor_transaction                 slave_moniter_transaction_queue[$];
// Size of slave_moniter_transaction_queue
xil_axi4stream_uint                            slave_moniter_transaction_queue_size =0;
// Scoreboard transaction from slave monitor transaction queue
axi4stream_monitor_transaction                 slv_scb_transaction;

// Master VIP agent verbosity level
xil_axi4stream_uint                           mst_agent_verbosity = 0;
// Slave VIP agent verbosity level
xil_axi4stream_uint                           slv_agent_verbosity = 0;

design_1_axi4stream_vip_0_0_mst_t                              mst_agent;
design_1_axi4stream_vip_1_0_slv_t                              slv_agent;

// Clock signal
bit                                     clock;
// Reset signal
bit                                     reset;

queue_wrapper #(`WORD_S) results;
tester #(
	.WIDTH(`BLK_S),
	.QUEUE_DATA_WIDTH(`WORD_S)
	) queue_tester;

aes_test #(
	.master_agent_t(design_1_axi4stream_vip_0_0_mst_t)
	) aes_tester;

// instantiate bd
design_1_wrapper DUT(
        .aresetn(reset),
        .aclk(clock)
);
// Data passed by the kernel has the bytes swapped due to the way it is represented in the 16 byte
// buffer (data from the buffer gets converted to little endian 32-bit words and sent on the axi bus)
function [0:`WORD_S-1] swap_bytes32(input [0:`WORD_S-1] data);
        integer i;
        begin
                for (i = 0; i < `WORD_S / `BYTE_S; i=i+1)
                        swap_bytes32[i*`BYTE_S +: `BYTE_S] = data[(`WORD_S / `BYTE_S - i - 1)*`BYTE_S +: `BYTE_S];
        end
endfunction

function [0:`BLK_S-1] swap_blk(input [0:`BLK_S-1] blk);
        integer i;
        begin
                for (i = 0; i < `BLK_S / `WORD_S; i=i+1)
                        swap_blk[i*`WORD_S +: `WORD_S] = swap_bytes32(blk[i*`WORD_S +: `WORD_S]);

        end
endfunction

// 125 MHz clock
always #4 clock <= ~clock;

initial
begin
        reset <= 0;
        @(posedge clock);
        @(negedge clock) reset <= 1;    
end

//Main process
initial begin
	mst_monitor_transaction = new("master monitor transaction");
	slv_monitor_transaction = new("slave monitor transaction");

	mst_agent = new("master vip agent",DUT.design_1_i.axi4stream_vip_0.inst.IF);
	slv_agent = new("slave vip agent",DUT.design_1_i.axi4stream_vip_1.inst.IF);
	$timeformat (-12, 1, " ps", 1);

	aes_tester = new(mst_agent);
	queue_tester = new();
	results = new();

	mst_agent.vif_proxy.set_dummy_drive_type(XIL_AXI4STREAM_VIF_DRIVE_NONE);
	slv_agent.vif_proxy.set_dummy_drive_type(XIL_AXI4STREAM_VIF_DRIVE_NONE);

	mst_agent.set_agent_tag("Master VIP");
	slv_agent.set_agent_tag("Slave VIP");

	// set print out verbosity level.
	mst_agent.set_verbosity(mst_agent_verbosity);
	slv_agent.set_verbosity(slv_agent_verbosity);

	mst_agent.start_master();
	slv_agent.start_slave();
	slv_gen_tready();

	testcase1();
	testcase2();
	testcase3();
	testcase4();

	$finish;
end

task slv_gen_tready();
        axi4stream_ready_gen                           ready_gen;
        ready_gen = slv_agent.driver.create_ready("ready_gen");
        ready_gen.set_ready_policy(XIL_AXI4STREAM_READY_GEN_OSC);
        ready_gen.set_low_time(2);
        ready_gen.set_high_time(6);
        slv_agent.driver.send_tready(ready_gen);
endtask :slv_gen_tready

initial begin
        forever begin
                mst_agent.monitor.item_collected_port.get(mst_monitor_transaction);
                master_moniter_transaction_queue.push_back(mst_monitor_transaction);
                master_moniter_transaction_queue_size++;
        end  
end 

initial begin
        forever begin
                slv_agent.monitor.item_collected_port.get(slv_monitor_transaction);
                slave_moniter_transaction_queue.push_back(slv_monitor_transaction);
                slave_moniter_transaction_queue_size++;
        end
end

initial begin
        forever begin
                wait (master_moniter_transaction_queue_size>0 ) begin
                        xil_axi4stream_data_byte mst_data [0:3];
                        mst_scb_transaction = master_moniter_transaction_queue.pop_front;
                        master_moniter_transaction_queue_size--;

                        mst_scb_transaction.get_data(mst_data);
                end
        end
end // initial begin

initial begin
        forever begin
                wait (slave_moniter_transaction_queue_size > 0) begin
                        xil_axi4stream_data_byte slv_data [4];
                        reg [0:`WORD_S-1] slv_data_packed;

                        slv_scb_transaction = slave_moniter_transaction_queue.pop_front;
                        slave_moniter_transaction_queue_size--;  

                        slv_scb_transaction.get_data(slv_data);

                        tester#($size(slv_data_packed))::pack(slv_data, slv_data_packed);
                        results.push_back(swap_bytes32(slv_data_packed));  // swap bytes again 
                                                                           // to match the values
                                                                           // as seen by the kernel
                        comparison_cnt++;
                end  
        end
end // initial begin

// Benchmarks
`define AES_AXI_STREAM DUT.design_1_i.zynq_aes_0.inst
`define AES_CONTROLLER `AES_AXI_STREAM.controller

initial begin
	time total_time;

	forever begin
		wait (`AES_AXI_STREAM.s00_axis_tvalid && `AES_AXI_STREAM.s00_axis_tready);
		total_time = $time;
		wait (`AES_AXI_STREAM.m00_axis_tlast == 1'b1);
		wait (`AES_AXI_STREAM.m00_axis_tlast == 1'b0);
		total_time = $time - total_time;

		$display("BENCHMARK: Request took %t.", total_time);
	end
end

`include "test1.vh"
`include "test2.vh"
`include "test3.vh"
`include "test4.vh"

endmodule

