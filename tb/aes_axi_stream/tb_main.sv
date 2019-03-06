import axi4stream_vip_pkg::*;
import design_1_axi4stream_vip_0_0_pkg::*;
import design_1_axi4stream_vip_1_0_pkg::*;

`include "test_fc.vh"
`include "aes.vh"

module tb_main(
);

// Error count to check how many comparison failed
xil_axi4stream_uint                            error_cnt = 0; 
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

// Test signals
reg [0:7]               data_tmp[];

reg [0:`BLK_S-1]        aes_plaintext;
reg [0:`KEY_S-1]        aes_key;

//  Expected results
reg [0:`WORD_S-1] expected_results[] = '{
        32'h0,
        32'h0,
        32'h0,
        32'h0,

        // Test 1
        32'h29c3505f,
        32'h571420f6,
        32'h402299b3,
        32'h1a02d73a,

        // Test 2
        32'h2914b146,
        32'h6013ba1e,
        32'h48d6d795,
        32'he97d3e15
};

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


always #10 clock <= ~clock;

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

        mst_agent.vif_proxy.set_dummy_drive_type(XIL_AXI4STREAM_VIF_DRIVE_NONE);
        slv_agent.vif_proxy.set_dummy_drive_type(XIL_AXI4STREAM_VIF_DRIVE_NONE);

        mst_agent.set_agent_tag("Master VIP");
        slv_agent.set_agent_tag("Slave VIP");

        // set print out verbosity level.
        mst_agent.set_verbosity(mst_agent_verbosity);
        slv_agent.set_verbosity(slv_agent_verbosity);

        mst_agent.start_master();
        slv_agent.start_slave();

        // Test 1
        // The values need to be swap to math the values put by the kernel on the AXI bus
        aes_key =  {
                8'h54, 8'h68, 8'h61, 8'h74,
                8'h73, 8'h20, 8'h6D, 8'h79,
                8'h20, 8'h4B, 8'h75, 8'h6E,
                8'h67, 8'h20, 8'h46, 8'h75
        };
        aes_plaintext =  {
                8'h54, 8'h77, 8'h6F, 8'h20,
                8'h4F, 8'h6E, 8'h65, 8'h20,
                8'h4E, 8'h69, 8'h6E, 8'h65,
                8'h20, 8'h54, 8'h77, 8'h6F
        };
 
        aes_plaintext = swap_blk(aes_plaintext);
        aes_key = swap_blk(aes_key);

        $display("Sending...");
        tester #(32)::packed_to_unpacked(`SET_KEY, data_tmp);
        tester::print_unpacked(data_tmp);
        gen_transaction(data_tmp);

        tester #($size(aes_key))::packed_to_unpacked(aes_key, data_tmp);
        tester::print_unpacked(data_tmp);
        gen_transaction(data_tmp, 1);

        slv_gen_tready();

        wait(comparison_cnt == 4);
        tester #(32)::packed_to_unpacked(`ENCRYPT, data_tmp);
        tester::print_unpacked(data_tmp);
        gen_transaction(data_tmp);

        tester #($size(aes_plaintext))::packed_to_unpacked(aes_plaintext, data_tmp);
        tester::print_unpacked(data_tmp);
        gen_transaction(data_tmp, 1);

        wait(comparison_cnt == 8);

        // Test 2
        aes_plaintext = {
                8'h12, 8'h34, 8'h56, 8'h78,
                8'h91, 8'h11, 8'h23, 8'h45,
                8'h67, 8'h89, 8'h01, 8'h23,
                8'h45, 8'h67, 8'h89, 8'h01
        };
        aes_plaintext = swap_blk(aes_plaintext);

        tester #(32)::packed_to_unpacked(`ENCRYPT, data_tmp);
        tester::print_unpacked(data_tmp);
        gen_transaction(data_tmp);

        tester #($size(aes_plaintext))::packed_to_unpacked(aes_plaintext, data_tmp);
        tester::print_unpacked(data_tmp);
        gen_transaction(data_tmp, 1);

        wait(comparison_cnt == 12);

        if(error_cnt == 0) begin
                $display("Regression Testing Completed Successfully");
        end 

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
                        print_data("Sent master data: ", mst_data);
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
                        print_data("Received slave data: ", slv_data);

                        tester#($size(slv_data_packed))::pack(slv_data, slv_data_packed);

                        tester #($size(slv_data_packed))::verify_output(slv_data_packed, 
                                         swap_bytes32(expected_results[comparison_cnt])); // swap bytes again 
                                                                                          // to match the values
                                                                                          // as seen by the kernel
                        comparison_cnt++;
                end  
        end
end // initial begin

/* ******************** */
task automatic gen_rand_transaction(ref axi4stream_transaction wr_transaction);
        wr_transaction = mst_agent.driver.create_transaction("Master VIP write transaction");
        wr_transaction.set_xfer_alignment(XIL_AXI4STREAM_XFER_RANDOM);
        WR_TRANSACTION_FAIL: assert(wr_transaction.randomize());
endtask

// Tasks
task gen_transaction(input [0:7] data[], input last = 0);
        for (int i = 0; i < $size(data); i = i + 4)
        begin
                xil_axi4stream_data_byte data_dbg[4];
                axi4stream_transaction                         wr_transaction; 

                gen_rand_transaction(wr_transaction);
                wr_transaction.set_data('{data[i+3], data[i+2], data[i+1], data[i]});

                wr_transaction.set_last(0);
                if (i == $size(data) - 4 && last == 1)
                        wr_transaction.set_last(1);

                wr_transaction.get_data(data_dbg);

                mst_agent.driver.send(wr_transaction);
        end
endtask;

function print_data(string msg, xil_axi4stream_data_byte data[4]);
        begin
                $write({msg, " "});

                // data is stored in litle endian
                $write("0x");
                for(int i = $size(data) - 1; i >= 0; i--) begin
                        $write("%H", data[i]);
                end
                $display("");
        end
endfunction;

// Debugging
/*always @(DUT.design_1_i.aes_axi_stream_0.inst.aes_mod.en) begin
        $display("xxx1 en: %H", DUT.design_1_i.aes_axi_stream_0.inst.aes_mod.en);
        $display("xxx1 aes_plaintext: %H", DUT.design_1_i.aes_axi_stream_0.inst.aes_mod.aes_plaintext);
        $display("xxx1 aes_key: %H\n", DUT.design_1_i.aes_axi_stream_0.inst.aes_mod.aes_key);

end
always @(DUT.design_1_i.aes_axi_stream_0.inst.writes_done) begin
        $display("xxx2 writes_done: %H\n", DUT.design_1_i.aes_axi_stream_0.inst.writes_done);
end

always @(DUT.design_1_i.aes_axi_stream_0.inst.s00_axis_tlast) begin
        $display("xxx3 axis_tlast: %H\n", DUT.design_1_i.aes_axi_stream_0.inst.s00_axis_tlast);
end
*/

endmodule

