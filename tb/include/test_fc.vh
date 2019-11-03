`ifndef TEST_FC_VH
`define TEST_FC_VH

`include "queue_wrapper.vh"

`define PRINT_DBG(var) $display("DEBUG: var: %H", var)
`define VERIFY(sim_val, exp_val) \
        if (!tester #(.WIDTH($size(sim_val)))::verify_output(sim_val, exp_val)) begin \
                        $display("ERROR: %s: : %4d", `__FILE__, `__LINE__); \
		        $finish; \
        end

class tester #(
	int unsigned WIDTH = 32,
	int unsigned UNPACKED_WIDTH = 8,
	int unsigned QUEUE_DATA_WIDTH = 32);

	static function [WIDTH-1:0] reverse_blk8(input [WIDTH-1:0] blk);
		integer i;
		for (i = 0; i < WIDTH / 8; i=i+1)
			reverse_blk8[i*8 +: 8] = blk[(WIDTH / 8 - i - 1)*8+: 8];
	endfunction

	static task pack(input [UNPACKED_WIDTH-1:0] data[], output [WIDTH-1:0] out);
		begin
		for (int i = 0; i < $size(data); ++i)
			out[i*UNPACKED_WIDTH +: UNPACKED_WIDTH] = data[i];
		end
	endtask

	static function bit verify_output(input [WIDTH-1:0] simulated_value, input [WIDTH-1:0] expected_value);
		verify_output = 1;
		if (simulated_value !== expected_value)
		begin
			verify_output = 0;
			$display("Simulated Value = %h \n Expected Value = %h \n at time = %d",
				simulated_value,
				expected_value,
				$time);
		end
	endfunction

	task q_push_back32_rev(input [WIDTH-1:0] data, input queue_wrapper#(QUEUE_DATA_WIDTH) queue);
		if (QUEUE_DATA_WIDTH != 32) begin
			$display("ERROR: %s %l: QUEUE_DATA_WIDTH must be 32!", `__FILE__, `__LINE__);
			$finish;
		end

		for (integer i = 0; i < WIDTH / 32; i=i+1) begin
			queue.push_back(data[i*32 +: 32]);
		end
	endtask
endclass

`endif
