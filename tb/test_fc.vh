// Test setup

`define PRINT_DBG(var) $display("DEBUG: var: %H", var)

class tester #(
	       int unsigned WIDTH = 32,
	       int unsigned UNPACKED_WIDTH = 8);
   static task verify_output(input [WIDTH-1:0] simulated_value, input [WIDTH-1:0] expected_value, ref integer errors);
      begin
	 if (simulated_value != expected_value)
	   begin
	      errors = errors + 1;
	      $display("Simulated Value = %h \n Expected Value = %h \n errors = %d \n at time = %d",
		       simulated_value,
		       expected_value,
		       errors,
		       $time);
	   end
      end
   endtask

   static task packed_to_unpacked(input [WIDTH-1:0] data_in, output [UNPACKED_WIDTH-1:0] data_unpacked []);
      begin
	 data_unpacked.delete();
	 data_unpacked = new [WIDTH/UNPACKED_WIDTH];
	 
	 for (int i = 0; i < $size(data_unpacked); ++i)
	   data_unpacked[i] = data_in[WIDTH - (i + 1)*UNPACKED_WIDTH +: UNPACKED_WIDTH];
      end
   endtask

   static task pack(input [UNPACKED_WIDTH-1:0] data[], output [WIDTH-1:0] out);
      begin
         for (int i = 0; i < $size(data); ++i)
            out[i*UNPACKED_WIDTH +: UNPACKED_WIDTH] = data[i];
      end
   endtask

   static task print_unpacked(input [UNPACKED_WIDTH-1:0] data_unpacked[]);
      begin
	 $write("debug: 0x");
	 for(int i = 0; i < $size(data_unpacked); i++) begin
	    $write("%H", data_unpacked[i]);
	 end
	 $display("");
      end
   endtask

   // The bit direction is reversed
   static task q_push_back32_rev(input [0:WIDTH-1] data, ref reg [0:31] queue[$]);
   begin
        for (integer i = 0; i < WIDTH / 32; i=i+1) begin
                // Workaround because push_back/push_front doesn't work (?)
                queue[queue.size()] = data[i*32 +: 32];
        end
   end
   endtask

endclass
