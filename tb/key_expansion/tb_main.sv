
`timescale 1ns/1ns
`define PERIOD 5

`include "aes.vh"

module tb_main();

   // Module instantiation
   reg clk;
   reg reset;
   reg en;

   reg [`Nb-1:0] round_no;
   reg [`KEY_S-1:0] prev_key;
   wire [`KEY_S-1:0] round_key;
   wire 	     en_o;

   
   round_key DUT (
		  .clk(clk),
		  .reset(reset),
		  .en(en),

		  .key(prev_key),

		  .round_key(round_key),
		  .en_o(en_o)
		  );

   // Test functions
`include "test_fc.vh"

   // Auxiliary counters
   integer 	     i;

   initial begin
      clk <= 0;
      forever #(`PERIOD) clk = ~clk;
   end

   initial begin
      reset <= 0;
      @(posedge clk); //may need several cycles for reset
      @(negedge clk) reset = 1;
   end

   initial begin
      errors = 0; // reset error count

      // Inputs

      $display("Testing W output and number of clock cycles... ");

      // Testcase init
      wait(reset)
	@(posedge clk);
      @(negedge clk) reset = 0;

      // Testcase
      @(negedge clk) begin
	 en = 1;
	 prev_key =  {
		      8'h54, 8'h68, 8'h61, 8'h74,
		      8'h73, 8'h20, 8'h6D, 8'h79,
		      8'h20, 8'h4B, 8'h75, 8'h6E,
		      8'h67, 8'h20, 8'h46, 8'h75
		      };
	 round_no = 1  ;
      end

      @(negedge clk) begin
	 en = 0;
      end

      @(posedge en_o);
      
   /*   @(negedge clk) begin
	 tester #(1)::verify_output(en_o, 1'b1);
	 tester #($size(round_key))::verify_output(round_key, `KEY_S'b0);
      end
*/
      @(negedge clk)
	tester #(1)::verify_output(en_o, 1'b0);

      // Testcase end
      @(negedge clk) reset = 1;
      @(negedge clk);

      $display("\nSimulation completed with %d errors\n", errors);
      $stop;
   end // initial begin

   always @(DUT.round_key)
     begin
	$display("%H", DUT.round_key);
     end
endmodule
