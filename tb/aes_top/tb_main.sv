
`timescale 1ns/1ns
`define PERIOD 5

`include "aes.vh"

module tb_main();

   // Module instantiation
   reg clk;
   reg reset;
   reg en;

   reg [`KEY_S-1:0] key;

   aes_top DUT (
		.clk(clk),
		.reset(reset),
		.en(en),
      
		.key(key)
		);
   
   // Test functions
`include "test_fc.vh"

   // Auxiliary counters
   integer 	     i;

   // Test results
   reg [`KEY_S-1:0]  expected_round_key [0:`Nr] = '{
						    `KEY_S'h5468617473206d79204b756e67204675,
						    `KEY_S'he232fcf191129188b159e4e6d679a293,
						    `KEY_S'h56082007c71ab18f76435569a03af7fa,
						    `KEY_S'hd2600de7157abc686339e901c3031efb,
						    `KEY_S'ha11202c9b468bea1d75157a01452495b,
						    `KEY_S'hb1293b3305418592d210d232c6429b69,
						    `KEY_S'hbd3dc287b87c47156a6c9527ac2e0e4e,
						    `KEY_S'hcc96ed1674eaaa031e863f24b2a8316a,
						    `KEY_S'h8e51ef21fabb4522e43d7a0656954b6c,
						    `KEY_S'hbfe2bf904559fab2a16480b4f7f1cbd8,
						    `KEY_S'h28fddef86da4244accc0a4fe3b316f26
						    };

   reg [`Nb-1:0]     round = 1'b0;
   
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

      // Testcase init
      wait(reset)
	@(posedge clk);
      @(negedge clk) reset = 0;

      // Testcase
      @(negedge clk) begin
	 en = 1;
	 key =  {
		 8'h54, 8'h68, 8'h61, 8'h74,
		 8'h73, 8'h20, 8'h6D, 8'h79,
		 8'h20, 8'h4B, 8'h75, 8'h6E,
		 8'h67, 8'h20, 8'h46, 8'h75
		 };
      end

      @(negedge clk) begin
	 en = 0;
      end

      @(posedge DUT.en_o);
      @(negedge clk);
      @(negedge clk); // wait 1 more cycle
      
      for (i =0; i < `Nr + 1'b1; i = i+1) begin
	 tester #($size(key))::verify_output(DUT.sram.sram[round], expected_round_key[round]);
	 round = round + 1'b1;
      end
      
      /*      @(negedge clk)
       tester #($size(en_o))::verify_output(en_o, 1'b0);
       */
      // Testcase end
      @(negedge clk) reset = 1;
      @(negedge clk);

      $display("\nSimulation completed with %d errors\n", errors);
      $stop;
   end // initial begin
endmodule
