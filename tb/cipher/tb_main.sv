
`timescale 1ns/1ns
`define PERIOD 5

`include "aes.vh"

module tb_main();

   // Module instantiation
   reg clk;
   reg reset;
   reg en;

   reg [0:`BLK_S-1] plaintext;
   reg [0:`KEY_S-1] key;

   wire [0:3] 	    round_no;
   wire [0:`BLK_S-1] ciphertext;
   wire 	     r_e;
   wire 	     en_o;

   cipher DUT (
	       .clk(clk),
	       .reset(reset),
	       .en(en),

	       .plaintext(plaintext),
	       .key(key),

	       .ciphertext(ciphertext),
	       .round_no(round_no),
	       .r_e(r_e),
	       .en_o(en_o)
	       );

   // Test functions
`include "test_fc.vh"

   // Auxiliary counters
   integer 	     i;

   // Test results
   reg [`KEY_S-1:0]  key_sram [0:`Nr] = '{
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

   reg [0:`BLK_S-1]  expected_ciphertext =
		     `BLK_S'h29c3505f571420f6402299b31a02d73a;

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
	 plaintext =  {
		       8'h54, 8'h77, 8'h6F, 8'h20,
		       8'h4F, 8'h6E, 8'h65, 8'h20,
		       8'h4E, 8'h69, 8'h6E, 8'h65,
		       8'h20, 8'h54, 8'h77, 8'h6F
		       };
      end

      @(negedge clk) begin
	 en = 0;
      end

      @(posedge DUT.en_o);
      @(negedge clk);

      tester #($size(expected_ciphertext))::verify_output(DUT.ciphertext, expected_ciphertext);

      // Testcase end
      @(negedge clk) reset = 1;
      @(negedge clk);

      $display("\nSimulation completed with %d errors\n", errors);
      $stop;
   end // initial begin

   // simulate key sram behavior
   always @(posedge clk) begin
      if (r_e == 1'b1) begin
	 key <= key_sram[round_no];
      end
   end
endmodule
