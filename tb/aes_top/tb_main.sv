
`timescale 1ns/1ns
`define PERIOD 5

`include "aes.vh"

module tb_main();

   // Module instantiation
   reg clk;
   reg reset;
   reg en;

   reg [0:`KEY_S-1] aes_key;
   reg [0:`BLK_S-1] aes_plaintext;

   wire [0:`BLK_S-1] aes_ciphertext;
   wire 	     en_o;

   aes_top DUT (
		.clk(clk),
		.reset(reset),
		.en(en),

		.aes_key(aes_key),
		.aes_plaintext(aes_plaintext),

		.aes_ciphertext(aes_ciphertext),
		.en_o(en_o)
		);

   // Test functions
`include "test_fc.vh"

   // Auxiliary counters
   integer 	     i;

   // Test results
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
      end

      @(negedge clk) begin
	 en = 0;
      end

      @(posedge DUT.en_o);

      // Test ciphertext output
`define RES_AES_CIPHERTEXT `BLK_S'h29c3505f571420f6402299b31a02d73a
      @(negedge clk);
      tester #($size(aes_ciphertext))::verify_output(aes_ciphertext, `RES_AES_CIPHERTEXT);

      // Test 1 clock cycle
      @(negedge clk);
      tester #($size(en_o))::verify_output(en_o, `BLK_S'h0);

      // Testcase end
      @(negedge clk) reset = 1;
      @(negedge clk);

      $display("\nSimulation completed with %d errors\n", errors);
      $stop;
   end // initial begin
endmodule
