`include "aes.vh"

module aes_top(
	       input 		  clk,
	       input 		  reset,
	       input 		  en,

	       input [0:`KEY_S-1] key
	       );

   wire [0:`KEY_S-1] 		  round_key;
   wire 			  w_e;
   wire [0:`Nk-1] 		  round_no;
   wire 			  en_o;

   round_key round_key_gen(
			   .clk(clk),
			   .reset(reset),
			   .en(en),

			   .key(key),
			   .round_key(round_key),
			   .w_e(w_e),
			   .round_no(round_no),
			   .en_o(en_o)
			   );
   
   key_sram sram(
		 .clk(clk),

		 .addr(round_no),
		 .i_data(round_key),
		 .w_e(w_e)
		 );
endmodule
