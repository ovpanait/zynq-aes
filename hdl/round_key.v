`include "aes.vh"

module round_key(
		 input 			 clk,
		 input 			 reset,
		 input 			 en,

		 input [0:`KEY_S-1] 	 key,

		 output reg [0:`KEY_S-1] round_key,
		 output reg 		 w_e,
		 output reg [0:3] 	 round_no,

		 output reg 		 en_o
		 );

   parameter IDLE = 1'b0, AES_ROUND = 1'b1;

   genvar 				 i;
   wire [0:`WORD_S-1] 			 prev_key_arr[0:`Nk];

   reg [0:`WORD_S-1] 			 subbytes_tmp;
   reg [0:`BYTE_S-1] 			 g0;
   reg [0:`WORD_S-1] 			 g;

   reg [0:`WORD_S-1] 			 round_key_tmp_arr[0:`Nk];

   reg 					 state;

`include "aes_functions.vh"

   generate
      for (i=0; i < `Nk; i=i+1) begin
	 assign prev_key_arr[i] = round_key[i*`WORD_S +: `WORD_S];
      end
   endgenerate

   always @(*) begin
      subbytes_tmp = {
		      get_sbox(get_byte(prev_key_arr[`Nk-1], 1)),
		      get_sbox(get_byte(prev_key_arr[`Nk-1], 2)),
		      get_sbox(get_byte(prev_key_arr[`Nk-1], 3)),
		      get_sbox(get_byte(prev_key_arr[`Nk-1], 0))
		      };

      g0 = get_byte(subbytes_tmp, 0) ^ get_rcon(round_no + 1'b1);
      g = {
	   g0,
	   get_byte(subbytes_tmp, 1),
	   get_byte(subbytes_tmp, 2),
	   get_byte(subbytes_tmp, 3)
	   };

      round_key_tmp_arr[0] = g ^ prev_key_arr[0];
      round_key_tmp_arr[1] = round_key_tmp_arr[0] ^ prev_key_arr[1];
      round_key_tmp_arr[2] = round_key_tmp_arr[1] ^ prev_key_arr[2];
      round_key_tmp_arr[3] = round_key_tmp_arr[2] ^ prev_key_arr[3];
   end

   always @(posedge clk) begin
      if (reset == 1'b1) begin
	 round_key <= {`KEY_S{1'b0}};
      round_no <= 1'b0;

      en_o <= 1'b0;
      w_e <= 1'b0;
      state <= IDLE;
   end
      else begin
	 w_e <= 1'b0;

	 case (state)
	   IDLE:
	     begin
		en_o <= 1'b0;

		if (en == 1'b1) begin
		   round_key <= key;
		   round_no <= 1'b0;
		   w_e <= 1'b1;
		   state <= AES_ROUND;
		end
	     end
	   AES_ROUND:
	     begin
		// Compute AES round
		en_o <= 1'b0;
		w_e <= 1'b1;

		round_key <= {
			      round_key_tmp_arr[0],
			      round_key_tmp_arr[1],
			      round_key_tmp_arr[2],
			      round_key_tmp_arr[3]
			      };
		round_no <= round_no + 1'b1;

		if (round_no == `Nr - 1'b1) begin
		   en_o <= 1'b1;
		   state <= IDLE;
		end
	     end
	 endcase
      end
   end
endmodule
