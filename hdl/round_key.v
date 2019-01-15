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

   localparam  sbox = {
		       8'h16, 8'hBB, 8'h54, 8'hB0,
		       8'h0F, 8'h2D, 8'h99, 8'h41,
		       8'h68, 8'h42, 8'hE6, 8'hBF,
		       8'h0D, 8'h89, 8'hA1, 8'h8C,
		       8'hDF, 8'h28, 8'h55, 8'hCE,
		       8'hE9, 8'h87, 8'h1E, 8'h9B,
		       8'h94, 8'h8E, 8'hD9, 8'h69,
		       8'h11, 8'h98, 8'hF8, 8'hE1,
		       8'h9E, 8'h1D, 8'hC1, 8'h86,
		       8'hB9, 8'h57, 8'h35, 8'h61,
		       8'h0E, 8'hF6, 8'h03, 8'h48,
		       8'h66, 8'hB5, 8'h3E, 8'h70,
		       8'h8A, 8'h8B, 8'hBD, 8'h4B,
		       8'h1F, 8'h74, 8'hDD, 8'hE8,
		       8'hC6, 8'hB4, 8'hA6, 8'h1C,
		       8'h2E, 8'h25, 8'h78, 8'hBA,
		       8'h08, 8'hAE, 8'h7A, 8'h65,
		       8'hEA, 8'hF4, 8'h56, 8'h6C,
		       8'hA9, 8'h4E, 8'hD5, 8'h8D,
		       8'h6D, 8'h37, 8'hC8, 8'hE7,
		       8'h79, 8'hE4, 8'h95, 8'h91,
		       8'h62, 8'hAC, 8'hD3, 8'hC2,
		       8'h5C, 8'h24, 8'h06, 8'h49,
		       8'h0A, 8'h3A, 8'h32, 8'hE0,
		       8'hDB, 8'h0B, 8'h5E, 8'hDE,
		       8'h14, 8'hB8, 8'hEE, 8'h46,
		       8'h88, 8'h90, 8'h2A, 8'h22,
		       8'hDC, 8'h4F, 8'h81, 8'h60,
		       8'h73, 8'h19, 8'h5D, 8'h64,
		       8'h3D, 8'h7E, 8'hA7, 8'hC4,
		       8'h17, 8'h44, 8'h97, 8'h5F,
		       8'hEC, 8'h13, 8'h0C, 8'hCD,
		       8'hD2, 8'hF3, 8'hFF, 8'h10,
		       8'h21, 8'hDA, 8'hB6, 8'hBC,
		       8'hF5, 8'h38, 8'h9D, 8'h92,
		       8'h8F, 8'h40, 8'hA3, 8'h51,
		       8'hA8, 8'h9F, 8'h3C, 8'h50,
		       8'h7F, 8'h02, 8'hF9, 8'h45,
		       8'h85, 8'h33, 8'h4D, 8'h43,
		       8'hFB, 8'hAA, 8'hEF, 8'hD0,
		       8'hCF, 8'h58, 8'h4C, 8'h4A,
		       8'h39, 8'hBE, 8'hCB, 8'h6A,
		       8'h5B, 8'hB1, 8'hFC, 8'h20,
		       8'hED, 8'h00, 8'hD1, 8'h53,
		       8'h84, 8'h2F, 8'hE3, 8'h29,
		       8'hB3, 8'hD6, 8'h3B, 8'h52,
		       8'hA0, 8'h5A, 8'h6E, 8'h1B,
		       8'h1A, 8'h2C, 8'h83, 8'h09,
		       8'h75, 8'hB2, 8'h27, 8'hEB,
		       8'hE2, 8'h80, 8'h12, 8'h07,
		       8'h9A, 8'h05, 8'h96, 8'h18,
		       8'hC3, 8'h23, 8'hC7, 8'h04,
		       8'h15, 8'h31, 8'hD8, 8'h71,
		       8'hF1, 8'hE5, 8'hA5, 8'h34,
		       8'hCC, 8'hF7, 8'h3F, 8'h36,
		       8'h26, 8'h93, 8'hFD, 8'hB7,
		       8'hC0, 8'h72, 8'hA4, 8'h9C,
		       8'hAF, 8'hA2, 8'hD4, 8'hAD,
		       8'hF0, 8'h47, 8'h59, 8'hFA,
		       8'h7D, 8'hC9, 8'h82, 8'hCA,
		       8'h76, 8'hAB, 8'hD7, 8'hFE,
		       8'h2B, 8'h67, 8'h01, 8'h30,
		       8'hC5, 8'h6F, 8'h6B, 8'hF2,
		       8'h7B, 8'h77, 8'h7C, 8'h63
		       };


   localparam rcon = {
		      8'h36, 8'h1B, 8'h80,
		      8'h40, 8'h20, 8'h10, 8'h08,
		      8'h04, 8'h02, 8'h01, 8'h8D
		      };

   parameter IDLE = 1'b0, AES_ROUND = 1'b1;

   genvar 				 i;
   wire [0:`WORD_S-1] 			 prev_key_arr[0:`Nk];

   wire [0:`WORD_S-1] 			 subbytes_tmp;
   wire [0:`BYTE_S-1] 			 g0;
   wire [0:`WORD_S-1] 			 g;

   wire [0:`WORD_S-1] 			 round_key_tmp_arr[0:`Nk];

   reg 					 state;

   // Helper functions
   function [0:`BYTE_S-1] get_byte;
      input [0:`WORD_S-1] 		 word;
      input [0:2] 			 byte_no;
      begin
	 get_byte = word[byte_no*`BYTE_S +: `BYTE_S];
      end
   endfunction
   //

   // AES specific functions
   function [0:`BYTE_S-1] get_sbox;
      input [0:`BYTE_S-1] index;
      begin
	 get_sbox = sbox[index*`BYTE_S +: `BYTE_S];
      end
   endfunction

   function [0:`BYTE_S-1] get_rcon;
      input [0:`BYTE_S-1] index;
      begin
	 get_rcon = rcon[index*`BYTE_S +: `BYTE_S];
      end
   endfunction
   //

   generate
      for (i=0; i < `Nk; i=i+1) begin
	 assign prev_key_arr[i] = round_key[i*`WORD_S +: `WORD_S];
      end
   endgenerate

   assign subbytes_tmp = {
			  get_sbox(get_byte(prev_key_arr[`Nk-1], 1)),
			  get_sbox(get_byte(prev_key_arr[`Nk-1], 2)),
			  get_sbox(get_byte(prev_key_arr[`Nk-1], 3)),
			  get_sbox(get_byte(prev_key_arr[`Nk-1], 0))
			  };

   assign g0 = get_byte(subbytes_tmp, 0) ^ get_rcon(round_no + 1'b1);
   assign g = {
	       g0,
	       get_byte(subbytes_tmp, 1),
	       get_byte(subbytes_tmp, 2),
	       get_byte(subbytes_tmp, 3)
	       };

   assign round_key_tmp_arr[0] = g ^ prev_key_arr[0];
   assign round_key_tmp_arr[1] = round_key_tmp_arr[0] ^ prev_key_arr[1];
   assign round_key_tmp_arr[2] = round_key_tmp_arr[1] ^ prev_key_arr[2];
   assign round_key_tmp_arr[3] = round_key_tmp_arr[2] ^ prev_key_arr[3];

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
