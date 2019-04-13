`include "aes.vh"

module cipher(
	      input 		      clk,
	      input 		      reset,
	      input 		      en,

	      input [0:`BLK_S-1]      plaintext,
	      input [0:`KEY_S-1]      key,

	      output reg [0:`BLK_S-1] ciphertext,
	      output reg [0:`Nk-1]    round_no,
	      output reg 	      r_e,
	      output reg 	      en_o
	      );

   localparam IDLE = 2'b0,
     FIRST_ROUND = 2'b10,
     AES_ROUND = 2'b01,
     INIT_SRAM =2'b11;

   reg [0:1] 			      fsm_state;

   reg [0:`KEY_S-1] 		      aes_state_sub_bytes;
   reg [0:`KEY_S-1] 		      aes_state_shift_rows;
   reg [0:`KEY_S-1] 		      aes_state_mix_cols;
   reg [0:`KEY_S-1] 		      aes_state_add_rkey;

`include "aes_functions.vh"

   // AES cipher round
   always @(*) begin
      aes_state_sub_bytes = sub_bytes(ciphertext);
      aes_state_shift_rows = shift_rows(aes_state_sub_bytes);
      aes_state_mix_cols = (round_no == `Nr + 1) ? aes_state_shift_rows : mix_cols(aes_state_shift_rows);
      aes_state_add_rkey = aes_state_mix_cols ^ key;
   end

   always @(posedge clk) begin
      if (reset == 1'b1) begin
	 ciphertext <= {`BLK_S{1'b0}};
      round_no <= 4'b0;
      r_e <= 1'b0;
      en_o <= 1'b0;
   end
      else begin
	 case (fsm_state)
	   IDLE:
	     begin
		en_o <= 1'b0;
		r_e <= 1'b0;

		if (en == 1'b1) begin
		   ciphertext <= plaintext;

		   round_no <= 1'b0;
		   r_e <= 1'b1;

		   fsm_state <= INIT_SRAM;
		end
	     end
	   INIT_SRAM:
	     begin
		// one clock delay to start reading from SRAM
		round_no <= round_no + 1'b1;
		r_e <= 1'b1;

		fsm_state <= FIRST_ROUND;
	     end
	   FIRST_ROUND:
	     begin
		ciphertext <= ciphertext ^ key;

		round_no <= round_no + 1'b1;
		r_e <= 1'b1;

		fsm_state <= AES_ROUND;
	     end
	   AES_ROUND:
	     begin
		ciphertext <= aes_state_add_rkey;
		round_no <= round_no + 1'b1;
		r_e <= 1'b1;

		if (round_no == `Nr + 1) begin
		   fsm_state <= IDLE;
		   en_o <= 1'b1;
		end
	     end
	   default:
	     begin
		fsm_state <= IDLE;
	     end
	 endcase
      end
   end
endmodule
