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

localparam rsbox = {
        8'h7D, 8'h0C, 8'h21, 8'h55, 8'h63, 8'h14, 8'h69, 8'hE1,
        8'h26, 8'hD6, 8'h77, 8'hBA, 8'h7E, 8'h04, 8'h2B, 8'h17,
        8'h61, 8'h99, 8'h53, 8'h83, 8'h3C, 8'hBB, 8'hEB, 8'hC8,
        8'hB0, 8'hF5, 8'h2A, 8'hAE, 8'h4D, 8'h3B, 8'hE0, 8'hA0,
        8'hEF, 8'h9C, 8'hC9, 8'h93, 8'h9F, 8'h7A, 8'hE5, 8'h2D,
        8'h0D, 8'h4A, 8'hB5, 8'h19, 8'hA9, 8'h7F, 8'h51, 8'h60,
        8'h5F, 8'hEC, 8'h80, 8'h27, 8'h59, 8'h10, 8'h12, 8'hB1,
        8'h31, 8'hC7, 8'h07, 8'h88, 8'h33, 8'hA8, 8'hDD, 8'h1F,
        8'hF4, 8'h5A, 8'hCD, 8'h78, 8'hFE, 8'hC0, 8'hDB, 8'h9A,
        8'h20, 8'h79, 8'hD2, 8'hC6, 8'h4B, 8'h3E, 8'h56, 8'hFC,
        8'h1B, 8'hBE, 8'h18, 8'hAA, 8'h0E, 8'h62, 8'hB7, 8'h6F,
        8'h89, 8'hC5, 8'h29, 8'h1D, 8'h71, 8'h1A, 8'hF1, 8'h47,
        8'h6E, 8'hDF, 8'h75, 8'h1C, 8'hE8, 8'h37, 8'hF9, 8'hE2,
        8'h85, 8'h35, 8'hAD, 8'hE7, 8'h22, 8'h74, 8'hAC, 8'h96,
        8'h73, 8'hE6, 8'hB4, 8'hF0, 8'hCE, 8'hCF, 8'hF2, 8'h97,
        8'hEA, 8'hDC, 8'h67, 8'h4F, 8'h41, 8'h11, 8'h91, 8'h3A,
        8'h6B, 8'h8A, 8'h13, 8'h01, 8'h03, 8'hBD, 8'hAF, 8'hC1,
        8'h02, 8'h0F, 8'h3F, 8'hCA, 8'h8F, 8'h1E, 8'h2C, 8'hD0,
        8'h06, 8'h45, 8'hB3, 8'hB8, 8'h05, 8'h58, 8'hE4, 8'hF7,
        8'h0A, 8'hD3, 8'hBC, 8'h8C, 8'h00, 8'hAB, 8'hD8, 8'h90,
        8'h84, 8'h9D, 8'h8D, 8'hA7, 8'h57, 8'h46, 8'h15, 8'h5E,
        8'hDA, 8'hB9, 8'hED, 8'hFD, 8'h50, 8'h48, 8'h70, 8'h6C,
        8'h92, 8'hB6, 8'h65, 8'h5D, 8'hCC, 8'h5C, 8'hA4, 8'hD4,
        8'h16, 8'h98, 8'h68, 8'h86, 8'h64, 8'hF6, 8'hF8, 8'h72,
        8'h25, 8'hD1, 8'h8B, 8'h6D, 8'h49, 8'hA2, 8'h5B, 8'h76,
        8'hB2, 8'h24, 8'hD9, 8'h28, 8'h66, 8'hA1, 8'h2E, 8'h08,
        8'h4E, 8'hC3, 8'hFA, 8'h42, 8'h0B, 8'h95, 8'h4C, 8'hEE,
        8'h3D, 8'h23, 8'hC2, 8'hA6, 8'h32, 8'h94, 8'h7B, 8'h54,
        8'hCB, 8'hE9, 8'hDE, 8'hC4, 8'h44, 8'h43, 8'h8E, 8'h34,
        8'h87, 8'hFF, 8'h2F, 8'h9B, 8'h82, 8'h39, 8'hE3, 8'h7C,
        8'hFB, 8'hD7, 8'hF3, 8'h81, 8'h9E, 8'hA3, 8'h40, 8'hBF,
        8'h38, 8'hA5, 8'h36, 8'h30, 8'hD5, 8'h6A, 8'h09, 8'h52 };

// Helper functions
function [0:`BYTE_S-1] get_byte;
   input [0:`WORD_S-1] 		 word;
   input [0:2] 			 byte_no;
   begin
      get_byte = word[byte_no*`BYTE_S +: `BYTE_S];
   end
endfunction

function [0:`BLK_S-1] blk_get_byte;
   input [0:`BLK_S-1] 		 blk;
   input [0:`BLK_S/`BYTE_S-1] 	 byte_no;
   begin
      blk_get_byte = blk[byte_no*`BYTE_S +: `BYTE_S];
   end
endfunction

function [0:`WORD_S-1] get_word;
   input [0:`BLK_S-1] 		 blk;
   input [0:2] 			 word_no;
   begin
      get_word = blk[word_no*`WORD_S +: `WORD_S];
   end
endfunction

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

// Cipher functions

// subBytes
function [0:`BLK_S-1] sub_bytes;
   input [0:`BLK_S-1] blk;

   integer 	      i;
   begin
      for (i = 0; i < `BLK_S / `BYTE_S; i=i+1) begin
	 sub_bytes[i*`BYTE_S +: `BYTE_S] = get_sbox(blk[i*`BYTE_S +: `BYTE_S]);
      end
   end
endfunction

// shiftRows
function [0:`BLK_S-1] shift_rows;
   input [0:`BLK_S-1] blk;

   integer 	      i, j, k;
   begin
      for (j = 0; j < `BLK_S / `BYTE_S; j=j+4) begin
	 for (i=j, k=j; i < `BLK_S / `BYTE_S; i=i+1, k=k+5)
	   shift_rows[i*`BYTE_S +: `BYTE_S] = blk_get_byte(blk, k % 16);
      end
   end
endfunction

// mixColumns
function [0:`BYTE_S-1] mul2;
   input [0:`BYTE_S-1] op;
   begin
      mul2 = ((op << 1) ^ (((op >> 7) & 1'b1) * 8'h1b));
   end
endfunction // mul2

function [0:`BYTE_S-1] mul3;
   input [0:`BYTE_S-1] op;
   begin
      mul3 = mul2(op) ^ op;
   end
endfunction // mul3

function [0:`WORD_S-1] mix_word;
   input [0:`WORD_S-1] word;

   reg [0:`BYTE_S-1]   byte0;
   reg [0:`BYTE_S-1]   byte1;
   reg [0:`BYTE_S-1]   byte2;
   reg [0:`BYTE_S-1]   byte3;
   begin
      byte0 = get_byte(word, 0);
      byte1 = get_byte(word, 1);
      byte2 = get_byte(word, 2);
      byte3 = get_byte(word, 3);

      mix_word[0*`BYTE_S +: `BYTE_S] = mul2(byte0) ^ mul3(byte1) ^ byte2 ^ byte3;
      mix_word[1*`BYTE_S +: `BYTE_S] = byte0 ^ mul2(byte1) ^ mul3(byte2) ^ byte3;
      mix_word[2*`BYTE_S +: `BYTE_S] = byte0 ^ byte1 ^ mul2(byte2) ^ mul3(byte3);
      mix_word[3*`BYTE_S +: `BYTE_S] = mul3(byte0) ^ byte1 ^ byte2 ^mul2(byte3);
   end
endfunction

function [0:`BLK_S-1] mix_cols;
   input [0:`BLK_S-1] blk;
   integer 	      i;
   begin
      for (i = 0; i < `BLK_S / `WORD_S; i=i+1) begin
	 mix_cols[i*`WORD_S +: `WORD_S] = mix_word(get_word(blk,i));
      end
   end
endfunction

// Decipher functions
function [0:`BYTE_S-1] get_rsbox;
   input [0:`BYTE_S-1] index;
   begin
      get_rsbox = rsbox[index*`BYTE_S +: `BYTE_S];
   end
endfunction

function [0:`BLK_S-1] inv_sub_bytes;
   input [0:`BLK_S-1] blk;

   integer 	      i;
   begin
      for (i = 0; i < `BLK_S / `BYTE_S; i=i+1) begin
	 inv_sub_bytes[i*`BYTE_S +: `BYTE_S] = get_rsbox(blk[i*`BYTE_S +: `BYTE_S]);
      end
   end
endfunction

function [0:`BYTE_S-1] xtime;
        input [0:`BYTE_S-1] x;
        begin
                xtime = ((x<<1) ^ (((x>>7) & 1'b1) * 8'h1b));
        end
endfunction

function [0:`BYTE_S-1] multiply;
        input [0:`BYTE_S-1] x;
        input [0:`BYTE_S-1] y;
        begin
        multiply = (  ((y & 1) * x) ^
                ((y>>1 & 1) * xtime(x)) ^
                ((y>>2 & 1) * xtime(xtime(x))) ^
                ((y>>3 & 1) * xtime(xtime(xtime(x)))) ^
                ((y>>4 & 1) * xtime(xtime(xtime(xtime(x))))));
        end
endfunction

function [0:`WORD_S-1] inv_mix_word;
   input [0:`WORD_S-1] word;

   reg [0:`BYTE_S-1]   byte0;
   reg [0:`BYTE_S-1]   byte1;
   reg [0:`BYTE_S-1]   byte2;
   reg [0:`BYTE_S-1]   byte3;
   begin
      byte0 = get_byte(word, 0);
      byte1 = get_byte(word, 1);
      byte2 = get_byte(word, 2);
      byte3 = get_byte(word, 3);

      inv_mix_word[0*`BYTE_S +: `BYTE_S] = multiply(byte0, 8'h0e) ^ multiply(byte1, 8'h0b) ^ multiply(byte2, 8'h0d) ^ multiply(byte3, 8'h09);
      inv_mix_word[1*`BYTE_S +: `BYTE_S] = multiply(byte0, 8'h09) ^ multiply(byte1, 8'h0e) ^ multiply(byte2, 8'h0b) ^ multiply(byte3, 8'h0d);
      inv_mix_word[2*`BYTE_S +: `BYTE_S] = multiply(byte0, 8'h0d) ^ multiply(byte1, 8'h09) ^ multiply(byte2, 8'h0e) ^ multiply(byte3, 8'h0b);
      inv_mix_word[3*`BYTE_S +: `BYTE_S] = multiply(byte0, 8'h0b) ^ multiply(byte1, 8'h0d) ^ multiply(byte2, 8'h09) ^ multiply(byte3, 8'h0e);
   end
endfunction

function [0:`BLK_S-1] inv_mix_cols;
   input [0:`BLK_S-1] blk;
   integer 	      i;
   begin
      for (i = 0; i < `BLK_S / `WORD_S; i=i+1) begin
	 inv_mix_cols[i*`WORD_S +: `WORD_S] = inv_mix_word(get_word(blk,i));
      end
   end
endfunction

function [0:`BLK_S-1] inv_shift_rows;
   input [0:`BLK_S-1] blk;

   integer 	      i, j, k;
   begin
      for (j = 0; j < `BLK_S / `BYTE_S; j=j+4) begin
	 for (i=j, k=j; i < `BLK_S / `BYTE_S; i=i+1, k=k+13)
	   inv_shift_rows[i*`BYTE_S +: `BYTE_S] = blk_get_byte(blk, k % 16);
      end
   end
endfunction
