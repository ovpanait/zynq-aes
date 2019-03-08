module block_ram #
  (
   parameter integer ADDR_WIDTH = 9,
   parameter integer DATA_WIDTH = 128, 
   parameter integer DEPTH = 512          // 8192 bytes
   ) 
   (
    input 			clk,

    input [0:DATA_WIDTH-1] 	i_data,
    input [0:ADDR_WIDTH-1] 	addr,
    input 			w_e,
    input 			r_e,

    output reg [0:DATA_WIDTH-1] o_data
    );

   reg [0:DATA_WIDTH-1] 	sram [0:DEPTH-1];

   always @ (posedge clk) begin
      if (w_e)
        sram[addr] <= i_data;
      else if (r_e)
        o_data <= sram[addr];
   end
endmodule
