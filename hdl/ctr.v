module ctr(
	input [`BLK_S-1:0]           in_blk,
	input [`BLK_S-1:0]           out_blk,
	input [`IV_BITS-1:0]         iv,

	output reg [`BLK_S-1:0]      in_blk_next,
	output reg [`BLK_S-1:0]      out_blk_next,
	output reg [`IV_BITS-1:0]    iv_next
);

function [`IV_BITS-1:0] reverse_iv(input [`IV_BITS-1:0] iv);
	integer i;

	for (i = 0; i < `IV_BITS / `BYTE_S; i=i+1)
		reverse_iv[i*`BYTE_S +: `BYTE_S] = iv[`IV_BITS - (i+1)*`BYTE_S +: `BYTE_S];
endfunction

always @(*) begin
	iv_next = reverse_iv(reverse_iv(iv) + 1'b1);
	in_blk_next = iv;
	out_blk_next = out_blk ^ in_blk;
end

endmodule
