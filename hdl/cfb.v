module cfb(
	input                        encryption,

	input [`BLK_S-1:0]           in_blk,
	input [`BLK_S-1:0]           out_blk,
	input [`IV_BITS-1:0]         iv,

	output reg [`BLK_S-1:0]      in_blk_next,
	output reg [`BLK_S-1:0]      out_blk_next,
	output reg [`IV_BITS-1:0]    iv_next
);

always @(*) begin
	if (encryption) begin
		in_blk_next = iv;
		out_blk_next = out_blk ^ in_blk;
		iv_next = out_blk_next;
	end else begin
		in_blk_next = iv;
		iv_next = in_blk;
		out_blk_next = out_blk ^ in_blk;
	end
end
endmodule
