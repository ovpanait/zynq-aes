module ecb(
	input [`BLK_S-1:0]           in_blk,
	input [`BLK_S-1:0]           out_blk,

	output reg [`BLK_S-1:0]      in_blk_next,
	output reg [`BLK_S-1:0]      out_blk_next
);

always @(*) begin
	in_blk_next = in_blk;
	out_blk_next = out_blk;
end

endmodule
