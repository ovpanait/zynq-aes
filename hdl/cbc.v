module cbc(
	input                        clk,
	input                        reset,
	input                        crypto_done,

	input                        encryption,
	input                        decryption,

	input [`BLK_S-1:0]           in_blk,
	input [`BLK_S-1:0]           out_blk,
	input [`IV_BITS-1:0]         iv,

	output reg [`BLK_S-1:0]      in_blk_next,
	output reg [`BLK_S-1:0]      out_blk_next,
	output reg [`IV_BITS-1:0]    iv_next
);

always @(*) begin
	if (encryption) begin
		in_blk_next = in_blk ^ iv;
		if (crypto_done) begin
			out_blk_next = out_blk;
			iv_next = out_blk;
		end
	end

	if (decryption) begin
		in_blk_next = in_blk;
		if (crypto_done) begin
			out_blk_next = iv ^ out_blk;
			iv_next = in_blk;
		end
	end
end

endmodule
