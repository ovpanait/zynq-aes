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

module cbc(
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
		out_blk_next = out_blk;
		iv_next = out_blk;
	end else begin
		in_blk_next = in_blk;
		out_blk_next = iv ^ out_blk;
		iv_next = in_blk;
	end
end
endmodule

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


module ofb(
	input [`BLK_S-1:0]           in_blk,
	input [`BLK_S-1:0]           out_blk,
	input [`IV_BITS-1:0]         iv,

	output reg [`BLK_S-1:0]      in_blk_next,
	output reg [`BLK_S-1:0]      out_blk_next,
	output reg [`IV_BITS-1:0]    iv_next
);

always @(*) begin
	in_blk_next = iv;
	out_blk_next = out_blk ^ in_blk;
	iv_next = out_blk;
end
endmodule


module pcbc(
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
		out_blk_next = out_blk;
		iv_next = in_blk ^ out_blk;
	end else begin
		in_blk_next = in_blk;
		out_blk_next = iv ^ out_blk;
		iv_next = in_blk ^ out_blk_next;
	end
end
endmodule
