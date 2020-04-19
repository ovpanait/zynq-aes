// ---------- ECB ----------
module ecb(
	input [`BLK_S-1:0]           in_blk,
	input [`BLK_S-1:0]           out_blk,

	input                        aes_alg_done,

	output reg                   ecb_op_done,
	output reg [`BLK_S-1:0]      in_blk_next,
	output reg [`BLK_S-1:0]      out_blk_next
);

always @(*) begin
	in_blk_next = in_blk;
	out_blk_next = out_blk;
	ecb_op_done = aes_alg_done;
end
endmodule

// ---------- CBC ----------
module cbc(
	input                        encryption,
	input                        decryption,

	input                        aes_alg_done,

	input [`BLK_S-1:0]           in_blk,
	input [`BLK_S-1:0]           out_blk,
	input [`IV_BITS-1:0]         iv,

	output reg                   cbc_op_done,
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

	cbc_op_done = aes_alg_done;
end
endmodule

// ---------- CTR ----------
module ctr(
	input [`BLK_S-1:0]           in_blk,
	input [`BLK_S-1:0]           out_blk,
	input [`IV_BITS-1:0]         iv,

	input                        aes_alg_done,

	output reg                   ctr_op_done,
	output reg [`BLK_S-1:0]      in_blk_next,
	output reg [`BLK_S-1:0]      out_blk_next,
	output reg [`IV_BITS-1:0]    iv_next
);

always @(*) begin
	in_blk_next = iv;
	out_blk_next = out_blk ^ in_blk;
	iv_next = iv + 1'b1;

	ctr_op_done = aes_alg_done;
end
endmodule

// ---------- CFB ----------
module cfb(
	input                        encryption,

	input [`BLK_S-1:0]           in_blk,
	input [`BLK_S-1:0]           out_blk,
	input [`IV_BITS-1:0]         iv,

	input                        aes_alg_done,

	output reg                   cfb_op_done,
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

	cfb_op_done = aes_alg_done;
end
endmodule

// ---------- OFB ----------
module ofb(
	input [`BLK_S-1:0]           in_blk,
	input [`BLK_S-1:0]           out_blk,
	input [`IV_BITS-1:0]         iv,

	input                        aes_alg_done,

	output reg                   ofb_op_done,
	output reg [`BLK_S-1:0]      in_blk_next,
	output reg [`BLK_S-1:0]      out_blk_next,
	output reg [`IV_BITS-1:0]    iv_next
);

always @(*) begin
	in_blk_next = iv;
	out_blk_next = out_blk ^ in_blk;
	iv_next = out_blk;

	ofb_op_done = aes_alg_done;
end
endmodule

// ---------- PCBC ----------
module pcbc(
	input                        encryption,
	input                        decryption,

	input [`BLK_S-1:0]           in_blk,
	input [`BLK_S-1:0]           out_blk,
	input [`IV_BITS-1:0]         iv,

	input                        aes_alg_done,

	output reg                   pcbc_op_done,
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

	pcbc_op_done = aes_alg_done;
end
endmodule
