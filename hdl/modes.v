// ---------- ECB ----------
module ecb(
	input [`BLK_S-1:0]           data_blk,

	input [`BLK_S-1:0]           aes_alg_out_blk,
	input                        aes_alg_done,
	output reg [`BLK_S-1:0]      aes_alg_in_blk,

	output reg [`BLK_S-1:0]      ecb_out_blk,
	output reg                   ecb_op_done
);

always @(*) begin
	aes_alg_in_blk = data_blk;
	ecb_out_blk = aes_alg_out_blk;
	ecb_op_done = aes_alg_done;
end
endmodule

// ---------- CBC ----------
module cbc(
	input                        encryption,

	input [`BLK_S-1:0]           data_blk,

	input [`IV_BITS-1:0]         iv,
	output reg [`IV_BITS-1:0]    iv_next,

	input [`BLK_S-1:0]           aes_alg_out_blk,
	input                        aes_alg_done,
	output reg [`BLK_S-1:0]      aes_alg_in_blk,

	output reg [`BLK_S-1:0]      cbc_out_blk,
	output reg                   cbc_op_done
);

always @(*) begin
	if (encryption) begin
		aes_alg_in_blk = data_blk ^ iv;
		cbc_out_blk = aes_alg_out_blk;
		iv_next = aes_alg_out_blk;
	end else begin
		aes_alg_in_blk = data_blk;
		cbc_out_blk = iv ^ aes_alg_out_blk;
		iv_next = data_blk;
	end

	cbc_op_done = aes_alg_done;
end
endmodule

// ---------- CTR ----------
module ctr(
	input [`BLK_S-1:0]           data_blk,

	input [`IV_BITS-1:0]         iv,
	output reg [`IV_BITS-1:0]    iv_next,

	input [`BLK_S-1:0]           aes_alg_out_blk,
	input                        aes_alg_done,
	output reg [`BLK_S-1:0]      aes_alg_in_blk,

	output reg                   ctr_op_done,
	output reg [`BLK_S-1:0]      ctr_out_blk
);

always @(*) begin
	aes_alg_in_blk = iv;
	ctr_out_blk = aes_alg_out_blk ^ data_blk;
	iv_next = iv + 1'b1;

	ctr_op_done = aes_alg_done;
end
endmodule

// ---------- CFB ----------
module cfb(
	input                        encryption,

	input [`BLK_S-1:0]           data_blk,

	input [`IV_BITS-1:0]         iv,
	output reg [`IV_BITS-1:0]    iv_next,

	input [`BLK_S-1:0]           aes_alg_out_blk,
	input                        aes_alg_done,
	output reg [`BLK_S-1:0]      aes_alg_in_blk,

	output reg                   cfb_op_done,
	output reg [`BLK_S-1:0]      cfb_out_blk
);

always @(*) begin
	if (encryption) begin
		aes_alg_in_blk = iv;
		cfb_out_blk = aes_alg_out_blk ^ data_blk;
		iv_next = cfb_out_blk;
	end else begin
		aes_alg_in_blk = iv;
		iv_next = data_blk;
		cfb_out_blk = aes_alg_out_blk ^ data_blk;
	end

	cfb_op_done = aes_alg_done;
end
endmodule

// ---------- OFB ----------
module ofb(
	input [`BLK_S-1:0]           data_blk,

	input [`IV_BITS-1:0]         iv,
	output reg [`IV_BITS-1:0]    iv_next,

	input [`BLK_S-1:0]           aes_alg_out_blk,
	output reg [`BLK_S-1:0]      aes_alg_in_blk,
	input                        aes_alg_done,

	output reg                   ofb_op_done,
	output reg [`BLK_S-1:0]      ofb_out_blk
);

always @(*) begin
	aes_alg_in_blk = iv;
	ofb_out_blk = aes_alg_out_blk ^ data_blk;
	iv_next = aes_alg_out_blk;

	ofb_op_done = aes_alg_done;
end
endmodule

// ---------- PCBC ----------
module pcbc(
	input                        encryption,

	input [`BLK_S-1:0]           data_blk,

	input [`IV_BITS-1:0]         iv,
	output reg [`IV_BITS-1:0]    iv_next,

	output reg [`BLK_S-1:0]      aes_alg_in_blk,
	input [`BLK_S-1:0]           aes_alg_out_blk,
	input                        aes_alg_done,

	output reg                   pcbc_op_done,
	output reg [`BLK_S-1:0]      pcbc_out_blk
);

always @(*) begin
	if (encryption) begin
		aes_alg_in_blk = data_blk ^ iv;
		pcbc_out_blk = aes_alg_out_blk;
		iv_next = data_blk ^ aes_alg_out_blk;
	end else begin
		aes_alg_in_blk = data_blk;
		pcbc_out_blk = iv ^ aes_alg_out_blk;
		iv_next = data_blk ^ pcbc_out_blk;
	end

	pcbc_op_done = aes_alg_done;
end
endmodule
