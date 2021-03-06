// ---------- ECB ----------
module ecb(
	input                        clk,
	input                        reset,

	input                        encrypt_flag,
	input                        decrypt_flag,

	input                        controller_out_ready,
	input                        last_blk,

	input [`BLK_S-1:0]           ecb_in_blk,
	input                        ecb_in_tvalid,
	output reg                   ecb_in_tready,

	output reg [`BLK_S-1:0]      aes_alg_in_blk,
	output reg                   aes_alg_en_cipher,
	output reg                   aes_alg_en_decipher,

	input [`BLK_S-1:0]           aes_alg_out_blk,
	input                        aes_alg_done,
	input                        aes_alg_busy,

	output reg                   ecb_out_store_blk,
	output reg [`BLK_S:0]        ecb_out_blk,

	output reg                   ecb_done
);

reg  [`BLK_S-1:0] in_blk;

reg  aes_alg_start;

reg  out_transfer;
reg  in_transfer;
reg  fill;

always @(*) begin
	ecb_in_tready = ~aes_alg_busy && controller_out_ready &&
	                        ~aes_alg_start;

	in_transfer = (ecb_in_tvalid && ecb_in_tready);

	aes_alg_in_blk = in_blk;
	aes_alg_en_cipher = encrypt_flag && aes_alg_start;
	aes_alg_en_decipher = decrypt_flag && aes_alg_start;

	ecb_out_blk = {last_blk, aes_alg_out_blk};
	ecb_out_store_blk = aes_alg_done;
	ecb_done = last_blk && ecb_out_store_blk;
end

always @(posedge clk) begin
	if (in_transfer) begin
		in_blk <= ecb_in_blk;
	end
end

always @(posedge clk) begin
	if (reset) begin
		aes_alg_start <= 1'b0;
	end else begin
		aes_alg_start <= controller_out_ready && in_transfer;
	end
end

//`define ECB_SIM_VERBOSE
`ifdef ECB_SIM_VERBOSE
always @(posedge clk) begin
	if (in_transfer) begin
		$display("ECB: input blk: %H", ecb_in_blk);
	end

	if (fill) begin
		$display("ECB: output blk: %H", aes_alg_out_blk);
	end
end
`endif
endmodule

// ---------- CBC ----------
module cbc(
	input                        clk,
	input                        reset,

	input                        encrypt_flag,
	input                        decrypt_flag,

	input                        controller_out_ready,
	input                        last_blk,

	input [`BLK_S-1:0]           cbc_in_blk,
	input                        cbc_in_tvalid,
	output reg                   cbc_in_tready,

	output reg [`BLK_S-1:0]      aes_alg_in_blk,
	output reg                   aes_alg_en_cipher,
	output reg                   aes_alg_en_decipher,

	input [`BLK_S-1:0]           aes_alg_out_blk,
	input                        aes_alg_done,
	input                        aes_alg_busy,

	output reg                   cbc_out_store_blk,
	output reg [`BLK_S:0]        cbc_out_blk,

	output reg                   cbc_done
);

reg  [`IV_BITS-1:0] iv;
reg  iv_ready;

reg  [`BLK_S-1:0] in_blk;

reg  aes_alg_start;

reg  out_transfer;
reg  in_transfer;
reg  fill;

always @(*) begin
	cbc_in_tready = ~aes_alg_busy && controller_out_ready &&
	                        ~aes_alg_start;

	in_transfer = (cbc_in_tvalid && cbc_in_tready);

	aes_alg_in_blk = encrypt_flag ? in_blk ^ iv : in_blk;
	aes_alg_en_cipher = encrypt_flag && aes_alg_start;
	aes_alg_en_decipher = decrypt_flag && aes_alg_start;

	cbc_out_blk = encrypt_flag ?
	              {last_blk, aes_alg_out_blk} :
	              {last_blk, iv ^ aes_alg_out_blk};
	cbc_out_store_blk = aes_alg_done;
	cbc_done = last_blk && cbc_out_store_blk;
end

always @(posedge clk) begin
	if (reset) begin
		iv_ready <= 1'b0;
		iv <= {`IV_BITS{1'b0}};
	end else begin
		if (in_transfer && !iv_ready) begin
			iv_ready <= 1'b1;
			iv <= cbc_in_blk;
		end

		// At the end of an AES operation, update IV depending on
		// encryption/decryption flag
		if (encrypt_flag && aes_alg_done)
			iv <= aes_alg_out_blk;

		if (decrypt_flag && aes_alg_done)
			iv <= in_blk;

		if (cbc_done)
			iv_ready <= 1'b0;
	end
end

always @(posedge clk) begin
	if (in_transfer) begin
		in_blk <= cbc_in_blk;
	end
end

always @(posedge clk) begin
	if (reset) begin
		aes_alg_start <= 1'b0;
	end else begin
		aes_alg_start <= controller_out_ready && in_transfer
		                           && iv_ready;
	end
end

//`define CBC_SIM_VERBOSE
`ifdef CBC_SIM_VERBOSE
always @(posedge clk) begin
	if (in_transfer) begin
		$display("CBC: input blk: %H", cbc_in_blk);
	end

	if (in_transfer && !iv_ready) begin
		$display("CBC: iv: %H", cbc_in_blk);
	end

	if (cbc_out_store_blk) begin
		$display("CBC: output blk: %H", aes_alg_out_blk);
	end
end
`endif
endmodule

// ---------- CTR ----------
module ctr(
	input                        clk,
	input                        reset,

	input                        encrypt_flag,
	input                        decrypt_flag,

	input                        controller_out_ready,
	input                        last_blk,

	input [`BLK_S-1:0]           ctr_in_blk,
	input                        ctr_in_tvalid,
	output reg                   ctr_in_tready,

	output reg [`BLK_S-1:0]      aes_alg_in_blk,
	output reg                   aes_alg_en_cipher,
	output reg                   aes_alg_en_decipher,

	input [`BLK_S-1:0]           aes_alg_out_blk,
	input                        aes_alg_done,
	input                        aes_alg_busy,

	output reg                   ctr_out_store_blk,
	output reg [`BLK_S:0]        ctr_out_blk,

	output reg                   ctr_done
);

reg  [`IV_BITS-1:0] iv;
reg  iv_ready;

reg  [`BLK_S-1:0] in_blk;

reg  aes_alg_start;

reg  out_transfer;
reg  in_transfer;
reg  fill;

always @(*) begin
	ctr_in_tready = ~aes_alg_busy && controller_out_ready &&
	                        ~aes_alg_start;

	in_transfer = (ctr_in_tvalid && ctr_in_tready);

	aes_alg_in_blk = iv;
	aes_alg_en_cipher = (encrypt_flag || decrypt_flag) && aes_alg_start;

	ctr_out_blk = {last_blk, aes_alg_out_blk ^ in_blk};
	ctr_out_store_blk = aes_alg_done;
	ctr_done = last_blk && ctr_out_store_blk;
end

always @(posedge clk) begin
	if (reset) begin
		iv_ready <= 1'b0;
		iv <= {`IV_BITS{1'b0}};
	end else begin
		if (in_transfer && !iv_ready) begin
			iv_ready <= 1'b1;
			iv <= ctr_in_blk;
		end

		if (aes_alg_done)
			iv <= {iv[`IV_BITS-1:64], iv[63:0] + 1'b1};

		if (ctr_done)
			iv_ready <= 1'b0;
	end
end

always @(posedge clk) begin
	if (in_transfer) begin
		in_blk <= ctr_in_blk;
	end
end

always @(posedge clk) begin
	if (reset) begin
		aes_alg_start <= 1'b0;
	end else begin
		aes_alg_start <= controller_out_ready && in_transfer
		                           && iv_ready;
	end
end

//`define CTR_SIM_VERBOSE
`ifdef CTR_SIM_VERBOSE
always @(posedge clk) begin
	if (in_transfer) begin
		$display("CTR: input blk: %H", ctr_in_blk);
	end

	if (in_transfer && !iv_ready) begin
		$display("CTR: iv: %H", ctr_in_blk);
	end

	if (ctr_out_store_blk) begin
		$display("CTR: output blk: %H", aes_alg_out_blk);
	end
end
`endif
endmodule

// ---------- CFB ----------
module cfb(
	input                        clk,
	input                        reset,

	input                        encrypt_flag,
	input                        decrypt_flag,

	input                        controller_out_ready,
	input                        last_blk,

	input [`BLK_S-1:0]           cfb_in_blk,
	input                        cfb_in_tvalid,
	output reg                   cfb_in_tready,

	output reg [`BLK_S-1:0]      aes_alg_in_blk,
	output reg                   aes_alg_en_cipher,
	output reg                   aes_alg_en_decipher,

	input [`BLK_S-1:0]           aes_alg_out_blk,
	input                        aes_alg_done,
	input                        aes_alg_busy,

	output reg                   cfb_out_store_blk,
	output reg [`BLK_S:0]        cfb_out_blk,

	output reg                   cfb_done
);

reg  [`IV_BITS-1:0] iv;
reg  iv_ready;

reg  [`BLK_S-1:0] in_blk;

reg  aes_alg_start;

reg  out_transfer;
reg  in_transfer;
reg  fill;

always @(*) begin
	cfb_in_tready = ~aes_alg_busy && controller_out_ready &&
	                        ~aes_alg_start;

	in_transfer = (cfb_in_tvalid && cfb_in_tready);

	aes_alg_in_blk = iv;
	aes_alg_en_cipher = (encrypt_flag || decrypt_flag) && aes_alg_start;
	aes_alg_en_decipher = 1'b0;

	cfb_out_blk = {last_blk, in_blk ^ aes_alg_out_blk};
	cfb_out_store_blk = aes_alg_done;
	cfb_done = last_blk && cfb_out_store_blk;
end

always @(posedge clk) begin
	if (reset) begin
		iv_ready <= 1'b0;
		iv <= {`IV_BITS{1'b0}};
	end else begin
		if (in_transfer && !iv_ready) begin
			iv_ready <= 1'b1;
			iv <= cfb_in_blk;
		end

		// At the end of an AES operation, update IV depending on
		// encryption/decryption flag
		if (encrypt_flag && aes_alg_done)
			iv <= in_blk ^ aes_alg_out_blk;

		if (decrypt_flag && aes_alg_done)
			iv <= in_blk;

		if (cfb_done)
			iv_ready <= 1'b0;
	end
end

always @(posedge clk) begin
	if (in_transfer) begin
		in_blk <= cfb_in_blk;
	end
end

always @(posedge clk) begin
	if (reset) begin
		aes_alg_start <= 1'b0;
	end else begin
		aes_alg_start <= controller_out_ready && in_transfer
		                           && iv_ready;
	end
end

//`define CFB_SIM_VERBOSE
`ifdef CFB_SIM_VERBOSE
always @(posedge clk) begin
	if (in_transfer) begin
		$display("CFB: input blk: %H", cfb_in_blk);
	end

	if (in_transfer && !iv_ready) begin
		$display("CFB: iv: %H", cfb_in_blk);
	end

	if (cfb_out_store_blk) begin
		$display("CFB: output blk: %H", aes_alg_out_blk);
	end
end
`endif
endmodule

// ---------- OFB ----------
module ofb(
	input                        clk,
	input                        reset,

	input                        encrypt_flag,
	input                        decrypt_flag,

	input                        controller_out_ready,
	input                        last_blk,

	input [`BLK_S-1:0]           ofb_in_blk,
	input                        ofb_in_tvalid,
	output reg                   ofb_in_tready,

	output reg [`BLK_S-1:0]      aes_alg_in_blk,
	output reg                   aes_alg_en_cipher,
	output reg                   aes_alg_en_decipher,

	input [`BLK_S-1:0]           aes_alg_out_blk,
	input                        aes_alg_done,
	input                        aes_alg_busy,

	output reg                   ofb_out_store_blk,
	output reg [`BLK_S:0]        ofb_out_blk,

	output reg                   ofb_done
);

reg  [`IV_BITS-1:0] iv;
reg  iv_ready;

reg  [`BLK_S-1:0] in_blk;

reg  aes_alg_start;

reg  out_transfer;
reg  in_transfer;
reg  fill;

always @(*) begin
	ofb_in_tready = ~aes_alg_busy && controller_out_ready &&
	                        ~aes_alg_start;

	in_transfer = (ofb_in_tvalid && ofb_in_tready);

	aes_alg_in_blk = iv;
	aes_alg_en_cipher = (encrypt_flag || decrypt_flag) && aes_alg_start;
	aes_alg_en_decipher = 1'b0;

	ofb_out_blk = {last_blk, in_blk ^ aes_alg_out_blk};
	ofb_out_store_blk = aes_alg_done;
	ofb_done = last_blk && ofb_out_store_blk;
end

always @(posedge clk) begin
	if (reset) begin
		iv_ready <= 1'b0;
		iv <= {`IV_BITS{1'b0}};
	end else begin
		if (in_transfer && !iv_ready) begin
			iv_ready <= 1'b1;
			iv <= ofb_in_blk;
		end

		if (aes_alg_done)
			iv <= aes_alg_out_blk;

		if (ofb_done)
			iv_ready <= 1'b0;
	end
end

always @(posedge clk) begin
	if (in_transfer) begin
		in_blk <= ofb_in_blk;
	end
end

always @(posedge clk) begin
	if (reset) begin
		aes_alg_start <= 1'b0;
	end else begin
		aes_alg_start <= controller_out_ready && in_transfer
		                           && iv_ready;
	end
end

//`define OFB_SIM_VERBOSE
`ifdef OFB_SIM_VERBOSE
always @(posedge clk) begin
	if (in_transfer) begin
		$display("OFB: input blk: %H", ofb_in_blk);
	end

	if (in_transfer && !iv_ready) begin
		$display("OFB: iv: %H", ofb_in_blk);
	end

	if (ofb_out_store_blk) begin
		$display("OFB: output blk: %H", aes_alg_out_blk);
	end
end
`endif
endmodule

// ---------- PCBC ----------
module pcbc(
	input                        clk,
	input                        reset,

	input                        encrypt_flag,
	input                        decrypt_flag,

	input                        controller_out_ready,
	input                        last_blk,

	input [`BLK_S-1:0]           pcbc_in_blk,
	input                        pcbc_in_tvalid,
	output reg                   pcbc_in_tready,

	output reg [`BLK_S-1:0]      aes_alg_in_blk,
	output reg                   aes_alg_en_cipher,
	output reg                   aes_alg_en_decipher,

	input [`BLK_S-1:0]           aes_alg_out_blk,
	input                        aes_alg_done,
	input                        aes_alg_busy,

	output reg                   pcbc_out_store_blk,
	output reg [`BLK_S:0]        pcbc_out_blk,

	output reg                   pcbc_done
);

reg  [`IV_BITS-1:0] iv;
reg  iv_ready;

reg  [`BLK_S-1:0] in_blk;

reg  aes_alg_start;

reg  out_transfer;
reg  in_transfer;
reg  fill;

always @(*) begin
	pcbc_in_tready = ~aes_alg_busy && controller_out_ready &&
	                        ~aes_alg_start;

	in_transfer = (pcbc_in_tvalid && pcbc_in_tready);

	aes_alg_in_blk = encrypt_flag ? iv ^ in_blk :
	                 decrypt_flag ? in_blk      :
	                 {`BLK_S{1'b0}};
	aes_alg_en_cipher = encrypt_flag && aes_alg_start;
	aes_alg_en_decipher = decrypt_flag && aes_alg_start;

	pcbc_out_blk = encrypt_flag ? {last_blk, aes_alg_out_blk} :
	               decrypt_flag ? {last_blk, iv ^ aes_alg_out_blk} :
	               {`BLK_S{1'b0}};
	pcbc_out_store_blk = aes_alg_done;
	pcbc_done = last_blk && pcbc_out_store_blk;
end

always @(posedge clk) begin
	if (reset) begin
		iv_ready <= 1'b0;
		iv <= {`IV_BITS{1'b0}};
	end else begin
		if (in_transfer && !iv_ready) begin
			iv_ready <= 1'b1;
			iv <= pcbc_in_blk;
		end

		if (encrypt_flag && aes_alg_done)
			iv <= in_blk ^ aes_alg_out_blk;

		if (decrypt_flag && aes_alg_done)
			iv <= in_blk ^ pcbc_out_blk;

		if (pcbc_done)
			iv_ready <= 1'b0;
	end
end

always @(posedge clk) begin
	if (in_transfer) begin
		in_blk <= pcbc_in_blk;
	end
end

always @(posedge clk) begin
	if (reset) begin
		aes_alg_start <= 1'b0;
	end else begin
		aes_alg_start <= controller_out_ready && in_transfer
		                           && iv_ready;
	end
end

//`define PCBC_SIM_VERBOSE
`ifdef PCBC_SIM_VERBOSE
always @(posedge clk) begin
	if (in_transfer) begin
		$display("PCBC: input blk: %H", pcbc_in_blk);
	end

	if (in_transfer && !iv_ready) begin
		$display("PCBC: iv: %H", pcbc_in_blk);
	end

	if (pcbc_out_store_blk) begin
		$display("PCBC: output blk: %H", aes_alg_out_blk);
	end
end
`endif
endmodule

// ---------- GCM ----------

module gcm #(
	parameter integer GCTR_BLK_BITS = 128,
	parameter integer SUBKEY_H_BITS = 128,
	parameter integer GCM_BLK_BITS = 128,
	parameter integer GHASH_BITS = 128,
	parameter integer TAG_BITS = 128,
	parameter integer AAD_BLK_BITS = 128,
	parameter integer AAD_LEN_BITS = 64,
	parameter integer DATA_LEN_BITS = 64
)(
	input                           clk,
	input                           reset,

	input                           key_expanded,

	input                           encrypt_flag,
	input                           decrypt_flag,

	input                           controller_out_ready,

	input [`BLK_S-1:0]              aes_alg_out_blk,
	output reg [`BLK_S-1:0]         aes_alg_in_blk,
	output reg                      aes_alg_en_cipher,
	output reg                      aes_alg_en_decipher,
	input                           aes_alg_done,

	input [GCM_BLK_BITS-1:0]        gcm_in_blk,
	input                           gcm_valid,
	output reg                      gcm_ready,

	output reg [GCM_BLK_BITS:0]     gcm_out_blk,
	output reg                      gcm_out_store_blk,

	output reg                      gcm_done
);

localparam GCM_COMPUTE_SUBKEY = 3'b000;
localparam GCM_GET_IV         = 3'b001;
localparam GCM_GET_AAD_SIZE   = 3'b010;
localparam GCM_HASH_AAD       = 3'b011;
localparam GCM_CRYPTO         = 3'b100;
localparam GCM_AAD_EXTRA      = 3'b101;
localparam GCM_TAG            = 3'b110;

reg  gcm_en;

reg  [2:0] state;
reg  [2:0] state_next;

reg  [`IV_BITS-1:0] j0;
reg  [`IV_BITS-1:0] icb;

reg  [SUBKEY_H_BITS-1:0] subkey_H;
reg  subkey_busy;

wire [GHASH_BITS-1:0] ghash_next;
reg  [GCM_BLK_BITS-1:0] ghash_data_blk;
wire ghash_done;
reg  ghash_busy;
reg  ghash_en;

reg  [GCTR_BLK_BITS-1:0] gctr_out_blk_final;
reg  gctr_out_blk_final_valid;

wire [GCTR_BLK_BITS-1:0] gctr_aes_alg_in_blk;
wire [GCTR_BLK_BITS-1:0] gctr_out_blk;
reg  [GCTR_BLK_BITS-1:0] gctr_in_blk;
wire [GCTR_BLK_BITS-1:0] gctr_mask;
reg  [GCTR_BLK_BITS-1:0] gctr_icb;
wire [`IV_BITS-1:0] gctr_icb_next;
wire gctr_aes_alg_start;
wire gctr_done;
wire gctr_busy;
reg  gctr_en;

reg  compute_subkey;
reg  get_iv;
reg  get_aad_size;
reg  hash_aad;
reg  hash_aad_done;
reg  crypto_start;
reg  crypto_done;
reg  crypto_store;
reg  crypto_blk_last;
reg  [DATA_LEN_BITS-1:0] crypto_cnt_next;
reg  hash_crypto_data;
reg  hash_aad_extra;

reg  [DATA_LEN_BITS-1:0] data_size_bkp;
reg  [DATA_LEN_BITS-1:0] data_size;
reg  [AAD_LEN_BITS-1:0] aad_size;
reg  [AAD_LEN_BITS-1:0] aad_size_bkp;
reg  aad_ready;
reg  aad_busy;

reg  crypto_ready;

reg  [TAG_BITS-1:0] tag;
reg  tag_start;
reg  tag_done;

ghash ghasher(
	.clk(clk),
	.reset(reset),
	.en(ghash_en),

	.g_prev(tag),
	.data_block(ghash_data_blk),
	.subkey_H(subkey_H),

	.ghash(ghash_next),
	.done(ghash_done)
);

gctr gctr_mod(
	.clk(clk),
	.reset(reset),
	.en(gctr_en),

	.icb(gctr_icb),
	.data_blk(gctr_in_blk),

	.aes_alg_out_blk(aes_alg_out_blk),
	.aes_alg_done(aes_alg_done),
	.aes_alg_in_blk(gctr_aes_alg_in_blk),
	.aes_alg_start(gctr_aes_alg_start),

	.gctr_out_blk(gctr_out_blk),
	.gctr_icb_next(gctr_icb_next),
	.gctr_busy(gctr_busy),
	.gctr_done(gctr_done)
);

gcm_mask #(
	.WIDTH(GCM_BLK_BITS),
	.SEL_WIDTH(7)
) mask_gen (
	.clk(clk),
	.sel(data_size[6:0]),

	.mask(gctr_mask)
);

/*
   * ---- FSM ----
   *
   * GCM_COMPUTE_SUBKEY - Wait for AES key to be expanded and start an AES
   *                      encryption operation on a full block of 0s to compute
   *                      the subkey H.
   * GCM_GET_IV         - Wait until the IV is received.
   * GCM_GET_AAD_SIZE   - Wait until a block containing AAD & input data size
   *                      in bits is received.
   * GCM_HASH_AAD       - Hash all input AAD blocks. Stop when we have hashed
   *                      "aad_size" bits.
   * GCM_CRYPTO         - Perform AES encryption on all input data blocks. Go
   *                      to the next steps when "data_size" bits were
   *                      encrypted. The result of each AES encryption is fed
   *                      to the GHASH module in order to advance with tag
   *                      computation.
   * GCM_AAD_EXTRA      - Start hashin the AAD "extra" block containing
   *                      {aad_size, data_size}, received in GCM_GET_AAD_SIZE
   *                      state.
   * GCM_TAG            - Wait for any hashing operaions to finish and compute
   *                      the final tag.
 */
always @(*) begin
	compute_subkey   = (state == GCM_COMPUTE_SUBKEY) && key_expanded;
	get_iv           = (state == GCM_GET_IV)         && gcm_en;
	get_aad_size     = (state == GCM_GET_AAD_SIZE)   && gcm_en;
	hash_aad         = (state == GCM_HASH_AAD)       && gcm_en;
	hash_aad_done    = (state == GCM_HASH_AAD)       && (aad_size == 0);
	crypto_start     = (state == GCM_CRYPTO)         && gcm_en;
	crypto_done      = (state == GCM_CRYPTO)         && (data_size == 0);
	hash_crypto_data = (state == GCM_CRYPTO)         &&
	                   (encrypt_flag ? gctr_out_blk_final_valid : gcm_en);
	hash_aad_extra   = (state == GCM_AAD_EXTRA)      && !aad_busy && controller_out_ready;
	tag_start        = (state == GCM_TAG)            && ghash_done;
	tag_done         = (state == GCM_TAG)            && gctr_out_blk_final_valid;
end

always @(*) begin
	state_next = state;

	case (state)
	GCM_COMPUTE_SUBKEY: begin
		if (compute_subkey)
			state_next = GCM_GET_IV;
	end
	GCM_GET_IV: begin
		if (get_iv)
			state_next = GCM_GET_AAD_SIZE;
	end
	GCM_GET_AAD_SIZE: begin
		if (get_aad_size)
			state_next = GCM_HASH_AAD;
	end
	GCM_HASH_AAD: begin
		if (hash_aad_done)
			state_next = GCM_CRYPTO;
	end
	GCM_CRYPTO: begin
		if (crypto_done)
			state_next = GCM_AAD_EXTRA;
	end
	GCM_AAD_EXTRA:
		if (hash_aad_extra)
			state_next = GCM_TAG;
	GCM_TAG:
		if (tag_done)
			state_next = GCM_COMPUTE_SUBKEY;
	default: begin
		state_next = GCM_COMPUTE_SUBKEY;
	end
	endcase
end

always @(posedge clk) begin
	if (reset) begin
		state <= GCM_COMPUTE_SUBKEY;
	end else begin
		state <= state_next;
	end
end

always @(*) begin
	aad_busy = ghash_busy || subkey_busy || hash_aad_done;
	aad_ready = !aad_busy;

	crypto_blk_last = data_size < GCM_BLK_BITS;
	crypto_ready = !gctr_busy && !crypto_done && ~gctr_out_blk_final_valid
	               && !subkey_busy && controller_out_ready;
	crypto_store = (state == GCM_CRYPTO) && gctr_out_blk_final_valid;

	gcm_ready =
	            (state == GCM_GET_IV)        ?    1'b1      :
	            (state == GCM_CRYPTO)        ? crypto_ready :
	            (state == GCM_GET_AAD_SIZE)  ? aad_ready    :
		    (state == GCM_HASH_AAD)      ? aad_ready    :
		    1'b0;
	gcm_en = gcm_ready && gcm_valid;

	gcm_out_blk = {tag_done, gctr_out_blk_final};
	gcm_out_store_blk = crypto_store || tag_done;
	gcm_done = tag_done;
end

/*
   * Extract j0 (needed for the final step in tag generation) and icb (initial
   * counter block - used as input block for AES crypto operations) from IV.
   *
   * IV size limited to 96 bits for now.
 */
always @(posedge clk) begin
	if (get_iv) begin
		j0 <= {gcm_in_blk[`IV_BITS-1:32], {31{1'b0}}, 1'b1};
		icb <= {gcm_in_blk[`IV_BITS-1:32], {30{1'b0}}, 2'b10};
	end

	if (gctr_done)
		icb <= gctr_icb_next;
end

/*
   * We cannot start hashing until subkey_H is computed, so track it via
   * subkey_busy.
 */
always @(posedge clk) begin
	if (reset) begin
		subkey_busy <= 1'b0;
	end else begin
		if (compute_subkey)
			subkey_busy <= 1'b1;

		if (subkey_busy && aes_alg_done)
			subkey_busy <= 1'b0;
	end
end

always @(posedge clk) begin
	if (aes_alg_done && subkey_busy) begin
		subkey_H <= aes_alg_out_blk;
	end
end
/*
   * ---- Tag generation logic ----
   *
   * GHASH operations are run on input blocks and the resulting hashes
   * accumulate in the "tag" register. The current value of the "tag" register
   * is used to generate the new tag. GHASH is run:
   * (i)   on each AAD input block
   * (ii)  on each data block generated by an AES cipher operation
   * (iii) on a special block {aad_size, data_size} - which is created by
   *       merging a 64-bit value representing the AAD length in bits and a
   *       64-bit value representing the input data length in bits.
   *
   * The final hash obtained after GHASHing {aad_size, data_size} is called S.
   *
   * Finally, the tag T is generated by running GCTR(J0, S):
   *    T = GCTR(J0, S)
   *
 */
always @(*) begin
	ghash_en = (state == GCM_HASH_AAD)  ? hash_aad         :
	           (state == GCM_AAD_EXTRA) ? hash_aad_extra   :
	           (state == GCM_CRYPTO)    ? hash_crypto_data :
	           1'b0;

	ghash_data_blk = (state == GCM_HASH_AAD) ? gcm_in_blk :
	                 (state == GCM_AAD_EXTRA) ? {aad_size_bkp, data_size_bkp} :
	                 encrypt_flag ? gctr_out_blk_final :
	                 decrypt_flag ? gcm_in_blk :
	                 {GCM_BLK_BITS{1'b0}};
end

/*
 * The first block before the actual AAD contains information about the AAD and input data lenghts.
 * If this block is available on the input (signaled through "get_aad_size"),
 * fill "aad_size" and "data_size" with this info and reset everything, as we
 * are about to start the whole GCM process.
 *
 * Use "ghash_busy" to track when a GHASH operation is in progress.
 */
always @(posedge clk) begin
	if (reset) begin
		data_size_bkp <= {DATA_LEN_BITS{1'b0}};
		data_size <= {DATA_LEN_BITS{1'b0}};

		aad_size_bkp <= {AAD_LEN_BITS{1'b0}};
		aad_size <= {AAD_LEN_BITS{1'b0}};

		ghash_busy <= 1'b0;

		tag <= {TAG_BITS{1'b0}};
	end else begin
		if (get_aad_size) begin
			tag <= {TAG_BITS{1'b0}};

			aad_size <= gcm_in_blk[GCM_BLK_BITS-1:64];
			data_size <= gcm_in_blk[DATA_LEN_BITS:0];

			aad_size_bkp <= gcm_in_blk[GCM_BLK_BITS-1:64];
			data_size_bkp <= gcm_in_blk[DATA_LEN_BITS:0];

		end

		if (ghash_en) begin
			ghash_busy <= 1'b1;
		end

		if (ghash_done) begin
			ghash_busy <= 1'b0;

			if (state == GCM_HASH_AAD)
				aad_size <= (aad_size >= GCM_BLK_BITS) ?
				            (aad_size - GCM_BLK_BITS) :
				            {AAD_LEN_BITS{1'b0}};
		end

		if (ghash_done)
			tag <= ghash_next;

		if ((state == GCM_CRYPTO) && gctr_out_blk_final_valid)
			data_size <= (data_size >= GCM_BLK_BITS) ?
			             (data_size - GCM_BLK_BITS) :
			             {DATA_LEN_BITS{1'b0}};
	end
end

/*
   * ---- GCTR control logic ----
 */
always @(*) begin
	gctr_icb = (state == GCM_TAG) ? j0 : icb;
	gctr_in_blk = (state == GCM_TAG) ? ghash_next : gcm_in_blk;
	gctr_en = crypto_start || tag_start;
end

// When the GCM input data length (plaintext/ciphertext) is not a multiple of
// the block size, we need to zero out the extra bits of the last block.
always @(posedge clk) begin
	if (reset) begin
		gctr_out_blk_final <= {GCTR_BLK_BITS{1'b0}};
		gctr_out_blk_final_valid <= 1'b0;
	end else begin
		gctr_out_blk_final_valid <= gctr_done;

		if ((state == GCM_CRYPTO) && gctr_done && crypto_blk_last)
			gctr_out_blk_final <= gctr_out_blk & gctr_mask;
		else
			gctr_out_blk_final <= gctr_out_blk;
	end
end

/*
   * ---- AES algorithm control logic ----
   *
   * AES cipher operations need to be performed:
   * (i)  by GCTR module for each input data block
   * (ii) for computing the subkey H
 */
always @(posedge clk) begin
	aes_alg_en_cipher <= compute_subkey || gctr_aes_alg_start;
	aes_alg_en_decipher <= 1'b0;

	if (compute_subkey)
		aes_alg_in_blk <= {`BLK_S{1'b0}};
	else if (gctr_aes_alg_start)
		aes_alg_in_blk <= gctr_aes_alg_in_blk;

end

//`define GCM_SIMULATION_VERBOSE
`ifdef GCM_SIMULATION_VERBOSE
integer s_aad_blk_no = 0;

always @(posedge clk) begin
	if (gcm_en) begin
		$display("GCM: Received block %0d: %H", s_aad_blk_no,  gcm_in_blk);
		s_aad_blk_no = s_aad_blk_no + 1;
	end

	if (get_iv) begin
		$display("GCM: j0: %H", {gcm_in_blk[127:32], {31{1'b0}}, 1'b1});
		$display("GCM: icb: %H", {gcm_in_blk[127:32], {30{1'b0}}, 2'b10});

		$display("GCM State change: GCM_GET_IV -> GCM_GET_AAD_SIZE");
	end

	if (aes_alg_done && subkey_busy) begin
		$display("GCM: subkey_H: %H", aes_alg_out_blk);
	end

	if (compute_subkey) begin
		$display("GCM: State change: GCM_COMPUTE_SUBKEY -> GCM_GET_IV");
	end

	if (get_aad_size) begin
		$display("GCM: AAD size in bits : %H", gcm_in_blk[127:64]);
		$display("GCM: Data size in bits: %H", gcm_in_blk[63:0]);

		$display("GCM: State change: GCM_GET_AAD_SIZE -> GCM_HASH_AAD");
	end

	if (hash_aad_done) begin
		$display("GCM: State change: GCM_HASH_AAD -> GCM_CRYPTO");
	end

	if (crypto_done) begin
		$display("GCM: State change: GCM_CRYPTO -> GCM_AAD_EXTRA");
	end

	if (hash_aad_extra) begin
		$display("GCM State change: GCM_AAD_EXTRA -> GCM_TAG");
	end

	if (tag_done) begin
		$display("GCM: Tag: %H", gctr_out_blk_final);
		$display("GCM State change: GCM_TAG -> GCM_COMPUTE_SUBKEY");
	end

	if (gcm_out_store_blk) begin
		$display("GCM: OUT BLK: %H", gcm_out_blk);
	end
end
`endif

endmodule
