// ---------- ECB ----------
module ecb(
	input                        clk,
	input                        reset,

	input                        encrypt_flag,
	output                       decrypt_flag,

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
	output                       decrypt_flag,

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
	output                       decrypt_flag,

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
	output                       decrypt_flag,

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

	input [`IV_BITS-1:0]            iv,
	input                           iv_en,

	input                           key_expanded,

	input [`BLK_S-1:0]              aes_alg_out_blk,
	output reg [`BLK_S-1:0]         aes_alg_in_blk,
	input                           aes_alg_done,
	output reg                      aes_alg_start,

	input [GCM_BLK_BITS-1:0]        gcm_in_blk,
	input                           gcm_valid,
	output reg                      gcm_ready,

	output reg [TAG_BITS-1:0]       gcm_tag,
	output reg [GCM_BLK_BITS-1:0]   gcm_out_blk,
	output reg                      gcm_op_done,
	output reg                      gcm_tag_done
);

localparam GCM_COMPUTE_SUBKEY = 3'b000;
localparam GCM_GET_AAD_SIZE   = 3'b001;
localparam GCM_HASH_AAD       = 3'b010;
localparam GCM_CRYPTO         = 3'b011;
localparam GCM_AAD_EXTRA      = 3'b100;
localparam GCM_TAG            = 3'b101;

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

wire [GCTR_BLK_BITS-1:0] gctr_aes_alg_in_blk;
wire [GCTR_BLK_BITS-1:0] gctr_out_blk;
reg  [GCTR_BLK_BITS-1:0] gctr_in_blk;
reg  [GCTR_BLK_BITS-1:0] gctr_icb;
wire [`IV_BITS-1:0] gctr_icb_next;
wire gctr_aes_alg_start;
wire gctr_done;
wire gctr_busy;
reg  gctr_en;

reg  compute_subkey;
reg  get_aad_size;
reg  hash_aad;
reg  hash_aad_done;
reg  crypto_start;
reg  crypto_done;

reg  [DATA_LEN_BITS-1:0] data_size;
reg  [DATA_LEN_BITS-1:0] data_counter;
reg  [AAD_LEN_BITS-1:0] aad_size;
reg  [AAD_LEN_BITS:0] aad_counter;
reg  aad_ready;
reg  aad_busy;

reg  crypto_ready;

reg  hash_aad_extra;

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

/*
   * ---- FSM ----
   *
   * GCM_COMPUTE_SUBKEY - Wait for AES key to be expanded and start an AES
   *                      encryption operation on a full block of 0s to compute
   *                      the subkey H.
   * GCM_GET_AAD_SIZE   - Wait until a block containing AAD & input data size
   *                      in bits is received.
   * GCM_HASH_AAD       - Hash all input AAD blocks. Stop when we have hashed
   *                      "aad_size" bits.
   * GCM_CRYPTO         - Perform AES encryption on all input data blocks. Go
   *                      to the next steps when "data_size" bits were
   *                      encrypted. The result of each AES encryption is fed
   *                      to the GHASH module for advancing with tag.
   * computation.
   * GCM_AAD_EXTRA      - Start hashin the AAD "extra" block containing
   *                      {aad_size, data_size}, received in GCM_GET_AAD_SIZE
   *                      state.
   * GCM_TAG            - Wait for any hashing operaions to finish and compute
   *                      the final tag.
 */
always @(*) begin
	compute_subkey = (state == GCM_COMPUTE_SUBKEY) && key_expanded;
	get_aad_size   = (state == GCM_GET_AAD_SIZE)   && gcm_en;
	hash_aad       = (state == GCM_HASH_AAD)       && gcm_en;
	hash_aad_done  = (state == GCM_HASH_AAD)       && (aad_counter == aad_size);
	crypto_start   = (state == GCM_CRYPTO)         && gcm_en;
	crypto_done    = (state == GCM_CRYPTO)         && (data_counter == data_size);
	hash_aad_extra = (state == GCM_AAD_EXTRA)      && !ghash_busy;
	tag_start      = (state == GCM_TAG)            && ghash_done;
	tag_done       = (state == GCM_TAG)            && gctr_done;
end

always @(*) begin
	state_next = state;

	case (state)
	GCM_COMPUTE_SUBKEY: begin
		if (compute_subkey)
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
	gcm_ready = (state == GCM_CRYPTO)        ? crypto_ready :
	            (state == GCM_GET_AAD_SIZE)  ? aad_ready :
		    (state == GCM_HASH_AAD)      ? aad_ready :
		    1'b0;
	gcm_en = gcm_ready && gcm_valid;
end

/*
   * Extract j0 (needed for the final step in tag generation) and icb (initial
   * counter block - used as input block for AES crypto operations) from IV.
   *
   * IV size limited to 96 bits for now.
 */
always @(posedge clk) begin
	if (iv_en) begin
		j0 <= {iv[`IV_BITS-1:32], {31{1'b0}}, 1'b1};
		icb <= {iv[`IV_BITS-1:32], {30{1'b0}}, 2'b10};
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
	ghash_en = (state == GCM_HASH_AAD)  ? hash_aad       :
	           (state == GCM_AAD_EXTRA) ? hash_aad_extra :
	           (state == GCM_CRYPTO)    ? gctr_done      :
	           1'b0;

	ghash_data_blk = (state == GCM_HASH_AAD) ? gcm_in_blk :
	                 (state == GCM_AAD_EXTRA) ? {aad_size, data_size} :
	                 gctr_out_blk;
end

always @(*) begin
	aad_busy = ghash_busy || ((state == GCM_HASH_AAD) && subkey_busy) || hash_aad_done;
	aad_ready = !aad_busy;
end

/*
 * The final tag is not stored in the "tag" register because we have no later
 * use for it. Use the GCTR output and "done" strobe directly to save one clock
 * cycle.
 */
always @(*) begin
	gcm_tag_done = tag_done;
	gcm_tag = gctr_out_blk;
end

/*
 * The first block before the actual AAD contains information about the AAD and input data lenghts.
 * If this block is available on the input (signaled through "get_aad_size"),
 * fill "aad_size" and "data_size" with this info and reset everything, as we
 * are about to start the whole GCM process.
 *
 * Use "ghash_busy" to track when a GHASH operation is in progress. Also, keep
 * track of how many blocks we GHASHed using the aad_counter and data_counter.
 */
always @(posedge clk) begin
	if (reset) begin
		data_counter <= {DATA_LEN_BITS{1'b0}};
		aad_counter <= {DATA_LEN_BITS{1'b0}};
		data_size <= {AAD_LEN_BITS{1'b0}};
		aad_size <= {AAD_LEN_BITS{1'b0}};
		ghash_busy <= 1'b0;

		tag <= {TAG_BITS{1'b0}};
	end else begin
		if (get_aad_size) begin
			data_counter <= {DATA_LEN_BITS{1'b0}};
			aad_counter <= {AAD_LEN_BITS{1'b0}};
			tag <= {TAG_BITS{1'b0}};

			aad_size <= gcm_in_blk[GCM_BLK_BITS-1:64];
			data_size <= gcm_in_blk[DATA_LEN_BITS:0];
		end

		if (ghash_en) begin
			ghash_busy <= 1'b1;
		end

		if (ghash_done) begin
			ghash_busy <= 1'b0;

			if (state == GCM_HASH_AAD)
				aad_counter <= aad_counter + AAD_BLK_BITS;
		end

		if (ghash_done)
			tag <= ghash_next;

		if ((state == GCM_CRYPTO) && gctr_done) begin
			data_counter <= data_counter + GCM_BLK_BITS;
		end
	end
end

/*
   * ---- GCTR control logic ----
 */
always @(*) begin
	crypto_ready = !gctr_busy && !crypto_done;

	gctr_icb = (state == GCM_TAG) ? j0 : icb;
	gctr_in_blk = (state == GCM_TAG) ? ghash_next : gcm_in_blk;
	gctr_en = crypto_start || tag_start;

	gcm_out_blk = gctr_out_blk;
	gcm_op_done = (state == GCM_CRYPTO) && gctr_done;
end

/*
   * ---- AES algorithm control logic ----
   *
   * AES cipher operations need to be performed:
   * (i)  by GCTR module for each input data block
   * (ii) for computing the subkey H
 */
always @(*) begin
	aes_alg_start = compute_subkey || gctr_aes_alg_start;
end

always @(posedge clk) begin
	if (compute_subkey)
		aes_alg_in_blk <= {`BLK_S{1'b0}};
	else if (crypto_start)
		aes_alg_in_blk <= gctr_aes_alg_in_blk;

end

//`define GCM_SIMULATION_VERBOSE
`ifdef GCM_SIMULATION_VERBOSE
integer s_aad_blk_no = 0;

always @(posedge clk) begin
	if (iv_en) begin
		$display("GCM: j0: %H", {iv[127:32], {31{1'b0}}, 1'b1});
		$display("GCM: icb: %H", {iv[127:32], {30{1'b0}}, 2'b10});
	end

	if (gcm_en) begin
		$display("GCM: Received block %0d: %H", s_aad_blk_no,  gcm_in_blk);
		s_aad_blk_no = s_aad_blk_no + 1;
	end

	if (aes_alg_done && subkey_busy) begin
		$display("GCM: subkey_H: %H", aes_alg_out_blk);
	end

	if (compute_subkey) begin
		$display("GCM: State change: GCM_COMPUTE_SUBKEY -> GCM_GET_AAD_SIZE");
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
		$display("GCM: Tag: %H", gctr_out_blk);
	end
end
`endif

endmodule
