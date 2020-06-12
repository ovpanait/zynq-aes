`include "aes.vh"

module aes_controller #
(
	parameter IN_BUS_DATA_WIDTH = 32,
	parameter IN_FIFO_DEPTH = 256,

	parameter OUT_BUS_DATA_WIDTH = 32,
	parameter OUT_FIFO_DEPTH = 256,

	parameter ECB_SUPPORT  =  1,
	parameter CBC_SUPPORT  =  1,
	parameter CTR_SUPPORT  =  1,
	parameter CFB_SUPPORT  =  1,
	parameter OFB_SUPPORT  =  1,
	parameter PCBC_SUPPORT =  1
)
(
	input                                clk,
	input                                reset,

	// input stage
	input                                in_bus_data_wren,
	input                                in_bus_tlast,
	input [IN_BUS_DATA_WIDTH-1:0]        in_bus_data,

	output                               controller_in_busy,

	// output stage
	output                               out_bus_tvalid,
	input                                out_bus_tready,
	output     [OUT_BUS_DATA_WIDTH-1:0]  out_bus_tdata,
	output                               out_bus_tlast
);

`include "controller_fc.vh"
`include "common.vh"

localparam IN_FIFO_DATA_WIDTH = `BLK_S + 1; // {tlast bit, 1 x 128-bit AES block}
localparam IN_FIFO_ADDR_WIDTH = clogb2(IN_FIFO_DEPTH);

localparam OUT_FIFO_DATA_WIDTH = `BLK_S + 1; // {tlast bit, 1 x 128-bit AES block}
localparam OUT_FIFO_ADDR_WIDTH = clogb2(OUT_FIFO_DEPTH);

localparam [2:0] AES_GET_CMD = 3'b000;
localparam [2:0] AES_GET_KEY_128  = 3'b001;
localparam [2:0] AES_GET_KEY_256  = 3'b010;
localparam [2:0] AES_PAYLOAD = 3'b100;

// ============================================================================
// AES controller input stage signals

wire                          in_fifo_read_tvalid;
wire                          in_fifo_read_tready;
wire [IN_FIFO_DATA_WIDTH-1:0] in_fifo_rdata;

// ============================================================================
// AES controller processing stage signals

// AES algorithm control signals
reg  [`BLK_S-1:0] aes_alg_in_blk;
reg  [`KEY_S-1:0] aes_alg_key;
wire [`BLK_S-1:0] aes_out_blk;
wire aes_op_in_progress;
reg  aes_alg_en_decipher;
reg  aes_alg_en_cipher;
reg  aes_alg_en_key;
wire aes_alg_done;
reg  aes128_mode;
reg  aes256_mode;

// FSM states and control signals
reg  [2:0] state;
reg  fsm_cmd_state,
     fsm_key128_state,
     fsm_key256_state,
     fsm_process_state;

reg  key_expanded;
reg  key_exp_in_progress;
reg  key128_start;
reg  key256_start;

reg  [`BLK_S-1:0] in_blk;

reg last_blk;

reg  [`KEY_S-1:0] aes_key;
reg  [`WORD_S-1:0] aes_cmd;

wire encrypt_flag;
wire decrypt_flag;

wire in_fifo_read_req;

reg  [`BLK_S:0] mode_out_blk;
reg  store_out_blk;

reg  mode_done;

// ECB signals
wire ecb_flag;

reg  ecb_in_tvalid;
wire ecb_in_tready;
wire ecb_done;

wire [`BLK_S:0 ] ecb_out_blk;
reg  [`BLK_S-1:0 ] ecb_in_blk;
wire [`BLK_S-1:0 ] ecb_aes_alg_in_blk;
wire ecb_aes_alg_en_decipher;
wire ecb_aes_alg_en_cipher;
wire ecb_out_store_blk;
reg  ecb_aes_alg_done;

// CBC signals
wire cbc_flag;

reg  cbc_in_tvalid;
wire cbc_in_tready;
wire cbc_done;

wire [`BLK_S:0 ] cbc_out_blk;
reg  [`BLK_S-1:0 ] cbc_in_blk;
wire [`BLK_S-1:0 ] cbc_aes_alg_in_blk;
wire cbc_aes_alg_en_decipher;
wire cbc_aes_alg_en_cipher;
wire cbc_out_store_blk;
reg  cbc_aes_alg_done;

// CTR signals
wire ctr_flag;

reg  ctr_in_tvalid;
wire ctr_in_tready;
wire ctr_done;

wire [`BLK_S:0 ] ctr_out_blk;
reg  [`BLK_S-1:0 ] ctr_in_blk;
wire [`BLK_S-1:0 ] ctr_aes_alg_in_blk;
wire ctr_aes_alg_en_decipher;
wire ctr_aes_alg_en_cipher;
wire ctr_out_store_blk;
reg  ctr_aes_alg_done;

// CFB signals
wire cfb_flag;

reg  cfb_in_tvalid;
wire cfb_in_tready;
wire cfb_done;

wire [`BLK_S:0 ] cfb_out_blk;
reg  [`BLK_S-1:0 ] cfb_in_blk;
wire [`BLK_S-1:0 ] cfb_aes_alg_in_blk;
wire cfb_aes_alg_en_decipher;
wire cfb_aes_alg_en_cipher;
wire cfb_out_store_blk;
reg  cfb_aes_alg_done;

// OFB signals
wire ofb_flag;

reg  ofb_in_tvalid;
wire ofb_in_tready;
wire ofb_done;

wire [`BLK_S:0 ] ofb_out_blk;
reg  [`BLK_S-1:0 ] ofb_in_blk;
wire [`BLK_S-1:0 ] ofb_aes_alg_in_blk;
wire ofb_aes_alg_en_decipher;
wire ofb_aes_alg_en_cipher;
wire ofb_out_store_blk;
reg  ofb_aes_alg_done;

// PCBC signals
wire pcbc_flag;

reg  pcbc_in_tvalid;
wire pcbc_in_tready;
wire pcbc_done;

wire [`BLK_S:0 ] pcbc_out_blk;
reg  [`BLK_S-1:0 ] pcbc_in_blk;
wire [`BLK_S-1:0 ] pcbc_aes_alg_in_blk;
wire pcbc_aes_alg_en_decipher;
wire pcbc_aes_alg_en_cipher;
wire pcbc_out_store_blk;
reg  pcbc_aes_alg_done;


// ============================================================================
// AES controller output stage signals

reg [OUT_FIFO_DATA_WIDTH-1:0] out_fifo_wdata;
reg out_fifo_write_tvalid;
wire out_fifo_write_tready;

wire out_fifo_write_req;

// ============================================================================
// AES controller input stage

aes_controller_input #(
	.BUS_DATA_WIDTH(IN_BUS_DATA_WIDTH),

	.FIFO_ADDR_WIDTH(IN_FIFO_ADDR_WIDTH),
	.FIFO_DATA_WIDTH(IN_FIFO_DATA_WIDTH)
) controller_input_block (
	.clk(clk),
	.reset(reset),

	.bus_data_wren(in_bus_data_wren),
	.bus_tlast(in_bus_tlast),
	.bus_data(in_bus_data),

	.in_fifo_read_tvalid(in_fifo_read_tvalid),
	.in_fifo_read_tready(in_fifo_read_tready),
	.in_fifo_rdata(in_fifo_rdata),

	.controller_in_busy(controller_in_busy)
);

// ============================================================================
// AES controller processing stage

/*
   * The processing stage of the AES controller does the following:
   * = Retrieve 32-bit command from the FIFO
   *   The command conveys the following information:
   *       - type of operation to be performed (encryption/decryption)
   *       - key size (AES-128/AES-256)
   *       - mode of operation (ECB,CBC, etc.)
   * = Retrieve and assemble 128/256-bit key
   * = Start key expansion
   * = Retrieve the rest of the data (the payload) one block at a time and pass
   *   it to module implementing the current mode of operation (ECB, CBC, etc.).
   *   The payload can be anything, the controller does not have any knowledge of
   *   the internal representation of the payload. It can be for instance IV +
   *   DATA in the most common cases, or IV + AAD info + AAD + DATA in others.
  */

always @(*) begin
	fsm_cmd_state     = (state == AES_GET_CMD);
	fsm_key128_state  = (state == AES_GET_KEY_128);
	fsm_key256_state  = (state == AES_GET_KEY_256);
	fsm_process_state = (state == AES_PAYLOAD);
end

assign encrypt_flag = is_encryption(aes_cmd);
assign decrypt_flag = is_decryption(aes_cmd);

/*
   * ECB_SUPPORT
 */
generate
if (ECB_SUPPORT) begin

assign ecb_flag = is_ECB_op(aes_cmd);

always @(*) begin
	ecb_in_blk = in_fifo_rdata;

	ecb_in_tvalid = fsm_process_state && in_fifo_read_tvalid;

	ecb_aes_alg_done = aes_alg_done && key_expanded;
end

ecb ecb_mod(
	.clk(clk),
	.reset(reset),

	.encrypt_flag(encrypt_flag),
	.decrypt_flag(decrypt_flag),

	.controller_out_ready(out_fifo_write_tready),
	.last_blk(last_blk),

	.ecb_in_blk(ecb_in_blk),
	.ecb_in_tvalid(ecb_in_tvalid),
	.ecb_in_tready(ecb_in_tready),

	.aes_alg_out_blk(aes_out_blk),
	.aes_alg_in_blk(ecb_aes_alg_in_blk),
	.aes_alg_en_cipher(ecb_aes_alg_en_cipher),
	.aes_alg_en_decipher(ecb_aes_alg_en_decipher),
	.aes_alg_done(ecb_aes_alg_done),
	.aes_alg_busy(aes_op_in_progress),

	.ecb_out_blk(ecb_out_blk),
	.ecb_out_store_blk(ecb_out_store_blk),

	.ecb_done(ecb_done)
);
end else begin
	assign ecb_flag = 1'b0;
end
endgenerate

/*
   * CBC_SUPPORT
 */
generate
if (CBC_SUPPORT) begin

assign cbc_flag = is_CBC_op(aes_cmd);

always @(*) begin
	cbc_in_blk = in_fifo_rdata;

	cbc_in_tvalid = fsm_process_state && in_fifo_read_tvalid;

	cbc_aes_alg_done = aes_alg_done && key_expanded;
end

cbc cbc_mod(
	.clk(clk),
	.reset(reset),

	.encrypt_flag(encrypt_flag),
	.decrypt_flag(decrypt_flag),

	.controller_out_ready(out_fifo_write_tready),
	.last_blk(last_blk),

	.cbc_in_blk(cbc_in_blk),
	.cbc_in_tvalid(cbc_in_tvalid),
	.cbc_in_tready(cbc_in_tready),

	.aes_alg_out_blk(aes_out_blk),
	.aes_alg_in_blk(cbc_aes_alg_in_blk),
	.aes_alg_en_cipher(cbc_aes_alg_en_cipher),
	.aes_alg_en_decipher(cbc_aes_alg_en_decipher),
	.aes_alg_done(cbc_aes_alg_done),
	.aes_alg_busy(aes_op_in_progress),

	.cbc_out_blk(cbc_out_blk),
	.cbc_out_store_blk(cbc_out_store_blk),

	.cbc_done(cbc_done)
);
end else begin
	assign cbc_flag = 1'b0;
end
endgenerate

/*
   * CTR SUPPORT
 */
generate
if (CTR_SUPPORT) begin

assign ctr_flag = is_CTR_op(aes_cmd);

always @(*) begin
	ctr_in_blk = in_fifo_rdata;

	ctr_in_tvalid = fsm_process_state && in_fifo_read_tvalid;

	ctr_aes_alg_done = aes_alg_done && key_expanded;
end

ctr ctr_mod(
	.clk(clk),
	.reset(reset),

	.encrypt_flag(encrypt_flag),
	.decrypt_flag(decrypt_flag),

	.controller_out_ready(out_fifo_write_tready),
	.last_blk(last_blk),

	.ctr_in_blk(ctr_in_blk),
	.ctr_in_tvalid(ctr_in_tvalid),
	.ctr_in_tready(ctr_in_tready),

	.aes_alg_out_blk(aes_out_blk),
	.aes_alg_in_blk(ctr_aes_alg_in_blk),
	.aes_alg_en_cipher(ctr_aes_alg_en_cipher),
	.aes_alg_en_decipher(ctr_aes_alg_en_decipher),
	.aes_alg_done(ctr_aes_alg_done),
	.aes_alg_busy(aes_op_in_progress),

	.ctr_out_blk(ctr_out_blk),
	.ctr_out_store_blk(ctr_out_store_blk),

	.ctr_done(ctr_done)
);
end else begin
	assign ctr_flag = 1'b0;
end
endgenerate

/*
   * CFB SUPPORT
 */
generate
if (CFB_SUPPORT) begin

assign cfb_flag = is_CFB_op(aes_cmd);

always @(*) begin
	cfb_in_blk = in_fifo_rdata;

	cfb_in_tvalid = fsm_process_state && in_fifo_read_tvalid;

	cfb_aes_alg_done = aes_alg_done && key_expanded;
end

cfb cfb_mod(
	.clk(clk),
	.reset(reset),

	.encrypt_flag(encrypt_flag),
	.decrypt_flag(decrypt_flag),

	.controller_out_ready(out_fifo_write_tready),
	.last_blk(last_blk),

	.cfb_in_blk(cfb_in_blk),
	.cfb_in_tvalid(cfb_in_tvalid),
	.cfb_in_tready(cfb_in_tready),

	.aes_alg_out_blk(aes_out_blk),
	.aes_alg_in_blk(cfb_aes_alg_in_blk),
	.aes_alg_en_cipher(cfb_aes_alg_en_cipher),
	.aes_alg_en_decipher(cfb_aes_alg_en_decipher),
	.aes_alg_done(cfb_aes_alg_done),
	.aes_alg_busy(aes_op_in_progress),

	.cfb_out_blk(cfb_out_blk),
	.cfb_out_store_blk(cfb_out_store_blk),

	.cfb_done(cfb_done)
);
end else begin
	assign cfb_flag = 1'b0;
end
endgenerate

/*
   * OFB SUPPORT
 */
generate
if (OFB_SUPPORT) begin

assign ofb_flag = is_OFB_op(aes_cmd);

always @(*) begin
	ofb_in_blk = in_fifo_rdata;

	ofb_in_tvalid = fsm_process_state && in_fifo_read_tvalid;

	ofb_aes_alg_done = aes_alg_done && key_expanded;
end

ofb ofb_mod(
	.clk(clk),
	.reset(reset),

	.encrypt_flag(encrypt_flag),
	.decrypt_flag(decrypt_flag),

	.controller_out_ready(out_fifo_write_tready),
	.last_blk(last_blk),

	.ofb_in_blk(ofb_in_blk),
	.ofb_in_tvalid(ofb_in_tvalid),
	.ofb_in_tready(ofb_in_tready),

	.aes_alg_out_blk(aes_out_blk),
	.aes_alg_in_blk(ofb_aes_alg_in_blk),
	.aes_alg_en_cipher(ofb_aes_alg_en_cipher),
	.aes_alg_en_decipher(ofb_aes_alg_en_decipher),
	.aes_alg_done(ofb_aes_alg_done),
	.aes_alg_busy(aes_op_in_progress),

	.ofb_out_blk(ofb_out_blk),
	.ofb_out_store_blk(ofb_out_store_blk),

	.ofb_done(ofb_done)
);
end else begin
	assign ofb_flag = 1'b0;
end
endgenerate

/*
   * PCBC SUPPORT
 */
generate
if (PCBC_SUPPORT) begin

assign pcbc_flag = is_PCBC_op(aes_cmd);

always @(*) begin
	pcbc_in_blk = in_fifo_rdata;

	pcbc_in_tvalid = fsm_process_state && in_fifo_read_tvalid;

	pcbc_aes_alg_done = aes_alg_done && key_expanded;
end

pcbc pcbc_mod(
	.clk(clk),
	.reset(reset),

	.encrypt_flag(encrypt_flag),
	.decrypt_flag(decrypt_flag),

	.controller_out_ready(out_fifo_write_tready),
	.last_blk(last_blk),

	.pcbc_in_blk(pcbc_in_blk),
	.pcbc_in_tvalid(pcbc_in_tvalid),
	.pcbc_in_tready(pcbc_in_tready),

	.aes_alg_out_blk(aes_out_blk),
	.aes_alg_in_blk(pcbc_aes_alg_in_blk),
	.aes_alg_en_cipher(pcbc_aes_alg_en_cipher),
	.aes_alg_en_decipher(pcbc_aes_alg_en_decipher),
	.aes_alg_done(pcbc_aes_alg_done),
	.aes_alg_busy(aes_op_in_progress),

	.pcbc_out_blk(pcbc_out_blk),
	.pcbc_out_store_blk(pcbc_out_store_blk),

	.pcbc_done(pcbc_done)
);
end else begin
	assign pcbc_flag = 1'b0;
end
endgenerate

/*
   * AES algorithm control blocks.
 */
always @(*) begin
	aes128_mode = is_128bit_key(aes_cmd);
	aes256_mode = is_256bit_key(aes_cmd);
	aes_alg_in_blk = ecb_flag  ? ecb_aes_alg_in_blk  :
	                 cbc_flag  ? cbc_aes_alg_in_blk  :
	                 ctr_flag  ? ctr_aes_alg_in_blk  :
	                 cfb_flag  ? cfb_aes_alg_in_blk  :
	                 ofb_flag  ? ofb_aes_alg_in_blk  :
	                 pcbc_flag ? pcbc_aes_alg_in_blk :
	                 {`BLK_S{1'b0}};
	aes_alg_key = aes_key;

	aes_alg_en_cipher = fsm_process_state ?
	                    (ecb_flag  ? ecb_aes_alg_en_cipher  :
	                     cbc_flag  ? cbc_aes_alg_en_cipher  :
	                     ctr_flag  ? ctr_aes_alg_en_cipher  :
	                     cfb_flag  ? cfb_aes_alg_en_cipher  :
	                     ofb_flag  ? ofb_aes_alg_en_cipher  :
	                     pcbc_flag ? pcbc_aes_alg_en_cipher :
	                      1'b0)
	                    : 1'b0;

	aes_alg_en_decipher = fsm_process_state ?
	                     (ecb_flag  ? ecb_aes_alg_en_decipher  :
	                      cbc_flag  ? cbc_aes_alg_en_decipher  :
	                      ctr_flag  ? ctr_aes_alg_en_decipher  :
	                      cfb_flag  ? cfb_aes_alg_en_decipher  :
	                      ofb_flag  ? ofb_aes_alg_en_decipher  :
	                      pcbc_flag ? pcbc_aes_alg_en_decipher :
	                      1'b0)
	                    : 1'b0;

end

always @(posedge clk) begin
/*
  * Registered so that data is retrieved from the FIFO.
  *
  * Key expansion is the only AES operation that the controller takes care of.
  * For encryption/decryption, the modules implementing the modes of operations
  * decide when they should take place.
 */
	if (reset) begin
		aes_alg_en_key <= 1'b0;
	end else begin
		aes_alg_en_key <= key128_start || key256_start;
	end
end

// AES algorithm
aes_top aes_mod(
	.clk(clk),
	.reset(reset),

	.en_cipher(aes_alg_en_cipher),
	.en_decipher(aes_alg_en_decipher),
	.en_key(aes_alg_en_key),

	.aes128_mode(aes128_mode),
	.aes256_mode(aes256_mode),

	.aes_op_in_progress(aes_op_in_progress),

	.aes_key(aes_alg_key),
	.aes_in_blk(aes_alg_in_blk),

	.aes_out_blk(aes_out_blk),
	.en_o(aes_alg_done)
);

/*
   * Controller processing stage logic.
 */
assign out_fifo_write_req = out_fifo_write_tready && out_fifo_write_tvalid;
assign in_fifo_read_req = in_fifo_read_tready && in_fifo_read_tvalid;

always @(posedge clk) begin
	if (reset == 1'b1) begin
		aes_key <= {`KEY_S{1'b0}};
		aes_cmd <= {`CMD_BITS{1'b0}};
		state <= AES_GET_CMD;
		in_blk <= {`BLK_S{1'b0}};
		last_blk <= 1'b0;
	end
	else begin
		case (state)
			AES_GET_CMD:
			begin
				if (in_fifo_read_req) begin
					aes_cmd <= in_fifo_rdata[`CMD_BITS-1:0];

					state <= AES_GET_KEY_128;
				end
			end
			AES_GET_KEY_128:
			begin
				if (in_fifo_read_req) begin
					state <= AES_PAYLOAD;

					aes_key[`AES256_KEY_BITS-1 : `AES128_KEY_BITS] <= in_fifo_rdata;

					if (aes256_mode)
						state <= AES_GET_KEY_256;
				end
			end
			AES_GET_KEY_256:
			begin
				if (in_fifo_read_req) begin
					aes_key[`AES128_KEY_BITS-1 : 0] <= in_fifo_rdata;
					state <= AES_PAYLOAD;
				end
			end
			AES_PAYLOAD:
			begin
				state <= AES_PAYLOAD;

				if (in_fifo_read_req) begin
					in_blk <= in_fifo_rdata[`BLK_S-1:0];
					last_blk <= in_fifo_rdata[`BLK_S];
				end

				if (mode_done) begin
					last_blk <= 1'b0;
					state <= AES_GET_CMD;
				end
			end
			default:
				state <= AES_GET_CMD;
		endcase
	end
end

always @(*) begin
	key128_start = (aes128_mode && in_fifo_read_req && fsm_key128_state);
	key256_start = (aes256_mode && in_fifo_read_req && fsm_key256_state);
end

always @(posedge clk) begin
	if (reset) begin
		key_expanded <= 1'b0;
		key_exp_in_progress <= 1'b0;
	end else begin
		if (mode_done)
			key_expanded <= 1'b0;

		if (key128_start || key256_start) begin
			key_exp_in_progress <= 1'b1;
		end

		if (aes_alg_done && key_exp_in_progress) begin
			key_exp_in_progress <= 1'b0;
			key_expanded <= 1'b1;
		end
	end
end

assign in_fifo_read_tready =
	fsm_cmd_state      ||
	fsm_key128_state   ||
	fsm_key256_state   ||
	(fsm_process_state &&
	                     (ecb_flag  ? ecb_in_tready  :
	                      cbc_flag  ? cbc_in_tready  :
	                      ctr_flag  ? ctr_in_tready  :
	                      cfb_flag  ? cfb_in_tready  :
	                      ofb_flag  ? ofb_in_tready  :
	                      pcbc_flag ? pcbc_in_tready :
			      1'b0));

always @(*) begin
	mode_done <=
	             ecb_flag  ? ecb_done  :
	             cbc_flag  ? cbc_done  :
	             ctr_flag  ? ctr_done  :
	             cfb_flag  ? cfb_done  :
	             ofb_flag  ? ofb_done  :
	             pcbc_flag ? pcbc_done :
	             1'b0;
end

/*
   * Output interface logic.
 */
always @(*) begin
	mode_out_blk =
	                ecb_flag  ? ecb_out_blk  :
	                cbc_flag  ? cbc_out_blk  :
	                ctr_flag  ? ctr_out_blk  :
	                cfb_flag  ? cfb_out_blk  :
	                ofb_flag  ? ofb_out_blk  :
	                pcbc_flag ? pcbc_out_blk :
	                {`BLK_S+1{1'b0}};

	store_out_blk =
	                ecb_flag  ? ecb_out_store_blk  :
	                cbc_flag  ? cbc_out_store_blk  :
	                ctr_flag  ? ctr_out_store_blk  :
	                cfb_flag  ? cfb_out_store_blk  :
	                ofb_flag  ? ofb_out_store_blk  :
	                pcbc_flag ? pcbc_out_store_blk :
	                1'b0;
end

always @(posedge clk) begin
	if (reset) begin
		out_fifo_write_tvalid <= 1'b0;
		out_fifo_wdata <= {`BLK_S{1'b0}};
	end else begin
		if (store_out_blk) begin
			out_fifo_wdata <= mode_out_blk;
			out_fifo_write_tvalid <= 1'b1;
		end

		if (out_fifo_write_req)
			out_fifo_write_tvalid <= 1'b0;
	end
end

// ============================================================================
// AES controller output stage

aes_controller_output #(
	.BUS_TDATA_WIDTH(OUT_BUS_DATA_WIDTH),

	.FIFO_ADDR_WIDTH(OUT_FIFO_ADDR_WIDTH),
	.FIFO_DATA_WIDTH(OUT_FIFO_DATA_WIDTH)
) controller_output_block (
	.clk(clk),
	.resetn(!reset),

	.fifo_write_tready(out_fifo_write_tready),
	.fifo_write_tvalid(out_fifo_write_tvalid),
	.fifo_wdata(out_fifo_wdata),

	.bus_tvalid(out_bus_tvalid),
	.bus_tready(out_bus_tready),
	.bus_tdata(out_bus_tdata),
	.bus_tlast(out_bus_tlast)
);

//`define SIMULATION_VERBOSE_EXTREME
`ifdef SIMULATION_VERBOSE_EXTREME
integer s_in_blk_cnt = 0;
integer s_in_cmd_cnt = 0;
integer s_out_blk_cnt = 0;

always @(posedge clk) begin
	case (state)
	AES_GET_CMD:
	begin
		if (in_fifo_read_req) begin
			$display("AES PROCESSING: cmd no %0d: %H", s_in_cmd_cnt, in_fifo_rdata[`CMD_BITS-1:0]);
			s_in_cmd_cnt = s_in_cmd_cnt + 1;
		end
	end
	AES_GET_KEY_128:
	begin
		if (in_fifo_read_req) begin
			$display("AES PROCESSING: key 128 - blk %0d: %H", s_in_blk_cnt, in_fifo_rdata);
			s_in_blk_cnt = s_in_blk_cnt + 1;
		end
	end
	AES_GET_KEY_256:
	begin
		if (in_fifo_read_req) begin
			$display("AES POCESSING: key 256 - blk %0d: %H", s_in_blk_cnt, in_fifo_rdata);
			s_in_blk_cnt = s_in_blk_cnt + 1;
		end
	end
	AES_PAYLOAD:
	begin
		if (in_fifo_read_req) begin
			$display("AES PROCESSING: input block no %0d: %H", s_in_blk_cnt, in_fifo_rdata);
			s_in_blk_cnt = s_in_blk_cnt + 1;
		end
	end
	endcase
end
`endif

//`define AES_CONTROLLER_BENCHMARK
`ifdef AES_CONTROLLER_BENCHMARK
reg  s_process;
time s_process_start_t;
integer s_process_in_blks = 0;

always @(posedge clk) begin
	if (state == AES_GET_CMD && in_fifo_read_req) begin
		s_process <= 1'b1;
		s_process_in_blks <= 1;
		s_process_start_t = $time;
	end

	if (s_process && in_fifo_read_req) begin
		s_process_in_blks <= s_process_in_blks + 1;
	end

	if (s_process && mode_done) begin
		$display("AES BENCHMARK: Processing %0d blocks took %0t",
				s_process_in_blks,
				$time - s_process_start_t);
		s_process <= 1'b0;
		s_process_in_blks <= 0;
	end
end
`endif

endmodule
