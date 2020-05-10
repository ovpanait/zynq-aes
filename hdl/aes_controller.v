`include "aes.vh"

module aes_controller #
(
	parameter IN_BUS_DATA_WIDTH = 32,
	parameter IN_FIFO_DEPTH = 256,

	parameter OUT_BUS_DATA_WIDTH = 32,
	parameter OUT_FIFO_DEPTH = 256,

	parameter ECB_SUPPORT =  1,
	parameter CBC_SUPPORT =  1,
	parameter CTR_SUPPORT =  1,
	parameter CFB_SUPPORT =  1,
	parameter OFB_SUPPORT =  1,
	parameter PCBC_SUPPORT = 1
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

localparam IN_FIFO_DATA_WIDTH = `BLK_S + 1; // {command bit, tlast bit, 1 x 128-bit AES block}
localparam IN_FIFO_ADDR_WIDTH = clogb2(IN_FIFO_DATA_WIDTH);

localparam OUT_FIFO_DATA_WIDTH = `BLK_S + 1; // {tlast bit, 1 x 128-bit AES block}
localparam OUT_FIFO_ADDR_WIDTH = clogb2(OUT_FIFO_DATA_WIDTH);

localparam [2:0] AES_GET_CMD = 3'b000;
localparam [2:0] AES_GET_KEY_128  = 3'b001;
localparam [2:0] AES_GET_KEY_256  = 3'b010;
localparam [2:0] AES_GET_IV = 3'b011;
localparam [2:0] AES_START = 3'b100;

// ============================================================================
// AES controller input stage signals

wire                          in_fifo_read_tvalid;
wire                          in_fifo_read_tready;
wire [IN_FIFO_DATA_WIDTH-1:0] in_fifo_rdata;
wire                          in_fifo_empty;

// ============================================================================
// AES controller processing stage signals

reg  [`BLK_S-1:0] aes_alg_in_blk;
reg  [`KEY_S-1:0] aes_alg_key;
wire [`BLK_S-1:0] aes_out_blk;
wire aes_op_in_progress;
reg  aes_decipher_mode;
reg  aes_key_exp_mode;
reg  aes_cipher_mode;
reg  aes_alg_start;
wire aes_alg_done;
reg  aes128_mode;
reg  aes256_mode;

reg [2:0]         state;
wire              get_iv;

reg fsm_cmd_state,
    fsm_key128_state,
    fsm_key256_state,
    fsm_iv_state,
    fsm_process_state;

reg last_blk;

reg  [`KEY_S-1:0] aes_key;
reg  [`WORD_S-1:0] aes_cmd;

reg [`IV_BITS-1:0]  iv;
wire [`IV_BITS-1:0] iv_next;
wire [`IV_BITS-1:0] cbc_iv;
wire [`IV_BITS-1:0] ctr_iv;
wire [`IV_BITS-1:0] cfb_iv;
wire [`IV_BITS-1:0] ofb_iv;
wire [`IV_BITS-1:0] pcbc_iv;

wire encryption_op;
wire decryption_op;
wire encrypt_flag;
wire decrypt_flag;

wire ecb_flag;
wire cbc_flag;
wire ctr_flag;
wire cfb_flag;
wire ofb_flag;
wire pcbc_flag;

wire op_done;
wire ecb_op_done;
wire cbc_op_done;
wire ctr_op_done;
wire cfb_op_done;
wire ofb_op_done;
wire pcbc_op_done;

reg [`BLK_S-1:0]  in_blk;
wire [`BLK_S-1:0] in_blk_next;
wire [`BLK_S-1:0] cbc_in_blk;
wire [`BLK_S-1:0] ecb_in_blk;
wire [`BLK_S-1:0] ctr_in_blk;
wire [`BLK_S-1:0] cfb_in_blk;
wire [`BLK_S-1:0] ofb_in_blk;
wire [`BLK_S-1:0] pcbc_in_blk;

wire [`BLK_S-1:0] out_blk_next;
wire [`BLK_S-1:0] cbc_out_blk;
wire [`BLK_S-1:0] ecb_out_blk;
wire [`BLK_S-1:0] ctr_out_blk;
wire [`BLK_S-1:0] cfb_out_blk;
wire [`BLK_S-1:0] ofb_out_blk;
wire [`BLK_S-1:0] pcbc_out_blk;

wire in_fifo_read_req;
wire need_iv;

wire store_out_blk;

genvar i;

// ============================================================================
// AES controller output stage signals

reg [OUT_FIFO_DATA_WIDTH-1:0] out_fifo_wdata;
reg out_fifo_write_tvalid;
wire out_fifo_write_tready;

wire out_fifo_almost_full;
wire out_fifo_full;
wire out_fifo_empty;

wire out_fifo_write_req;

// ============================================================================
// AES controller input stage

aes_controller_input #(
	.BUS_DATA_WIDTH(IN_BUS_DATA_WIDTH),

	.FIFO_ADDR_WIDTH(IN_FIFO_ADDR_WIDTH),
	.FIFO_DATA_WIDTH(IN_FIFO_DATA_WIDTH),
	.FIFO_SIZE(IN_FIFO_DEPTH)
) controller_input_block (
	.clk(clk),
	.reset(reset),

	.bus_data_wren(in_bus_data_wren),
	.bus_tlast(in_bus_tlast),
	.bus_data(in_bus_data),

	.in_fifo_read_tvalid(in_fifo_read_tvalid),
	.in_fifo_read_tready(in_fifo_read_tready),
	.in_fifo_rdata(in_fifo_rdata),
	.in_fifo_empty(in_fifo_empty),

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
	fsm_iv_state      = (state == AES_GET_IV);
	fsm_process_state = (state == AES_START);
end

assign need_iv =
                 cbc_flag ||
                 ctr_flag ||
                 cfb_flag ||
                 ofb_flag ||
                 pcbc_flag
                 ? 1'b1 : 1'b0;

assign in_blk_next =
                     pcbc_flag ? pcbc_in_blk :
                     cbc_flag  ? cbc_in_blk  :
                     ctr_flag  ? ctr_in_blk  :
                     cfb_flag  ? cfb_in_blk  :
                     ofb_flag  ? ofb_in_blk  :
                     ecb_flag  ? ecb_in_blk  :
                     {`BLK_S{1'b0}};

assign out_blk_next =
                      pcbc_flag ? pcbc_out_blk :
                      cbc_flag  ? cbc_out_blk  :
                      ctr_flag  ? ctr_out_blk  :
                      cfb_flag  ? cfb_out_blk  :
                      ofb_flag  ? ofb_out_blk  :
                      ecb_flag  ? ecb_out_blk  :
                      {`BLK_S{1'b0}};

assign iv_next =
                 pcbc_flag ? pcbc_iv :
                 cbc_flag  ? cbc_iv :
                 ctr_flag  ? ctr_iv :
                 cfb_flag  ? cfb_iv :
                 ofb_flag  ? ofb_iv :
                 {`IV_BITS{1'b0}};

assign op_done =
	pcbc_flag ? pcbc_op_done :
	cbc_flag  ? cbc_op_done  :
	ctr_flag  ? ctr_op_done  :
	cfb_flag  ? cfb_op_done  :
	ofb_flag  ? ofb_op_done  :
	ecb_flag  ? ecb_op_done  :
	1'b0;

assign encrypt_flag = is_encryption(aes_cmd);
assign decrypt_flag = is_decryption(aes_cmd);

assign encryption_op = encrypt_flag
                       || ctr_flag
                       || cfb_flag
                       || ofb_flag;

assign decryption_op = decrypt_flag
                       && !ctr_flag
                       && !cfb_flag
                       && !ofb_flag;
generate
if (ECB_SUPPORT) begin
	assign ecb_flag = is_ECB_op(aes_cmd);

	ecb ecb_mod(
		.data_blk(in_blk),

		.aes_alg_out_blk(aes_out_blk),
		.aes_alg_in_blk(ecb_in_blk),
		.aes_alg_done(aes_alg_done),

		.ecb_out_blk(ecb_out_blk),
		.ecb_op_done(ecb_op_done)
	);
end else begin
	assign ecb_flag = 1'b0;
end
endgenerate

generate
if (CBC_SUPPORT) begin
	assign cbc_flag = is_CBC_op(aes_cmd);

	cbc cbc_mod(
		.encryption(encrypt_flag),

		.data_blk(in_blk),

		.iv(iv),
		.iv_next(cbc_iv),

		.aes_alg_in_blk(cbc_in_blk),
		.aes_alg_out_blk(aes_out_blk),
		.aes_alg_done(aes_alg_done),

		.cbc_out_blk(cbc_out_blk),
		.cbc_op_done(cbc_op_done)
	);
end else begin
	assign cbc_flag = 1'b0;
end
endgenerate

generate
if (CTR_SUPPORT) begin
	assign ctr_flag = is_CTR_op(aes_cmd);

	ctr ctr_mod(
		.data_blk(in_blk),

		.iv(iv),
		.iv_next(ctr_iv),

		.aes_alg_in_blk(ctr_in_blk),
		.aes_alg_out_blk(aes_out_blk),
		.aes_alg_done(aes_alg_done),

		.ctr_op_done(ctr_op_done),
		.ctr_out_blk(ctr_out_blk)
	);
end else begin
	assign ctr_flag = 1'b0;
end
endgenerate

generate
if (PCBC_SUPPORT) begin
	assign pcbc_flag = is_PCBC_op(aes_cmd);

	pcbc pcbc_mod(
		.encryption(encrypt_flag),

		.data_blk(in_blk),

		.iv(iv),
		.iv_next(pcbc_iv),

		.aes_alg_in_blk(pcbc_in_blk),
		.aes_alg_out_blk(aes_out_blk),
		.aes_alg_done(aes_alg_done),

		.pcbc_op_done(pcbc_op_done),
		.pcbc_out_blk(pcbc_out_blk)
	);
end else begin
	assign pcbc_flag = 1'b0;
end
endgenerate

generate
if (CFB_SUPPORT) begin
	assign cfb_flag = is_CFB_op(aes_cmd);

	cfb cfb_mod(
		.encryption(encrypt_flag),

		.data_blk(in_blk),

		.iv(iv),
		.iv_next(cfb_iv),

		.aes_alg_in_blk(cfb_in_blk),
		.aes_alg_out_blk(aes_out_blk),
		.aes_alg_done(aes_alg_done),

		.cfb_op_done(cfb_op_done),
		.cfb_out_blk(cfb_out_blk)
	);
end else begin
	assign cfb_flag = 1'b0;
end
endgenerate

generate
if (OFB_SUPPORT) begin
	assign ofb_flag = is_OFB_op(aes_cmd);

	ofb ofb_mod(
		.data_blk(in_blk),

		.iv(iv),
		.iv_next(ofb_iv),

		.aes_alg_in_blk(ofb_in_blk),
		.aes_alg_out_blk(aes_out_blk),
		.aes_alg_done(aes_alg_done),

		.ofb_op_done(ofb_op_done),
		.ofb_out_blk(ofb_out_blk)
	);
end else begin
	assign ofb_flag = 1'b0;
end
endgenerate

/*
   * AES algorithm control blocks.
 */
always @(posedge clk) begin
	if (reset == 1'b1) begin
		aes_alg_start <= 1'b0;

		aes_decipher_mode <= 1'b0;
		aes_key_exp_mode <= 1'b0;
		aes_cipher_mode <= 1'b0;
	end else begin
		if (expand_key128_start || expand_key256_start) begin
			aes_cipher_mode <= 1'b0;
			aes_decipher_mode <= 1'b0;
			aes_key_exp_mode <= 1'b1;
		end else if (encrypt_start) begin
			aes_cipher_mode <= 1'b1;
			aes_decipher_mode <= 1'b0;
			aes_key_exp_mode <= 1'b0;
		end else if (decrypt_start) begin
			aes_cipher_mode <= 1'b0;
			aes_decipher_mode <= 1'b1;
			aes_key_exp_mode <= 1'b0;
		end

		/* Registered so the blocks can be retrieved from the FIFO */
		aes_alg_start <=
				encrypt_start       || decrypt_start ||
				expand_key128_start || expand_key256_start;
	end
end


always @(*) begin
	aes128_mode = is_128bit_key(aes_cmd);
	aes256_mode = is_256bit_key(aes_cmd);
	aes_alg_in_blk = in_blk_next;
	aes_alg_key = aes_key;
end

// AES algorithm
aes_top aes_mod(
	.clk(clk),
	.reset(reset),
	.en(aes_alg_start),

	.aes128_mode(aes128_mode),
	.aes256_mode(aes256_mode),

	.cipher_mode(aes_cipher_mode),
	.decipher_mode(aes_decipher_mode),
	.key_exp_mode(aes_key_exp_mode),

	.aes_op_in_progress(aes_op_in_progress),

	.aes_key(aes_alg_key),
	.aes_in_blk(aes_alg_in_blk),

	.aes_out_blk(aes_out_blk),
	.en_o(aes_alg_done)
);

assign out_fifo_write_req = out_fifo_write_tready && out_fifo_write_tvalid;
assign in_fifo_read_req = in_fifo_read_tready && in_fifo_read_tvalid;

assign get_iv = (fsm_iv_state && in_fifo_read_req);

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
					state <= AES_START;

					aes_key[`AES256_KEY_BITS-1 : `AES128_KEY_BITS] <= in_fifo_rdata;

					if (need_iv)
						state <= AES_GET_IV;

					if (aes256_mode)
						state <= AES_GET_KEY_256;
				end
			end
			AES_GET_KEY_256:
			begin
				if (in_fifo_read_req) begin
					aes_key[`AES128_KEY_BITS-1 : 0] <= in_fifo_rdata;
					state <= AES_START;

					if (need_iv)
						state <= AES_GET_IV;
				end
			end
			AES_GET_IV:
			begin
				if (in_fifo_read_req) begin
					state <= AES_START;
				end
			end
			AES_START:
			begin
				state <= AES_START;

				if (in_fifo_read_req) begin
					in_blk <= in_fifo_rdata[`BLK_S-1:0];
					last_blk <= in_fifo_rdata[`BLK_S];
				end

				if (op_done && last_blk) begin
					last_blk <= 1'b0;
					state <= AES_GET_CMD;
				end
			end
			default:
				state <= AES_GET_CMD;
		endcase
	end
end

assign in_fifo_read_tready =
	fsm_cmd_state      ||
	fsm_key128_state   ||
	fsm_key256_state   ||
	fsm_iv_state       ||
	(fsm_process_state && (out_fifo_write_tready && !aes_op_in_progress && !aes_alg_start));

/*
   * Start an AES crypto operation (key expansion/encryption/decryption) if:
   * - the 128-bit key is retrieved from the input FIFO
   * - the 256-bit key is retrieved from the input FIFO
   * - a data block is retrieved from the input FIFO
 */
assign expand_key128_start = (aes128_mode && in_fifo_read_req && fsm_key128_state);
assign expand_key256_start = (aes256_mode && in_fifo_read_req && fsm_key256_state);
assign encrypt_start = (encryption_op && in_fifo_read_req && fsm_process_state);
assign decrypt_start = (decryption_op && in_fifo_read_req && fsm_process_state);

assign store_out_blk = (aes_cipher_mode || aes_decipher_mode);

always @(posedge clk) begin
	if (get_iv)
		iv <= in_fifo_rdata;
	else if (op_done && store_out_blk)
		iv <= iv_next;
end

always @(posedge clk) begin
	if (reset)
		out_fifo_write_tvalid <= 1'b0;
	else begin
		if (op_done && store_out_blk) begin
			out_fifo_write_tvalid <= 1'b1;
			out_fifo_wdata <= {last_blk, out_blk_next};
		end

		if (out_fifo_write_req)
			out_fifo_write_tvalid <= 1'b0;
	end
end

// ============================================================================
// AES controller output stage

aes_controller_output #(
	.BUS_TDATA_WIDTH(OUT_BUS_DATA_WIDTH),
	.FIFO_SIZE(OUT_FIFO_DEPTH),
	.FIFO_ADDR_WIDTH(OUT_FIFO_ADDR_WIDTH),
	.FIFO_DATA_WIDTH(OUT_FIFO_DATA_WIDTH)
) controller_output_block (
	.clk(clk),
	.resetn(!reset),

	.fifo_write_tready(out_fifo_write_tready),
	.fifo_write_tvalid(out_fifo_write_tvalid),
	.fifo_wdata(out_fifo_wdata),

	.fifo_almost_full(out_fifo_almost_full),
	.fifo_full(out_fifo_full),
	.fifo_empty(out_fifo_empty),

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
	AES_GET_IV:
	begin
		if (in_fifo_read_req) begin
			$display("AES PROCESSING: IV - blk %0d: %H", s_in_blk_cnt, in_fifo_rdata);
			s_in_blk_cnt = s_in_blk_cnt + 1;
		end
	end
	AES_START:
	begin
		if (in_fifo_read_req) begin
			$display("AES PROCESSING: input block no %0d: %H", s_in_blk_cnt, in_fifo_rdata);
			s_in_blk_cnt = s_in_blk_cnt + 1;
		end
	end
	endcase

	if (op_done && (aes_cipher_mode || aes_decipher_mode)) begin
		$display("AES PROCESSING: computed aes block no %0d: %H", s_out_blk_cnt, {last_blk, out_blk_next});
		s_out_blk_cnt = s_out_blk_cnt + 1;
	end
end
`endif

endmodule
