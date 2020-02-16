`include "aes.vh"

module aes_controller #
(
	IN_BUS_DATA_WIDTH = 32,
	IN_FIFO_DEPTH = 256,

	OUT_BUS_DATA_WIDTH = 32,
	OUT_FIFO_DEPTH = 256,

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
localparam [2:0] AES_GET_KEY_128  = 3'b010;
localparam [2:0] AES_GET_KEY_256  = 3'b001;
localparam [2:0] AES_GET_IV = 3'b011;
localparam [2:0] AES_START = 3'b101;

// ============================================================================
// AES controller input stage signals

wire                          in_fifo_read_tvalid;
reg                           in_fifo_read_tready;
wire [IN_FIFO_DATA_WIDTH-1:0] in_fifo_rdata;
wire                          in_fifo_empty;

// ============================================================================
// AES controller processing stage signals

reg [2:0]         state;
wire              aes_done;
wire              get_iv;

reg last_blk;

reg [`KEY_S-1:0]  aes_key;
reg [`WORD_S-1:0] aes_cmd;

reg [`IV_BITS-1:0]  iv;
wire [`IV_BITS-1:0] iv_next;
wire [`IV_BITS-1:0] cbc_iv;
wire [`IV_BITS-1:0] ctr_iv;
wire [`IV_BITS-1:0] cfb_iv;
wire [`IV_BITS-1:0] ofb_iv;
wire [`IV_BITS-1:0] pcbc_iv;

reg aes_decipher_mode;
reg aes_key_exp_mode;
reg aes_cipher_mode;
reg aes_start;

wire aes_op_in_progress;
wire aes_start_decipher;
wire aes_start_key_exp;
wire aes_start_cipher;

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

reg [`BLK_S-1:0]  in_blk;
wire [`BLK_S-1:0] in_blk_next;
wire [`BLK_S-1:0] cbc_in_blk;
wire [`BLK_S-1:0] ecb_in_blk;
wire [`BLK_S-1:0] ctr_in_blk;
wire [`BLK_S-1:0] cfb_in_blk;
wire [`BLK_S-1:0] ofb_in_blk;
wire [`BLK_S-1:0] pcbc_in_blk;

wire [`BLK_S-1:0] out_blk;
wire [`BLK_S-1:0] out_blk_next;
wire [`BLK_S-1:0] cbc_out_blk;
wire [`BLK_S-1:0] ecb_out_blk;
wire [`BLK_S-1:0] ctr_out_blk;
wire [`BLK_S-1:0] cfb_out_blk;
wire [`BLK_S-1:0] ofb_out_blk;
wire [`BLK_S-1:0] pcbc_out_blk;

wire aes128_mode;
wire aes256_mode;

wire in_fifo_read_req;
wire need_iv;

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

assign aes_start_cipher = aes_start && aes_cipher_mode;
assign aes_start_decipher = aes_start && aes_decipher_mode;
assign aes_start_key_exp = aes_start && aes_key_exp_mode;

assign aes128_mode = is_128bit_key(aes_cmd);
assign aes256_mode = is_256bit_key(aes_cmd);

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
		.in_blk(in_blk),
		.out_blk(out_blk),

		.in_blk_next(ecb_in_blk),
		.out_blk_next(ecb_out_blk)
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
		.decryption(decrypt_flag),

		.in_blk(in_blk),
		.out_blk(out_blk),
		.iv(iv),

		.in_blk_next(cbc_in_blk),
		.out_blk_next(cbc_out_blk),
		.iv_next(cbc_iv)
	);
end else begin
	assign cbc_flag = 1'b0;
end
endgenerate

generate
if (CTR_SUPPORT) begin
	assign ctr_flag = is_CTR_op(aes_cmd);

	ctr ctr_mod(
		.in_blk(in_blk),
		.out_blk(out_blk),
		.iv(iv),

		.in_blk_next(ctr_in_blk),
		.out_blk_next(ctr_out_blk),
		.iv_next(ctr_iv)
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
		.decryption(decrypt_flag),

		.in_blk(in_blk),
		.out_blk(out_blk),
		.iv(iv),

		.in_blk_next(pcbc_in_blk),
		.out_blk_next(pcbc_out_blk),
		.iv_next(pcbc_iv)
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

		.in_blk(in_blk),
		.out_blk(out_blk),
		.iv(iv),

		.in_blk_next(cfb_in_blk),
		.out_blk_next(cfb_out_blk),
		.iv_next(cfb_iv)
	);
end else begin
	assign cfb_flag = 1'b0;
end
endgenerate

generate
if (OFB_SUPPORT) begin
	assign ofb_flag = is_OFB_op(aes_cmd);

	ofb ofb_mod(
		.in_blk(in_blk),
		.out_blk(out_blk),
		.iv(iv),

		.in_blk_next(ofb_in_blk),
		.out_blk_next(ofb_out_blk),
		.iv_next(ofb_iv)
	);
end else begin
	assign ofb_flag = 1'b0;
end
endgenerate

// AES algorithm
aes_top aes_mod(
	.clk(clk),
	.reset(reset),
	.en(aes_start),

	.aes128_mode(aes128_mode),
	.aes256_mode(aes256_mode),

	.cipher_mode(aes_cipher_mode),
	.decipher_mode(aes_decipher_mode),
	.key_exp_mode(aes_key_exp_mode),

	.aes_op_in_progress(aes_op_in_progress),

	.aes_key(aes_key),
	.aes_in_blk(in_blk_next),

	.aes_out_blk(out_blk),
	.en_o(aes_done)
);

assign out_fifo_write_req = out_fifo_write_tready && out_fifo_write_tvalid;
assign in_fifo_read_req = in_fifo_read_tready && in_fifo_read_tvalid;

assign get_iv = (state == AES_GET_IV && in_fifo_read_req);

always @(posedge clk) begin
	if (reset == 1'b1) begin
		aes_decipher_mode <= 1'b0;
		aes_key_exp_mode <= 1'b0;
		aes_cipher_mode <= 1'b1;

		in_fifo_read_tready <= 1'b0;
		aes_key <= {`KEY_S{1'b0}};
		aes_cmd <= {`CMD_BITS{1'b0}};
		state <= AES_GET_CMD;
		in_blk <= {`BLK_S{1'b0}};
		last_blk <= 1'b0;
	end
	else begin
		in_fifo_read_tready <= 1'b0;
		aes_start <= 1'b0;

		case (state)
			AES_GET_CMD:
			begin
				in_fifo_read_tready <= 1'b1;

				if (in_fifo_read_req) begin
					aes_cmd <= in_fifo_rdata[`CMD_BITS-1:0];

					in_fifo_read_tready <= 1'b0;
					state <= AES_GET_KEY_128;
				end
			end
			AES_GET_KEY_128:
			begin
				in_fifo_read_tready <= 1'b1;

				aes_decipher_mode <= 1'b0;
				aes_key_exp_mode <= 1'b0;
				aes_cipher_mode <= 1'b0;

				if (in_fifo_read_req) begin
					state <= AES_START;

					in_fifo_read_tready <= 1'b0;

					aes_key[`AES128_KEY_BITS-1 : 0] <= in_fifo_rdata;
					aes_key_exp_mode <= 1'b1;
					aes_start <= 1'b1;

					if (need_iv)
						state <= AES_GET_IV;

					if (aes256_mode) begin
						state <= AES_GET_KEY_256;
						aes_start <= 1'b0;
					end
				end
			end
			AES_GET_KEY_256:
			begin
				in_fifo_read_tready <= 1'b1;

				if (in_fifo_read_req) begin
					aes_key[`AES256_KEY_BITS-1 : `AES128_KEY_BITS] <= in_fifo_rdata;
					in_fifo_read_tready <= 1'b0;
					state <= AES_START;
					aes_start <= 1'b1;

					if (need_iv)
						state <= AES_GET_IV;
				end
			end
			AES_GET_IV:
			begin
				in_fifo_read_tready <= 1'b1;

				if (in_fifo_read_req) begin
					in_fifo_read_tready <= 1'b0;
					state <= AES_START;
				end
			end
			AES_START:
			begin
				state <= AES_START;

				if (out_fifo_write_tready && !aes_op_in_progress && !aes_start) begin
					in_fifo_read_tready <= 1'b1;
				end

				if (in_fifo_read_req) begin
					aes_key_exp_mode <= 1'b0;
					aes_cipher_mode <= encryption_op;
					aes_decipher_mode <= decryption_op;

					in_fifo_read_tready <= 1'b0;
					in_blk <= in_fifo_rdata[`BLK_S-1:0];
					last_blk <= in_fifo_rdata[`BLK_S];
					aes_start <= 1'b1;
				end

				if (aes_done && last_blk) begin
					last_blk <= 1'b0;
					state <= AES_GET_CMD;
				end
			end
			default:
				state <= AES_GET_CMD;
		endcase
	end
end

always @(posedge clk) begin
	if (get_iv)
		iv <= in_fifo_rdata;
	else if (aes_done && (aes_cipher_mode || aes_decipher_mode))
		iv <= iv_next;
end

always @(posedge clk) begin
	if (reset)
		out_fifo_write_tvalid <= 1'b0;
	else begin
		if (aes_done && (aes_cipher_mode || aes_decipher_mode)) begin
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

`ifdef SIMULATION_VERBOSE_EXTREME
integer s_in_blk_cnt = 0;
integer s_in_cmd_cnt = 0;
integer s_out_blk_cnt = 0;

always @(posedge clk) begin
	case (state)
	AES_GET_CMD:
	begin
		if (in_fifo_read_req) begin
			$display("AES PROCESSING: cmd no %d: %H", s_in_cmd_cnt, in_fifo_rdata[`CMD_BITS-1:0]);
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
			$display("AES PROCESSING: input block no %d: %H", s_in_blk_cnt, in_fifo_rdata);
			s_in_blk_cnt = s_in_blk_cnt + 1;
		end
	end
	endcase

	if (aes_done && (aes_cipher_mode || aes_decipher_mode)) begin
		$display("AES PROCESSING: computed aes block no %0d: %H", s_out_blk_cnt, {last_blk, out_blk_next});
		s_out_blk_cnt = s_out_blk_cnt + 1;
	end
end
`endif

endmodule
