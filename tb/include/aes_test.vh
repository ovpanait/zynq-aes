`ifndef AES_TEST_VH
`define AES_TEST_VH

`include "test_fc.vh"
`include "aes.vh"

class aes_test #(
	type master_agent_t);

	master_agent_t master_agent;

	function new(master_agent_t master_agnt);
		master_agent = master_agnt;
	endfunction

	// Data passed by the kernel has the bytes swapped due to the way it is represented in the 16 byte
	// buffer (data from the buffer gets converted to little endian 32-bit words and sent on the axi bus)
	static function [0:`WORD_S-1] swap_bytes32(input [0:`WORD_S-1] data);
		integer i;
		for (i = 0; i < `WORD_S / `BYTE_S; i=i+1)
			swap_bytes32[i*`BYTE_S +: `BYTE_S] = data[(`WORD_S / `BYTE_S - i - 1)*`BYTE_S +: `BYTE_S];
	endfunction

	static function [0:`BLK_S-1] swap_blk(input [0:`BLK_S-1] blk);
		integer i;
		for (i = 0; i < `BLK_S / `WORD_S; i=i+1)
			swap_blk[i*`WORD_S +: `WORD_S] = swap_bytes32(blk[i*`WORD_S +: `WORD_S]);
	endfunction

	static function bit is_cbc_op(input reg [`WORD_S-1:0] cmd);
		is_cbc_op = (cmd == `CBC_DECRYPT_128) || (cmd == `CBC_ENCRYPT_128);
	endfunction

	task gen_rand_transaction;
		ref axi4stream_transaction wr_transaction;

		wr_transaction = master_agent.driver.create_transaction("Master VIP write transaction");
		wr_transaction.set_xfer_alignment(XIL_AXI4STREAM_XFER_RANDOM);
		WR_TRANSACTION_FAIL: assert(wr_transaction.randomize());
	endtask

	task gen_transaction;
		input queue_wrapper#(8) data;
		input last;

		for (int i = 0; i < data.size(); i = i + 4) begin
			xil_axi4stream_data_byte data_dbg[4];
			axi4stream_transaction   wr_transaction; 

			gen_rand_transaction(wr_transaction);
			wr_transaction.set_data('{data.get(i+3), data.get(i+2), data.get(i+1), data.get(i)});

			wr_transaction.set_last(0);
			if (i == data.size() - 4 && last == 1) begin
				wr_transaction.set_last(1);
			end

			wr_transaction.get_data(data_dbg);

			master_agent.driver.send(wr_transaction);
		end
	endtask

	task aes_create_req;
		input reg [0:`WORD_S-1]  cmd;
		input reg [0:`KEY_S-1]   key;
		input reg [0:`IV_BITS-1] iv;
		input queue_wrapper#(`BLK_S) payload_queue;
		input integer blks_no;
		input queue_wrapper#(`WORD_S) req_queue;

		integer i;
		integer size;
		tester #(
			.WIDTH(`BLK_S),
			.QUEUE_DATA_WIDTH(`WORD_S)) queue_tester;

		queue_tester = new();

		req_queue.push_back(cmd);
		queue_tester.q_push_back32_rev(swap_blk(key), req_queue);
		if (is_cbc_op(cmd))
			queue_tester.q_push_back32_rev(swap_blk(iv), req_queue);

		for (i = 0; i < blks_no; i = i + 1) begin
			reg [0:`BLK_S-1] payload_data = payload_queue.get(i);
			queue_tester.q_push_back32_rev(swap_blk(payload_data), req_queue);
		end
	endtask

	task aes_send_request;
		input reg [0:`WORD_S-1]  cmd;
		input reg [0:`KEY_S-1]   key;
		input reg [0:`IV_BITS-1] iv;
		input queue_wrapper#(`BLK_S) payload_queue;
		input integer blks_no;

		queue_wrapper#(`WORD_S) req_queue;
		queue_wrapper#(8) req_queue_8b;

		req_queue = new();
		req_queue_8b = new();

		aes_create_req(cmd, key, iv, payload_queue, blks_no, req_queue);

		req_queue.unpack_8b_rev(req_queue_8b);
		gen_transaction(req_queue_8b, 1);
	endtask


endclass

`endif
