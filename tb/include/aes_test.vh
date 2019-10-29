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

	// reverse_blk8 is used to reverse AES blocks before sending them on
	// the AXI Stream interface. In the AES standard, blocks are labeled
	// from left to right (LSB -> MSB), but in HDL we process them from
	// right to left (MSB <- LSB). Reversing the blocks is less confusing
	// than swapping each 32-bit word individually.
	static function [`BLK_S-1:0] reverse_blk8(input [`BLK_S-1:0] blk);
		integer i;
		for (i = 0; i < `BLK_S / `BYTE_S; i=i+1)
			reverse_blk8[i*`BYTE_S +: `BYTE_S] = blk[(`BLK_S / `BYTE_S - i - 1)*`BYTE_S +: `BYTE_S];
	endfunction

	static function bit is_cbc_op(input reg [`WORD_S-1:0] cmd);
		is_cbc_op = cmd[`CBC_MODE_BIT];
	endfunction

	task gen_rand_transaction(ref axi4stream_transaction wr_transaction);
		wr_transaction = master_agent.driver.create_transaction("Master VIP write transaction");
		wr_transaction.set_xfer_alignment(XIL_AXI4STREAM_XFER_RANDOM);
		WR_TRANSACTION_FAIL: assert(wr_transaction.randomize());
	endtask

	task gen_transaction(
		input queue_wrapper#(8) data,
		input last
	);
		for (int i = 0; i < data.size(); i = i + 4) begin
			axi4stream_transaction wr_transaction;

			gen_rand_transaction(wr_transaction);
			wr_transaction.set_delay(0);
			wr_transaction.set_id(0);
			wr_transaction.set_last(0);
			wr_transaction.set_data('{data.get(i+3), data.get(i+2), data.get(i+1), data.get(i)});

			if (i == data.size() - 4 && last == 1) begin
				wr_transaction.set_last(1);
			end

			master_agent.driver.send(wr_transaction);
		end
	endtask

	task aes_create_req(
		input reg [`WORD_S-1:0]  cmd,
		input reg [`KEY_S-1:0]   key,
		input reg [`IV_BITS-1:0] iv,
		input queue_wrapper#(`BLK_S) payload_queue,
		input integer blks_no,
		input queue_wrapper#(`WORD_S) req_queue
	);
		integer i;
		integer size;
		tester #(
			.WIDTH(`BLK_S),
			.QUEUE_DATA_WIDTH(`WORD_S)) queue_tester;

		queue_tester = new();

		req_queue.push_back(cmd);
		queue_tester.q_push_back32_rev(reverse_blk8(key), req_queue);
		if (is_cbc_op(cmd))
			queue_tester.q_push_back32_rev(reverse_blk8(iv), req_queue);

		for (i = 0; i < blks_no; i = i + 1) begin
			reg [`BLK_S-1:0] payload_data = payload_queue.get(i);
			queue_tester.q_push_back32_rev(reverse_blk8(payload_data), req_queue);
		end
	endtask

	task aes_send_request(
		input reg [`WORD_S-1:0]  cmd,
		input reg [`KEY_S-1:0]   key,
		input reg [`IV_BITS-1:0] iv,
		input queue_wrapper#(`BLK_S) payload_queue,
		input integer blks_no
	);
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
