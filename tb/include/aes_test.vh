`ifndef AES_TEST_VH
`define AES_TEST_VH

`include "test_fc.vh"
`include "aes.vh"

class aes_test #(
	integer KEY_SIZE,
	type master_agent_t);

	master_agent_t master_agent;

	function new(master_agent_t master_agnt);
		master_agent = master_agnt;
	endfunction

	task gen_rand_transaction(ref axi4stream_transaction wr_transaction);
		wr_transaction = master_agent.driver.create_transaction("Master VIP write transaction");
		wr_transaction.set_xfer_alignment(XIL_AXI4STREAM_XFER_RANDOM);
		WR_TRANSACTION_FAIL: assert(wr_transaction.randomize());
	endtask

	task gen_transaction(
		input queue#(8) data,
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
		input reg [KEY_SIZE-1:0] key,
		input reg [`IV_BITS-1:0] iv,
		input queue#(`BLK_S) payload_queue,
		input integer blks_no,
		input queue#(`WORD_S) req_queue,
		input bit send_iv
	);
		integer i;
		integer size;
		tester #(
			.WIDTH(`BLK_S),
			.QUEUE_DATA_WIDTH(`WORD_S)) blk_tester;

		tester #(
			.WIDTH(KEY_SIZE),
			.QUEUE_DATA_WIDTH(`WORD_S)) key_tester;

		blk_tester = new();

		req_queue.push_back(cmd);
		key_tester.q_push_back32_rev(key_tester.reverse_blk8(key), req_queue);
		if (send_iv)
			blk_tester.q_push_back32_rev(blk_tester.reverse_blk8(iv), req_queue);

		for (i = 0; i < blks_no; i = i + 1) begin
			reg [`BLK_S-1:0] payload_data = payload_queue.get(i);
			blk_tester.q_push_back32_rev(blk_tester.reverse_blk8(payload_data), req_queue);
		end
	endtask

	task aes_send_request(
		input reg [`WORD_S-1:0]  cmd,
		input reg [KEY_SIZE-1:0] key,
		input reg [`IV_BITS-1:0] iv,
		input queue#(`BLK_S) payload_queue,
		input integer blks_no,
		input bit send_iv
	);
		queue#(`WORD_S) req_queue;
		queue#(8) req_queue_8b;

		req_queue = new();
		req_queue_8b = new();

		aes_create_req(cmd, key, iv, payload_queue, blks_no, req_queue, send_iv);

		req_queue.unpack_8b_rev(req_queue_8b);
		gen_transaction(req_queue_8b, 1);
	endtask

endclass

`endif
