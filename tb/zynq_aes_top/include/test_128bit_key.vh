task test_128bit_key();
	test_128bit_key_cbc();
	test_128bit_key_ecb();
endtask

task test_128bit_key_cbc();
	test_128bit_key_cbc_enc();
	test_128bit_key_cbc_dec();
endtask

task test_128bit_key_ecb();
	test_128bit_key_ecb_enc();
	test_128bit_key_ecb_dec();
endtask

// CBC encryption stress test
task test_128bit_key_cbc_enc();
	localparam testcase_name = "CBC encryption stress test (128-bit key)";
	localparam AES_KEY128 = 'h5468617473206D79204B756E67204675;
	localparam AES_IV = 'h54776F204F6E65204E696E652054776F;

	localparam test_blocks_no = 256;

	localparam plaintext_fn = "cbc_plaintext.txt";
	localparam ciphertext_fn = "cbc_ciphertext.txt";

	integer total_blocks;
	integer i, j;

	reg [`WORD_S-1:0]          cmd;
	reg [`AES128_KEY_BITS-1:0] key;
	reg [`IV_BITS-1:0]         iv;

	queue_wrapper#(`BLK_S) plaintext_queue;
	queue_wrapper#(`BLK_S) ciphertext_queue;
	queue_wrapper#(`WORD_S) expected_results_queue;

	cmd = {`WORD_S{1'b0}};
	comparison_cnt = 0;

	ciphertext_queue = new();
	plaintext_queue = new();
	expected_results_queue = new();

	plaintext_queue.fill_from_file(plaintext_fn);
	ciphertext_queue.fill_from_file(ciphertext_fn);

	if (test_blocks_no > plaintext_queue.size()) begin
		$display("ERROR: Cannot send %d blocks!", test_blocks_no);
		$display("ERROR: Only %d precomputed blocks available!", plaintext_queue.size());
		$finish;
	end
	total_blocks = test_blocks_no;
	$display("%s: START", testcase_name);
	$display("%s: Sending %d AES blocks.", testcase_name, total_blocks);

	for (i = 0; i < total_blocks; i++)
		queue_tester.q_push_back32_rev(queue_tester.reverse_blk8(ciphertext_queue.get(i)),
				expected_results_queue);

	// Prepare encryption request
	cmd = set_encryption_op_bit(cmd) |
	      set_key_128_bit(cmd) |
	      set_CBC_mode_bit(cmd);
	key = AES_KEY128;
	iv = AES_IV;

	aes_tester128.aes_send_request(cmd, key, iv, plaintext_queue, total_blocks);

	wait(comparison_cnt == total_blocks * 4);

	if (results.compare(expected_results_queue))
		$display("%s: FAIL!", testcase_name);
	results.clear();

	$display("%s: PASS!", testcase_name);
endtask

// CBC decryption stress test
task test_128bit_key_cbc_dec();
	localparam testcase_name = "CBC decryption stress test (128-bit key)";
	localparam AES_KEY128 = 'h5468617473206D79204B756E67204675;
	localparam AES_IV = 'h54776F204F6E65204E696E652054776F;

	localparam test_blocks_no = 256;

	localparam plaintext_fn = "cbc_plaintext.txt";
	localparam ciphertext_fn = "cbc_ciphertext.txt";

	integer total_blocks;
	integer i, j;

	reg [`WORD_S-1:0]  cmd;
	reg [`KEY_S-1:0]   key;
	reg [`IV_BITS-1:0] iv;

	queue_wrapper#(`BLK_S) plaintext_queue;
	queue_wrapper#(`BLK_S) ciphertext_queue;
	queue_wrapper#(`WORD_S) expected_results_queue;

        cmd = {`WORD_S{1'b0}};
	comparison_cnt = 0;

	ciphertext_queue = new();
	plaintext_queue = new();
	expected_results_queue = new();

	plaintext_queue.fill_from_file(plaintext_fn);
	ciphertext_queue.fill_from_file(ciphertext_fn);

	if (test_blocks_no > plaintext_queue.size()) begin
		$display("ERROR: Cannot send %d blocks!", test_blocks_no);
		$display("ERROR: Only %d precomputed blocks available!", plaintext_queue.size());
		$finish;
	end
	total_blocks = test_blocks_no;
	$display("%s: START", testcase_name);
	$display("%s: Sending %d AES blocks.", testcase_name, total_blocks);

	for (i = 0; i < total_blocks; i++)
		queue_tester.q_push_back32_rev(queue_tester.reverse_blk8(plaintext_queue.get(i)),
				expected_results_queue);

	// Prepare encryption request
	cmd = set_decryption_op_bit(cmd) |
	      set_key_128_bit(cmd) |
	      set_CBC_mode_bit(cmd);
	key = AES_KEY128;
	iv = AES_IV;

	aes_tester128.aes_send_request(cmd, key, iv, ciphertext_queue, total_blocks);

	wait(comparison_cnt == total_blocks * 4);

	if (results.compare(expected_results_queue))
		$display("%s: FAIL!", testcase_name);
	results.clear();
	$display("%s: PASS!", testcase_name);
endtask

// ECB encryption stress test
task test_128bit_key_ecb_enc();
	localparam testcase_name = "ECB encryption stress test (128-bit key)";
	localparam AES_KEY128 = 'h5468617473206D79204B756E67204675;

	localparam test_blocks_no = 256;

	localparam plaintext_fn = "ecb_plaintext.txt";
	localparam ciphertext_fn = "ecb_ciphertext.txt";

	integer total_blocks;
	integer i, j;

	reg [`WORD_S-1:0]  cmd;
	reg [`KEY_S-1:0]   key;
	reg [`IV_BITS-1:0] iv;

	queue_wrapper#(`BLK_S) plaintext_queue;
	queue_wrapper#(`BLK_S) ciphertext_queue;
	queue_wrapper#(`WORD_S) expected_results_queue;

        cmd = {`WORD_S{1'b0}};
	comparison_cnt = 0;

	ciphertext_queue = new();
	plaintext_queue = new();
	expected_results_queue = new();

	plaintext_queue.fill_from_file(plaintext_fn);
	ciphertext_queue.fill_from_file(ciphertext_fn);

	if (test_blocks_no > plaintext_queue.size()) begin
		$display("ERROR: Cannot send %d blocks!", test_blocks_no);
		$display("ERROR: Only %d precomputed blocks available!", plaintext_queue.size());
		$finish;
	end
	total_blocks = test_blocks_no;
	$display("%s: START", testcase_name);
	$display("%s: Sending %d AES blocks.", testcase_name, total_blocks);

	for (i = 0; i < total_blocks; i++)
		queue_tester.q_push_back32_rev(queue_tester.reverse_blk8(ciphertext_queue.get(i)), expected_results_queue);

	// Prepare encryption request
	cmd = set_encryption_op_bit(cmd) |
	      set_key_128_bit(cmd) |
	      set_ECB_mode_bit(cmd);
	key = AES_KEY128;
	iv = {`IV_BITS{1'b0}};

	aes_tester128.aes_send_request(cmd, key, iv, plaintext_queue, total_blocks);

	wait(comparison_cnt == total_blocks * 4);

	if (results.compare(expected_results_queue))
		$display("%s: FAIL!", testcase_name);
	results.clear();
	$display("%s: PASS!", testcase_name);
endtask

// ECB decryption stress test
task test_128bit_key_ecb_dec();
	localparam testcase_name = "ECB decryption stress test (128-bit key)";
	localparam AES_KEY128 = 'h5468617473206D79204B756E67204675;

	localparam test_blocks_no = 256;

	localparam plaintext_fn = "ecb_plaintext.txt";
	localparam ciphertext_fn = "ecb_ciphertext.txt";

	integer total_blocks;
	integer i, j;

	reg [`WORD_S-1:0]  cmd;
	reg [`KEY_S-1:0]   key;
	reg [`IV_BITS-1:0] iv;

	queue_wrapper#(`BLK_S) plaintext_queue;
	queue_wrapper#(`BLK_S) ciphertext_queue;
	queue_wrapper#(`WORD_S) expected_results_queue;

        cmd = {`WORD_S{1'b0}};
	comparison_cnt = 0;

	ciphertext_queue = new();
	plaintext_queue = new();
	expected_results_queue = new();

	plaintext_queue.fill_from_file(plaintext_fn);
	ciphertext_queue.fill_from_file(ciphertext_fn);

	if (test_blocks_no > plaintext_queue.size()) begin
		$display("ERROR: Cannot send %d blocks!", test_blocks_no);
		$display("ERROR: Only %d precomputed blocks available!", plaintext_queue.size());
		$finish;
	end
	total_blocks = test_blocks_no;
	$display("%s: START", testcase_name);
	$display("%s: Sending %d AES blocks.", testcase_name, total_blocks);

	for (i = 0; i < total_blocks; i++)
		queue_tester.q_push_back32_rev(queue_tester.reverse_blk8(plaintext_queue.get(i)),
				expected_results_queue);

	// Prepare decryption request
	cmd = set_decryption_op_bit(cmd) |
	      set_key_128_bit(cmd) |
	      set_ECB_mode_bit(cmd);
	key = AES_KEY128;
	iv = {`IV_BITS{1'b0}};

	aes_tester128.aes_send_request(cmd, key, iv, ciphertext_queue, total_blocks);

	wait(comparison_cnt == total_blocks * 4);

	if (results.compare(expected_results_queue))
		$display("%s: FAIL!", testcase_name);
	results.clear();
	$display("%s: PASS!", testcase_name);
endtask
