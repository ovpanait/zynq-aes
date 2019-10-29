// ECB decryption stress test
task testcase3();
	localparam AES_KEY128 = `KEY_S'h5468617473206D79204B756E67204675;

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
	$display("Sending %d AES blocks.", total_blocks);

	for (i = 0; i < total_blocks; i++)
		queue_tester.q_push_back32_rev(aes_tester.reverse_blk8(plaintext_queue.get(i)), expected_results_queue);

	$display("Starting Testcase: ECB encryption stress test");

	// Prepare decryption request
	cmd = set_decryption_op_bit(cmd) |
	      set_key_128_bit(cmd) |
	      set_ECB_mode_bit(cmd);
	key = AES_KEY128;
	iv = {`IV_BITS{1'b0}};

	aes_tester.aes_send_request(cmd, key, iv, ciphertext_queue, total_blocks);

	wait(comparison_cnt == total_blocks * 4);

	results.compare(expected_results_queue);
	results.clear();
	$display("Testcase 3 done without errors.\n");
endtask
