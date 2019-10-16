// CBC encryption stress test
task testcase1();
	localparam AES_KEY128 = `KEY_S'h5468617473206D79204B756E67204675;
	localparam AES_IV = `BLK_S'h54776F204F6E65204E696E652054776F;

	localparam test_blocks_no = 1000;

	localparam plaintext_fn = "cbc_plaintext.txt";
	localparam ciphertext_fn = "cbc_ciphertext.txt";

	integer total_blocks;
	integer i, j;

	reg [0:`WORD_S-1]  cmd;
	reg [0:`KEY_S-1]   key;
	reg [0:`IV_BITS-1] iv;

	queue_wrapper#(`BLK_S) plaintext_queue;
	queue_wrapper#(`BLK_S) ciphertext_queue;
	queue_wrapper#(`WORD_S) expected_results_queue;

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
		queue_tester.q_push_back32_rev(ciphertext_queue.get(i), expected_results_queue);

	$display("Starting Testcase: ECB encryption stress test");

	// Prepare encryption request
	cmd = `CBC_ENCRYPT_128;
	key = AES_KEY128;
	iv = AES_IV;

	aes_tester.aes_send_request(cmd, key, iv, plaintext_queue, total_blocks);

	wait(comparison_cnt == total_blocks * 4);

	results.compare(expected_results_queue);
	results.clear();
	$display("Testcase 1 done without errors.\n");
endtask
