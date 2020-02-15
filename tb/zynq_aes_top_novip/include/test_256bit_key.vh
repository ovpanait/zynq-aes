task test_256bit_key();
	test_256bit_key_cbc();
	test_256bit_key_ecb();
endtask

task test_256bit_key_cbc();
	test_256bit_key_cbc_enc();
	test_256bit_key_cbc_dec();
endtask

task test_256bit_key_ecb();
	test_256bit_key_ecb_enc();
	test_256bit_key_ecb_dec();
endtask

// CBC encryption stress test
task test_256bit_key_cbc_enc();
	localparam testcase_name = "CBC encryption stress test (256-bit key)";
	localparam AES_KEY256 = 'hb20394f27f88cb8fa5b9b8a95a123ab9853eb5a9f24471f07871a2b458f8180e;
	localparam AES_IV = 'hb53f62538a064bc49bf03f2dffda050d;

	localparam plaintext_fn = "cbc_plaintext_256.txt";
	localparam ciphertext_fn = "cbc_ciphertext_256.txt";

	integer total_blocks;
	integer i, j;

	reg [`WORD_S-1:0]          cmd;
	reg [`AES256_KEY_BITS-1:0] key;
	reg [`IV_BITS-1:0]         iv;

	queue_wrapper#(`BLK_S) plaintext_queue;
	queue_wrapper#(`BLK_S) ciphertext_queue;

	cmd = {`WORD_S{1'b0}};

	ciphertext_queue = new();
	plaintext_queue = new();

	plaintext_queue.fill_from_file(plaintext_fn);
	ciphertext_queue.fill_from_file(ciphertext_fn);

	total_blocks = 1 + ($urandom() % plaintext_queue.size()) % (4*DATA_FIFO_SIZE);
	$display("%s: START", testcase_name);
	$display("%s: Sending %d AES blocks.", testcase_name, total_blocks);

	// Prepare encryption request
	cmd = set_encryption_op_bit(cmd) |
	      set_key_256_bit(cmd) |
	      set_CBC_mode_bit(cmd);
	key = AES_KEY256;
	iv = AES_IV;

	bus_sem.get(1);
	for (i = 0; i < total_blocks; i++)
		axis_slave_queue_add128(ciphertext_queue.get(i), i == total_blocks - 1);

	aes_send_request(cmd, key, 256, iv, 1, plaintext_queue, total_blocks);
	wait_for_transfer();
	bus_sem.put(1);
endtask

// CBC decryption stress test
task test_256bit_key_cbc_dec();
	localparam testcase_name = "CBC decryption stress test (256-bit key)";
	localparam AES_KEY256 = 'hb20394f27f88cb8fa5b9b8a95a123ab9853eb5a9f24471f07871a2b458f8180e;
	localparam AES_IV = 'hb53f62538a064bc49bf03f2dffda050d;

	localparam test_blocks_no = 32;

	localparam plaintext_fn = "cbc_plaintext_256.txt";
	localparam ciphertext_fn = "cbc_ciphertext_256.txt";

	integer total_blocks;
	integer i, j;

	reg [`WORD_S-1:0]  cmd;
	reg [`KEY_S-1:0]   key;
	reg [`IV_BITS-1:0] iv;

	queue_wrapper#(`BLK_S) plaintext_queue;
	queue_wrapper#(`BLK_S) ciphertext_queue;

	cmd = {`WORD_S{1'b0}};

	ciphertext_queue = new();
	plaintext_queue = new();

	plaintext_queue.fill_from_file(plaintext_fn);
	ciphertext_queue.fill_from_file(ciphertext_fn);

	total_blocks = 1 + ($urandom() % plaintext_queue.size()) % (4*DATA_FIFO_SIZE);
	$display("%s: START", testcase_name);
	$display("%s: Sending %d AES blocks.", testcase_name, total_blocks);

	// Prepare encryption request
	cmd = set_decryption_op_bit(cmd) |
	      set_key_256_bit(cmd) |
	      set_CBC_mode_bit(cmd);
	key = AES_KEY256;
	iv = AES_IV;

	bus_sem.get(1);
	for (i = 0; i < total_blocks; i++)
		axis_slave_queue_add128(plaintext_queue.get(i), i == total_blocks - 1);

	aes_send_request(cmd, key, 256, iv, 1, ciphertext_queue, total_blocks);
	wait_for_transfer();
	bus_sem.put(1);
endtask

// ECB encryption stress test
task test_256bit_key_ecb_enc();
	localparam testcase_name = "ECB encryption stress test (256-bit key)";
	localparam AES_KEY256 = 'hc3d5b742b34e24f51cb67371bdb337e71243fd28c807ffd2c22a166d2126839b;

	localparam test_blocks_no = 32;

	localparam plaintext_fn = "ecb_plaintext_256.txt";
	localparam ciphertext_fn = "ecb_ciphertext_256.txt";

	integer total_blocks;
	integer i, j;

	reg [`WORD_S-1:0]  cmd;
	reg [`KEY_S-1:0]   key;
	reg [`IV_BITS-1:0] iv;

	queue_wrapper#(`BLK_S) plaintext_queue;
	queue_wrapper#(`BLK_S) ciphertext_queue;

	cmd = {`WORD_S{1'b0}};

	ciphertext_queue = new();
	plaintext_queue = new();

	plaintext_queue.fill_from_file(plaintext_fn);
	ciphertext_queue.fill_from_file(ciphertext_fn);

	total_blocks = 1 + ($urandom() % plaintext_queue.size()) % (4*DATA_FIFO_SIZE);
	$display("%s: START", testcase_name);
	$display("%s: Sending %d AES blocks.", testcase_name, total_blocks);

	// Prepare encryption request
	cmd = set_encryption_op_bit(cmd) |
	      set_key_256_bit(cmd) |
	      set_ECB_mode_bit(cmd);
	key = AES_KEY256;
	iv = {`IV_BITS{1'b0}};

	bus_sem.get(1);
	for (i = 0; i < total_blocks; i++)
		axis_slave_queue_add128(ciphertext_queue.get(i), i == total_blocks - 1);

	aes_send_request(cmd, key, 256, iv, 0, plaintext_queue, total_blocks);
	wait_for_transfer();
	bus_sem.put(1);
endtask

// ECB decryption stress test
task test_256bit_key_ecb_dec();
	localparam testcase_name = "ECB decryption stress test (256-bit key)";
	localparam AES_KEY256 = 'hc3d5b742b34e24f51cb67371bdb337e71243fd28c807ffd2c22a166d2126839b;

	localparam test_blocks_no = 32;

	localparam plaintext_fn = "ecb_plaintext_256.txt";
	localparam ciphertext_fn = "ecb_ciphertext_256.txt";

	integer total_blocks;
	integer i, j;

	reg [`WORD_S-1:0]  cmd;
	reg [`KEY_S-1:0]   key;
	reg [`IV_BITS-1:0] iv;

	queue_wrapper#(`BLK_S) plaintext_queue;
	queue_wrapper#(`BLK_S) ciphertext_queue;

	cmd = {`WORD_S{1'b0}};

	ciphertext_queue = new();
	plaintext_queue = new();

	plaintext_queue.fill_from_file(plaintext_fn);
	ciphertext_queue.fill_from_file(ciphertext_fn);

	total_blocks = 1 + ($urandom() % plaintext_queue.size()) % (4*DATA_FIFO_SIZE);
	$display("%s: START", testcase_name);
	$display("%s: Sending %d AES blocks.", testcase_name, total_blocks);

	// Prepare decryption request
	cmd = set_decryption_op_bit(cmd) |
	      set_key_256_bit(cmd) |
	      set_ECB_mode_bit(cmd);
	key = AES_KEY256;
	iv = {`IV_BITS{1'b0}};

	bus_sem.get(1);
	for (i = 0; i < total_blocks; i++)
		axis_slave_queue_add128(plaintext_queue.get(i), i == total_blocks - 1);

	aes_send_request(cmd, key, 256, iv, 0, ciphertext_queue, total_blocks);
	wait_for_transfer();
	bus_sem.put(1);
endtask
