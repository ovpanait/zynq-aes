task test_128bit_key();
	test_128bit_key_ofb();
	test_128bit_key_cfb();
	test_128bit_key_pcbc();
	test_128bit_key_ctr();
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

task test_128bit_key_ctr();
	test_128bit_key_ctr_enc();
	test_128bit_key_ctr_dec();
endtask

task test_128bit_key_pcbc();
	test_128bit_key_pcbc_enc();
	test_128bit_key_pcbc_dec();
endtask

task test_128bit_key_cfb();
	test_128bit_key_cfb_enc();
	test_128bit_key_cfb_dec();
endtask

task test_128bit_key_ofb();
	test_128bit_key_ofb_enc();
	test_128bit_key_ofb_dec();
endtask

// OFB encryption stress test
task test_128bit_key_ofb_enc();
	localparam testcase_name = "OFB encryption stress test (128-bit key)";
	localparam AES_KEY128 = 'h7af17b56fb4e12150938a6b947d0a639;
	localparam AES_IV = 'h8c5e2e2dfa06af266c9af15f7c07df01;

	localparam plaintext_fn = "ofb_plaintext_128.txt";
	localparam ciphertext_fn = "ofb_ciphertext_128.txt";

	integer total_blocks;
	integer i, j;

	reg [`WORD_S-1:0]          cmd;
	reg [`AES128_KEY_BITS-1:0] key;
	reg [`IV_BITS-1:0]         iv;

	queue#(`BLK_S) plaintext_queue;
	queue#(`BLK_S) ciphertext_queue;

	cmd = {`WORD_S{1'b0}};

	ciphertext_queue = new();
	plaintext_queue = new();

	plaintext_queue.fill_from_file(plaintext_fn);
	ciphertext_queue.fill_from_file(ciphertext_fn);

	total_blocks = 1 + 1 + ($urandom() % plaintext_queue.size()) % DATA_FIFO_SIZE;

	$display("%s: START", testcase_name);
	$display("%s: Sending %d AES blocks.", testcase_name, total_blocks);

	// Prepare encryption request
	cmd = set_encryption_op_bit(cmd) |
	      set_key_128_bit(cmd) |
	      set_OFB_mode_bit(cmd);
	key = AES_KEY128;
	iv = AES_IV;

	bus_sem.get(1);
	for (i = 0; i < total_blocks; i++)
		axis_slave_queue_add128(ciphertext_queue.get(i), i == total_blocks - 1);

	aes_send_request(cmd, key, 128, iv, 1, plaintext_queue, total_blocks);
	wait_for_transfer();
	bus_sem.put(1);
endtask

// OFB decryption stress test
task test_128bit_key_ofb_dec();
	localparam testcase_name = "OFB decryption stress test (128-bit key)";
	localparam AES_KEY128 = 'h7af17b56fb4e12150938a6b947d0a639;
	localparam AES_IV = 'h8c5e2e2dfa06af266c9af15f7c07df01;

	localparam plaintext_fn = "ofb_plaintext_128.txt";
	localparam ciphertext_fn = "ofb_ciphertext_128.txt";

	integer total_blocks;
	integer i, j;

	reg [`WORD_S-1:0]  cmd;
	reg [`KEY_S-1:0]   key;
	reg [`IV_BITS-1:0] iv;

	queue#(`BLK_S) plaintext_queue;
	queue#(`BLK_S) ciphertext_queue;

	cmd = {`WORD_S{1'b0}};

	ciphertext_queue = new();
	plaintext_queue = new();

	plaintext_queue.fill_from_file(plaintext_fn);
	ciphertext_queue.fill_from_file(ciphertext_fn);

	total_blocks = 1 + ($urandom() % plaintext_queue.size()) % DATA_FIFO_SIZE;

	$display("%s: START", testcase_name);
	$display("%s: Sending %d AES blocks.", testcase_name, total_blocks);

	// Prepare decryption request
	cmd = set_decryption_op_bit(cmd) |
	      set_key_128_bit(cmd) |
	      set_OFB_mode_bit(cmd);
	key = AES_KEY128;
	iv = AES_IV;

	bus_sem.get(1);
	for (i = 0; i < total_blocks; i++)
		axis_slave_queue_add128(plaintext_queue.get(i), i == total_blocks - 1);

	aes_send_request(cmd, key, 128, iv, 1, ciphertext_queue, total_blocks);
	wait_for_transfer();
	bus_sem.put(1);
endtask

// CFB encryption stress test
task test_128bit_key_cfb_enc();
	localparam testcase_name = "CFB encryption stress test (128-bit key)";
	localparam AES_KEY128 = 'h7781fa496fad370f8aa2b695c4d0fe06;
	localparam AES_IV = 'h3dd37da6407c03ef8fb0e100527fcc3f;

	localparam plaintext_fn = "cfb_plaintext_128.txt";
	localparam ciphertext_fn = "cfb_ciphertext_128.txt";

	integer total_blocks;
	integer i, j;

	reg [`WORD_S-1:0]          cmd;
	reg [`AES128_KEY_BITS-1:0] key;
	reg [`IV_BITS-1:0]         iv;

	queue#(`BLK_S) plaintext_queue;
	queue#(`BLK_S) ciphertext_queue;

	cmd = {`WORD_S{1'b0}};

	ciphertext_queue = new();
	plaintext_queue = new();

	plaintext_queue.fill_from_file(plaintext_fn);
	ciphertext_queue.fill_from_file(ciphertext_fn);

	total_blocks = 1 + ($urandom() % plaintext_queue.size()) % DATA_FIFO_SIZE;
	$display("%s: START", testcase_name);
	$display("%s: Sending %d AES blocks.", testcase_name, total_blocks);

	// Prepare encryption request
	cmd = set_encryption_op_bit(cmd) |
	      set_key_128_bit(cmd) |
	      set_CFB_mode_bit(cmd);
	key = AES_KEY128;
	iv = AES_IV;

	bus_sem.get(1);
	for (i = 0; i < total_blocks; i++)
		axis_slave_queue_add128(ciphertext_queue.get(i), i == total_blocks - 1);

	aes_send_request(cmd, key, 128, iv, 1, plaintext_queue, total_blocks);
	wait_for_transfer();
	bus_sem.put(1);
endtask

// CFB decryption stress test
task test_128bit_key_cfb_dec();
	localparam testcase_name = "CFB decryption stress test (128-bit key)";
	localparam AES_KEY128 = 'h7781fa496fad370f8aa2b695c4d0fe06;
	localparam AES_IV = 'h3dd37da6407c03ef8fb0e100527fcc3f;

	localparam plaintext_fn = "cfb_plaintext_128.txt";
	localparam ciphertext_fn = "cfb_ciphertext_128.txt";

	integer total_blocks;
	integer i, j;

	reg [`WORD_S-1:0]  cmd;
	reg [`KEY_S-1:0]   key;
	reg [`IV_BITS-1:0] iv;

	queue#(`BLK_S) plaintext_queue;
	queue#(`BLK_S) ciphertext_queue;

	cmd = {`WORD_S{1'b0}};

	ciphertext_queue = new();
	plaintext_queue = new();

	plaintext_queue.fill_from_file(plaintext_fn);
	ciphertext_queue.fill_from_file(ciphertext_fn);

	total_blocks = 1 + ($urandom() % plaintext_queue.size()) % DATA_FIFO_SIZE;
	$display("%s: START", testcase_name);
	$display("%s: Sending %d AES blocks.", testcase_name, total_blocks);

	// Prepare decryption request
	cmd = set_decryption_op_bit(cmd) |
	      set_key_128_bit(cmd) |
	      set_CFB_mode_bit(cmd);
	key = AES_KEY128;
	iv = AES_IV;

	bus_sem.get(1);
	for (i = 0; i < total_blocks; i++)
		axis_slave_queue_add128(plaintext_queue.get(i), i == total_blocks - 1);

	aes_send_request(cmd, key, 128, iv, 1, ciphertext_queue, total_blocks);
	wait_for_transfer();
	bus_sem.put(1);
endtask


// PCBC encryption stress test
task test_128bit_key_pcbc_enc();
	localparam testcase_name = "PCBC encryption stress test (128-bit key)";
	localparam AES_KEY128 = 'hdfeec7fa89e979a9eb3d4d3257e37eb4;
	localparam AES_IV = 'h852b3137f4cae47d797d51df6f4e87ab;

	localparam plaintext_fn = "pcbc_plaintext_128.txt";
	localparam ciphertext_fn = "pcbc_ciphertext_128.txt";

	integer total_blocks;
	integer i, j;

	reg [`WORD_S-1:0]          cmd;
	reg [`AES128_KEY_BITS-1:0] key;
	reg [`IV_BITS-1:0]         iv;

	queue#(`BLK_S) plaintext_queue;
	queue#(`BLK_S) ciphertext_queue;

	cmd = {`WORD_S{1'b0}};

	ciphertext_queue = new();
	plaintext_queue = new();

	plaintext_queue.fill_from_file(plaintext_fn);
	ciphertext_queue.fill_from_file(ciphertext_fn);

	total_blocks = 1 + ($urandom() % plaintext_queue.size()) % DATA_FIFO_SIZE;
	$display("%s: START", testcase_name);
	$display("%s: Sending %d AES blocks.", testcase_name, total_blocks);

	// Prepare encryption request
	cmd = set_encryption_op_bit(cmd) |
	      set_key_128_bit(cmd) |
	      set_PCBC_mode_bit(cmd);
	key = AES_KEY128;
	iv = AES_IV;

	bus_sem.get(1);
	for (i = 0; i < total_blocks; i++)
		axis_slave_queue_add128(ciphertext_queue.get(i), i == total_blocks - 1);

	aes_send_request(cmd, key, 128, iv, 1, plaintext_queue, total_blocks);
	wait_for_transfer();
	bus_sem.put(1);
endtask

// PCBC decryption stress test
task test_128bit_key_pcbc_dec();
	localparam testcase_name = "PCBC decryption stress test (128-bit key)";
	localparam AES_KEY128 = 'hdfeec7fa89e979a9eb3d4d3257e37eb4;
	localparam AES_IV = 'h852b3137f4cae47d797d51df6f4e87ab;

	localparam plaintext_fn = "pcbc_plaintext_128.txt";
	localparam ciphertext_fn = "pcbc_ciphertext_128.txt";

	integer total_blocks;
	integer i, j;

	reg [`WORD_S-1:0]  cmd;
	reg [`KEY_S-1:0]   key;
	reg [`IV_BITS-1:0] iv;

	queue#(`BLK_S) plaintext_queue;
	queue#(`BLK_S) ciphertext_queue;

	cmd = {`WORD_S{1'b0}};

	ciphertext_queue = new();
	plaintext_queue = new();

	plaintext_queue.fill_from_file(plaintext_fn);
	ciphertext_queue.fill_from_file(ciphertext_fn);

	total_blocks = 1 + ($urandom() % plaintext_queue.size()) % DATA_FIFO_SIZE;
	$display("%s: START", testcase_name);
	$display("%s: Sending %d AES blocks.", testcase_name, total_blocks);

	// Prepare decryption request
	cmd = set_key_128_bit(cmd) |
	      set_decryption_op_bit(cmd) |
	      set_PCBC_mode_bit(cmd);
	key = AES_KEY128;
	iv = AES_IV;

	bus_sem.get(1);
	for (i = 0; i < total_blocks; i++)
		axis_slave_queue_add128(plaintext_queue.get(i), i == total_blocks - 1);

	aes_send_request(cmd, key, 128, iv, 1, ciphertext_queue, total_blocks);
	wait_for_transfer();
	bus_sem.put(1);
endtask

// CTR encryption stress test
task test_128bit_key_ctr_enc();
	localparam testcase_name = "CTR encryption stress test (128-bit key)";
	localparam AES_KEY128 = 'hd103aa2aa292b696d7f58fb4c18368fa;
	localparam AES_IV = 'h402426994c5d2dc8f8da82a0bb5ca718;

	localparam plaintext_fn = "ctr_plaintext_128.txt";
	localparam ciphertext_fn = "ctr_ciphertext_128.txt";

	integer total_blocks;
	integer i, j;

	reg [`WORD_S-1:0]          cmd;
	reg [`AES128_KEY_BITS-1:0] key;
	reg [`IV_BITS-1:0]         iv;

	queue#(`BLK_S) plaintext_queue;
	queue#(`BLK_S) ciphertext_queue;

	cmd = {`WORD_S{1'b0}};

	ciphertext_queue = new();
	plaintext_queue = new();

	plaintext_queue.fill_from_file(plaintext_fn);
	ciphertext_queue.fill_from_file(ciphertext_fn);

	total_blocks = 1 + ($urandom() % plaintext_queue.size()) % DATA_FIFO_SIZE;
	$display("%s: START", testcase_name);
	$display("%s: Sending %d AES blocks.", testcase_name, total_blocks);

	// Prepare encryption request
	cmd = set_encryption_op_bit(cmd) |
	      set_key_128_bit(cmd) |
	      set_CTR_mode_bit(cmd);
	key = AES_KEY128;
	iv = AES_IV;

	bus_sem.get(1);
	for (i = 0; i < total_blocks; i++)
		axis_slave_queue_add128(ciphertext_queue.get(i), i == total_blocks - 1);

	aes_send_request(cmd, key, 128, iv, 1, plaintext_queue, total_blocks);
	wait_for_transfer();
	bus_sem.put(1);
endtask

// CTR decryption stress test
task test_128bit_key_ctr_dec();
	localparam testcase_name = "CTR decryption stress test (128-bit key)";
	localparam AES_KEY128 = 'hd103aa2aa292b696d7f58fb4c18368fa;
	localparam AES_IV = 'h402426994c5d2dc8f8da82a0bb5ca718;

	localparam plaintext_fn = "ctr_plaintext_128.txt";
	localparam ciphertext_fn = "ctr_ciphertext_128.txt";

	integer total_blocks;
	integer i, j;

	reg [`WORD_S-1:0]  cmd;
	reg [`KEY_S-1:0]   key;
	reg [`IV_BITS-1:0] iv;

	queue#(`BLK_S) plaintext_queue;
	queue#(`BLK_S) ciphertext_queue;

	cmd = {`WORD_S{1'b0}};

	ciphertext_queue = new();
	plaintext_queue = new();

	plaintext_queue.fill_from_file(plaintext_fn);
	ciphertext_queue.fill_from_file(ciphertext_fn);

	total_blocks = 1 + ($urandom() % plaintext_queue.size()) % DATA_FIFO_SIZE;
	$display("%s: START", testcase_name);
	$display("%s: Sending %d AES blocks.", testcase_name, total_blocks);

	// Prepare encryption request
	cmd = set_decryption_op_bit(cmd) |
	      set_key_128_bit(cmd) |
	      set_CTR_mode_bit(cmd);
	key = AES_KEY128;
	iv = AES_IV;

	bus_sem.get(1);
	for (i = 0; i < total_blocks; i++)
		axis_slave_queue_add128(plaintext_queue.get(i), i == total_blocks - 1);

	aes_send_request(cmd, key, 128, iv, 1, ciphertext_queue, total_blocks);
	wait_for_transfer();
	bus_sem.put(1);
endtask

// CBC encryption stress test
task test_128bit_key_cbc_enc();
	localparam testcase_name = "CBC encryption stress test (128-bit key)";
	localparam AES_KEY128 = 'h5468617473206D79204B756E67204675;
	localparam AES_IV = 'h54776F204F6E65204E696E652054776F;

	localparam plaintext_fn = "cbc_plaintext_128.txt";
	localparam ciphertext_fn = "cbc_ciphertext_128.txt";

	integer total_blocks;
	integer i, j;

	reg [`WORD_S-1:0]          cmd;
	reg [`AES128_KEY_BITS-1:0] key;
	reg [`IV_BITS-1:0]         iv;

	queue#(`BLK_S) plaintext_queue;
	queue#(`BLK_S) ciphertext_queue;

	cmd = {`WORD_S{1'b0}};

	ciphertext_queue = new();
	plaintext_queue = new();

	plaintext_queue.fill_from_file(plaintext_fn);
	ciphertext_queue.fill_from_file(ciphertext_fn);

	total_blocks = 1 + ($urandom() % plaintext_queue.size()) % DATA_FIFO_SIZE;
	$display("%s: START", testcase_name);
	$display("%s: Sending %d AES blocks.", testcase_name, total_blocks);

	// Prepare encryption request
	cmd = set_encryption_op_bit(cmd) |
	      set_key_128_bit(cmd) |
	      set_CBC_mode_bit(cmd);
	key = AES_KEY128;
	iv = AES_IV;

	bus_sem.get(1);
	for (i = 0; i < total_blocks; i++)
		axis_slave_queue_add128(ciphertext_queue.get(i), i == total_blocks - 1);

	aes_send_request(cmd, key, 128, iv, 1, plaintext_queue, total_blocks);
	wait_for_transfer();
	bus_sem.put(1);
endtask

// CBC decryption stress test
task test_128bit_key_cbc_dec();
	localparam testcase_name = "CBC decryption stress test (128-bit key)";
	localparam AES_KEY128 = 'h5468617473206D79204B756E67204675;
	localparam AES_IV = 'h54776F204F6E65204E696E652054776F;

	localparam plaintext_fn = "cbc_plaintext_128.txt";
	localparam ciphertext_fn = "cbc_ciphertext_128.txt";

	integer total_blocks;
	integer i, j;

	reg [`WORD_S-1:0]  cmd;
	reg [`KEY_S-1:0]   key;
	reg [`IV_BITS-1:0] iv;

	queue#(`BLK_S) plaintext_queue;
	queue#(`BLK_S) ciphertext_queue;

	cmd = {`WORD_S{1'b0}};

	ciphertext_queue = new();
	plaintext_queue = new();


	plaintext_queue.fill_from_file(plaintext_fn);
	ciphertext_queue.fill_from_file(ciphertext_fn);

	total_blocks = 1 + ($urandom() % plaintext_queue.size()) % DATA_FIFO_SIZE;
	$display("%s: START", testcase_name);
	$display("%s: Sending %d AES blocks.", testcase_name, total_blocks);

	// Prepare encryption request
	cmd = set_decryption_op_bit(cmd) |
	      set_key_128_bit(cmd) |
	      set_CBC_mode_bit(cmd);
	key = AES_KEY128;
	iv = AES_IV;

	bus_sem.get(1);
	for (i = 0; i < total_blocks; i++)
		axis_slave_queue_add128(plaintext_queue.get(i), i == total_blocks - 1);

	aes_send_request(cmd, key, 128, iv, 1, ciphertext_queue, total_blocks);
	wait_for_transfer();
	bus_sem.put(1);
endtask


// ECB encryption stress test
task test_128bit_key_ecb_enc();
	localparam testcase_name = "ECB encryption stress test (128-bit key)";
	localparam AES_KEY128 = 'h5468617473206D79204B756E67204675;

	localparam plaintext_fn = "ecb_plaintext_128.txt";
	localparam ciphertext_fn = "ecb_ciphertext_128.txt";

	integer total_blocks;
	integer i, j;

	reg [`WORD_S-1:0]  cmd;
	reg [`KEY_S-1:0]   key;
	reg [`IV_BITS-1:0] iv;

	queue#(`BLK_S) plaintext_queue;
	queue#(`BLK_S) ciphertext_queue;

	cmd = {`WORD_S{1'b0}};

	ciphertext_queue = new();
	plaintext_queue = new();

	plaintext_queue.fill_from_file(plaintext_fn);
	ciphertext_queue.fill_from_file(ciphertext_fn);

	total_blocks = 1 + ($urandom() % plaintext_queue.size()) % DATA_FIFO_SIZE;
	$display("%s: START", testcase_name);
	$display("%s: Sending %d AES blocks.", testcase_name, total_blocks);

	// Prepare encryption request
	cmd = set_encryption_op_bit(cmd) |
	      set_key_128_bit(cmd) |
	      set_ECB_mode_bit(cmd);
	key = AES_KEY128;
	iv = {`IV_BITS{1'b0}};

	bus_sem.get(1);
	for (i = 0; i < total_blocks; i++)
		axis_slave_queue_add128(ciphertext_queue.get(i), i == total_blocks - 1);

	aes_send_request(cmd, key, 128, iv, 0, plaintext_queue, total_blocks);
	wait_for_transfer();
	bus_sem.put(1);
endtask

// ECB decryption stress test
task test_128bit_key_ecb_dec();
	localparam testcase_name = "ECB decryption stress test (128-bit key)";
	localparam AES_KEY128 = 'h5468617473206D79204B756E67204675;

	localparam plaintext_fn = "ecb_plaintext_128.txt";
	localparam ciphertext_fn = "ecb_ciphertext_128.txt";

	integer total_blocks;
	integer i, j;

	reg [`WORD_S-1:0]  cmd;
	reg [`KEY_S-1:0]   key;
	reg [`IV_BITS-1:0] iv;

	queue#(`BLK_S) plaintext_queue;
	queue#(`BLK_S) ciphertext_queue;

	cmd = {`WORD_S{1'b0}};

	ciphertext_queue = new();
	plaintext_queue = new();

	plaintext_queue.fill_from_file(plaintext_fn);
	ciphertext_queue.fill_from_file(ciphertext_fn);

	total_blocks = 1 + ($urandom() % plaintext_queue.size()) % DATA_FIFO_SIZE;
	$display("%s: START", testcase_name);
	$display("%s: Sending %d AES blocks.", testcase_name, total_blocks);

	// Prepare decryption request
	cmd = set_decryption_op_bit(cmd) |
	      set_key_128_bit(cmd) |
	      set_ECB_mode_bit(cmd);
	key = AES_KEY128;
	iv = {`IV_BITS{1'b0}};

	bus_sem.get(1);
	for (i = 0; i < total_blocks; i++)
		axis_slave_queue_add128(plaintext_queue.get(i), i == total_blocks - 1);

	aes_send_request(cmd, key, 128, iv, 0, ciphertext_queue, total_blocks);
	wait_for_transfer();
	bus_sem.put(1);
endtask
