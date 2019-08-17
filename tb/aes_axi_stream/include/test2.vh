// ECB Encryption/decryption stress test
task testcase2();
	localparam AES_KEY128 = `KEY_S'h5468617473206D79204B756E67204675;

        localparam AES_PLAINTEXT_1 = `BLK_S'h54776f204f6e65204e696e652054776f;
        localparam AES_CIPHERTEXT_1 = `BLK_S'h29c3505f571420f6402299b31a02d73a;

        localparam AES_PLAINTEXT_2 = `BLK_S'h12345678911123456789012345678901;
        localparam AES_CIPHERTEXT_2 = `BLK_S'h2914b1466013ba1e48d6d795e97d3e15;

        localparam blocks_no = 256;

        integer initial_cmp_cnt; // testcase comparison counter
        integer i, j;
        reg [0:`WORD_S-1] expected_results[$] = {};

        time encrypt_time;
        time decrypt_time;

        for (i = 0; i < blocks_no / 2; i=i+1) begin
                tester #(`BLK_S)::q_push_back32_rev(AES_CIPHERTEXT_1, expected_results);
                tester #(`BLK_S)::q_push_back32_rev(AES_CIPHERTEXT_2, expected_results);
        end
        
        for (i = 0; i < blocks_no / 2; i=i+1) begin
                tester #(`BLK_S)::q_push_back32_rev(AES_PLAINTEXT_1, expected_results);
                tester #(`BLK_S)::q_push_back32_rev(AES_PLAINTEXT_2, expected_results);
        end

        $display("Starting Testcase: Encryption decryption stress test");

        initial_cmp_cnt = comparison_cnt;

	// Prepare encryption request
	encrypt_time = $time;

        tester::packed_to_unpacked(`ECB_ENCRYPT_128, data_tmp);
        tester::print_unpacked(data_tmp);
        gen_transaction(data_tmp);

	// Send key alongside encryption payload
        aes128_in_blk = swap_blk(AES_KEY128);
        tester #($size(aes128_in_blk))::packed_to_unpacked(aes128_in_blk, data_tmp);
        tester::print_unpacked(data_tmp);
        gen_transaction(data_tmp, 0);

        // Encrypt
        for (i = 0; i < blocks_no / 2; i=i+1) begin
                $display("Sending encryption blocks %d and %d", i * 2 , i * 2 + 1);

                aes128_in_blk =  AES_PLAINTEXT_1;
                // The values need to be swapped to match the values put by the kernel on the AXI bus
                aes128_in_blk = swap_blk(aes128_in_blk);

                tester #($size(aes128_in_blk))::packed_to_unpacked(aes128_in_blk, data_tmp);
                tester::print_unpacked(data_tmp);
                gen_transaction(data_tmp);

                aes128_in_blk = AES_PLAINTEXT_2;
                aes128_in_blk = swap_blk(aes128_in_blk);

                tester #($size(aes128_in_blk))::packed_to_unpacked(aes128_in_blk, data_tmp);
                tester::print_unpacked(data_tmp);

                if (i == blocks_no / 2 - 1)
                        gen_transaction(data_tmp, 1);
                else
                        gen_transaction(data_tmp, 0);
        end

	wait(comparison_cnt == initial_cmp_cnt + blocks_no * 4);
	encrypt_time = $time - encrypt_time;

	// Prepare decryption request
	decrypt_time = $time;

        tester::packed_to_unpacked(`ECB_DECRYPT_128, data_tmp);
        tester::print_unpacked(data_tmp);
        gen_transaction(data_tmp);

	// Send key alongside decryption payload
        aes128_in_blk = swap_blk(AES_KEY128);
        tester #($size(aes128_in_blk))::packed_to_unpacked(aes128_in_blk, data_tmp);
        tester::print_unpacked(data_tmp);
        gen_transaction(data_tmp, 0);

        // Now decrypt
        for (i = 0; i < blocks_no / 2; i=i+1) begin
                $display("Sending decryption blocks %d and %d", i * 2 , i * 2 + 1);

                aes128_in_blk = AES_CIPHERTEXT_1;
                aes128_in_blk = swap_blk(aes128_in_blk);

                tester #($size(aes128_in_blk))::packed_to_unpacked(aes128_in_blk, data_tmp);
                tester::print_unpacked(data_tmp);
                gen_transaction(data_tmp);

                aes128_in_blk = AES_CIPHERTEXT_2;
                aes128_in_blk = swap_blk(aes128_in_blk);

                tester #($size(aes128_in_blk))::packed_to_unpacked(aes128_in_blk, data_tmp);
                tester::print_unpacked(data_tmp);

                if (i == blocks_no / 2 - 1)
                        gen_transaction(data_tmp, 1);
                else
                        gen_transaction(data_tmp, 0);
        end

        wait(comparison_cnt == initial_cmp_cnt + blocks_no * 2 * 4);

        for (i = initial_cmp_cnt, j=0; i < comparison_cnt; i=i+1, j=j+1) begin
                if (tester #(`WORD_S)::verify_output(results[i], expected_results[j], errors) == 0)
                        $display("Word no. %d from block no %d does not match!", j, j / 4);
        end

	decrypt_time = $time - decrypt_time;
	$display("Encrypting %4d blocks took %t", blocks_no, encrypt_time);
	$display("Decrypting %4d blocks took %t", blocks_no, decrypt_time);

        $display("Testcase 2 done with %d errors.\n", errors);
        if (errors != 0)
                $finish;

        // No cleanup
endtask
