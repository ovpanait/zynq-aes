// CBC Encryption/decryption stress test
task testcase4();
	localparam AES_KEY_128 = `BLK_S'h5468617473206D79204B756E67204675;
	localparam AES_KEY_128_RES = `BLK_S'h00000000000000000000000000000000;

	localparam AES_IV_1 = `BLK_S'h54776F204F6E65204E696E652054776F;

        localparam AES_PLAINTEXT_1 = `BLK_S'h53696e676c6520626c6f636b206d7367;
        localparam AES_CIPHERTEXT_1 = `BLK_S'h55731240428dc8b9adfc2ce5502d11ff;

        localparam AES_PLAINTEXT_2 = `BLK_S'h12345678911123456789012345678901;
        localparam AES_CIPHERTEXT_2 = `BLK_S'h5af05d31aadbc4c9cfa81faa6d7e3538;

        localparam blocks_no = 2;

        integer initial_cmp_cnt; // testcase comparison counter
        integer i, j;
        reg [0:`WORD_S-1] expected_results[$] = {};

	tester #(`BLK_S)::q_push_back32_rev(AES_KEY_128_RES, expected_results);

        for (i = 0; i < blocks_no / 2; i=i+1) begin
                tester #(`BLK_S)::q_push_back32_rev(AES_CIPHERTEXT_1, expected_results);
                tester #(`BLK_S)::q_push_back32_rev(AES_CIPHERTEXT_2, expected_results);
        end
        
        for (i = 0; i < blocks_no / 2; i=i+1) begin
                tester #(`BLK_S)::q_push_back32_rev(AES_PLAINTEXT_1, expected_results);
                tester #(`BLK_S)::q_push_back32_rev(AES_PLAINTEXT_2, expected_results);
        end

        $display("Starting Testcase: CBC Encryption decryption stress test");

        initial_cmp_cnt = comparison_cnt;

        tester #(32)::packed_to_unpacked(`SET_KEY_128, data_tmp);
        tester::print_unpacked(data_tmp);
        gen_transaction(data_tmp, 0);

	aes128_in_blk = swap_blk(AES_KEY_128);
        tester #($size(aes128_in_blk))::packed_to_unpacked(aes128_in_blk, data_tmp);
        tester::print_unpacked(data_tmp);
        gen_transaction(data_tmp, 1);

        tester::packed_to_unpacked(`CBC_ENCRYPT_128, data_tmp);
        tester::print_unpacked(data_tmp);
        gen_transaction(data_tmp, 0);

	aes128_in_blk = swap_blk(AES_IV_1);
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
                gen_transaction(data_tmp, 0);

                aes128_in_blk = AES_PLAINTEXT_2;
                aes128_in_blk = swap_blk(aes128_in_blk);

                tester #($size(aes128_in_blk))::packed_to_unpacked(aes128_in_blk, data_tmp);
                tester::print_unpacked(data_tmp);

                if (i == blocks_no / 2 - 1)
                        gen_transaction(data_tmp, 1);
                else
                        gen_transaction(data_tmp, 0);
        end

        tester::packed_to_unpacked(`CBC_DECRYPT_128, data_tmp);
        tester::print_unpacked(data_tmp);
        gen_transaction(data_tmp, 0);

	aes128_in_blk = swap_blk(AES_IV_1);
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
                gen_transaction(data_tmp, 0);

                aes128_in_blk = AES_CIPHERTEXT_2;
                aes128_in_blk = swap_blk(aes128_in_blk);

                tester #($size(aes128_in_blk))::packed_to_unpacked(aes128_in_blk, data_tmp);
                tester::print_unpacked(data_tmp);

                if (i == blocks_no / 2 - 1)
                        gen_transaction(data_tmp, 1);
                else
                        gen_transaction(data_tmp, 0);
        end

        wait(comparison_cnt == initial_cmp_cnt + 4 + blocks_no * 2 * 4);
        for (i = initial_cmp_cnt, j=0; i < comparison_cnt; i=i+1, j=j+1) begin
                tester::verify_output(results[i], expected_results[j], errors);
        end

        $display("Testcase 4 done with %d errors.\n", errors);
        if (errors != 0)
                $finish;

        // No cleanup
endtask
