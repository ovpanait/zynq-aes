// CBC Encryption/decryption stress test
task testcase4();
	localparam AES_KEY128 = `KEY_S'h5468617473206D79204B756E67204675;

	localparam AES_IV_1 = `BLK_S'h54776F204F6E65204E696E652054776F;

        localparam AES_PLAINTEXT_1 = `BLK_S'h53696e676c6520626c6f636b206d7367;
        localparam AES_CIPHERTEXT_1 = `BLK_S'h55731240428dc8b9adfc2ce5502d11ff;

        localparam AES_PLAINTEXT_2 = `BLK_S'h12345678911123456789012345678901;
        localparam AES_CIPHERTEXT_2 = `BLK_S'h5af05d31aadbc4c9cfa81faa6d7e3538;

        localparam blocks_no = 8;

        integer initial_cmp_cnt; // testcase comparison counter
        integer i, j;
        reg [0:`WORD_S-1] expected_results[$];
        expected_results = {
        32'h55731240, 32'h428dc8b9, 32'hadfc2ce5, 32'h502d11ff,
        32'h5af05d31, 32'haadbc4c9, 32'hcfa81faa, 32'h6d7e3538,
        32'h56d862a8, 32'h2e03c897, 32'he9ec2f98, 32'h2f3711e9,
        32'h14641df1, 32'hd0d1026d, 32'h2544d37b, 32'h62179cf7,
        32'h86032f7c, 32'h21b9b7dc, 32'h1b859300, 32'h20def7cf,
        32'h83212182, 32'h25f2c763, 32'h6ecbbcae, 32'h03e9e47b,
        32'h14ad46f7, 32'h8e22d446, 32'h1343fb44, 32'h52abd6b4,
        32'hc9f5b658, 32'ha0be6a4a, 32'hd48a94a2, 32'h8e7872d3
        };

        for (i = 0; i < blocks_no / 2; i=i+1) begin
                tester #(`BLK_S)::q_push_back32_rev(AES_PLAINTEXT_1, expected_results);
                tester #(`BLK_S)::q_push_back32_rev(AES_PLAINTEXT_2, expected_results);
        end

        $display("Starting Testcase: CBC Encryption decryption stress test");

        initial_cmp_cnt = comparison_cnt;

	// Encryption requets
        tester::packed_to_unpacked(`CBC_ENCRYPT_128, data_tmp);
        tester::print_unpacked(data_tmp);
        gen_transaction(data_tmp, 0);

	// Send key alongside encryption payload
        aes128_in_blk = swap_blk(AES_KEY128);
        tester #($size(aes128_in_blk))::packed_to_unpacked(aes128_in_blk, data_tmp);
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

	// Send key alongside decryption payload
        aes128_in_blk = swap_blk(AES_KEY128);
        tester #($size(aes128_in_blk))::packed_to_unpacked(aes128_in_blk, data_tmp);
        tester::print_unpacked(data_tmp);
        gen_transaction(data_tmp, 0);

	aes128_in_blk = swap_blk(AES_IV_1);
        tester #($size(aes128_in_blk))::packed_to_unpacked(aes128_in_blk, data_tmp);
        tester::print_unpacked(data_tmp);
        gen_transaction(data_tmp, 0);

        // Now decrypt
        for (i = 0; i < blocks_no / 2; i=i+1) begin
                $display("Sending decryption blocks %d and %d", i * 2 , i * 2 + 1);

                aes128_in_blk = {expected_results[i*8], expected_results[i*8+1], expected_results[i*8+2], expected_results[i*8+3]};
                aes128_in_blk = swap_blk(aes128_in_blk);

                tester #($size(aes128_in_blk))::packed_to_unpacked(aes128_in_blk, data_tmp);
                tester::print_unpacked(data_tmp);
                gen_transaction(data_tmp, 0);

                aes128_in_blk = {expected_results[i*8+4], expected_results[i*8+5], expected_results[i*8+6], expected_results[i*8+7]};
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
                if (tester::verify_output(results[i], expected_results[j], errors) == 0)
                        $display("Word no. %d from block no %d does not match!", j, j / 4);
        end

        $display("Testcase 4 done with %d errors.\n", errors);
        if (errors != 0)
                $finish;

        // No cleanup
endtask
