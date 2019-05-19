// Test 3
// Second independent encryption operation with the same key.
task testcase3();
        localparam AES_PLAINTEXT_1 = `BLK_S'h54776f204f6e65204e696e652054776f;
        localparam AES_CIPHERTEXT_1 = `BLK_S'h29c3505f571420f6402299b31a02d73a;

        integer initial_cmp_cnt; // testcase comparison counter
        integer i, j;
        reg [0:`WORD_S-1] expected_results[$] = {};

        $display("Starting Testcase: Second independent encryption operation with the same key.");

        tester #(`BLK_S)::q_push_back32_rev(AES_CIPHERTEXT_1, expected_results);
        tester #(`BLK_S)::q_push_back32_rev(AES_PLAINTEXT_1, expected_results);
        initial_cmp_cnt = comparison_cnt;

        // Encrypt
        aes128_in_blk =  AES_PLAINTEXT_1;
        aes128_in_blk = swap_blk(aes128_in_blk);

        tester::packed_to_unpacked(`ECB_ENCRYPT_128, data_tmp);
        tester::print_unpacked(data_tmp);
        gen_transaction(data_tmp);

        tester #($size(aes128_in_blk))::packed_to_unpacked(aes128_in_blk, data_tmp);
        tester::print_unpacked(data_tmp);
        gen_transaction(data_tmp, 1);

        // Decrypt
        aes128_in_blk =  AES_CIPHERTEXT_1;
        aes128_in_blk = swap_blk(aes128_in_blk);

        tester::packed_to_unpacked(`ECB_DECRYPT_128, data_tmp);
        tester::print_unpacked(data_tmp);
        gen_transaction(data_tmp);

        tester #($size(aes128_in_blk))::packed_to_unpacked(aes128_in_blk, data_tmp);
        tester::print_unpacked(data_tmp);
        gen_transaction(data_tmp, 1);

        wait(comparison_cnt == initial_cmp_cnt + 8);

        for (i = initial_cmp_cnt, j=0; i < comparison_cnt; i=i+1, j=j+1) begin
                tester::verify_output(results[i], expected_results[j], errors);
        end

        $display("Testcase 3 done with %d errors.\n", errors);
        if (errors != 0)
                $finish;

        // No cleanup
endtask
