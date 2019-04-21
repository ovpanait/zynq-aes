// Test 1
// Encrypt/Decrypt two blocks in one go
task testcase2();
        localparam AES_PLAINTEXT_1 = `BLK_S'h54776f204f6e65204e696e652054776f;
        localparam AES_CIPHERTEXT_1 = `BLK_S'h29c3505f571420f6402299b31a02d73a;

        localparam AES_PLAINTEXT_2 = `BLK_S'h12345678911123456789012345678901;
        localparam AES_CIPHERTEXT_2 = `BLK_S'h2914b1466013ba1e48d6d795e97d3e15;

        integer initial_cmp_cnt; // testcase comparison counter
        integer i, j;
        reg [0:`WORD_S-1] expected_results[$] = {};

        tester #(`BLK_S)::q_push_back32_rev(AES_CIPHERTEXT_1, expected_results);
        tester #(`BLK_S)::q_push_back32_rev(AES_CIPHERTEXT_2, expected_results);
        tester #(`BLK_S)::q_push_back32_rev(AES_PLAINTEXT_1, expected_results);
        tester #(`BLK_S)::q_push_back32_rev(AES_PLAINTEXT_2, expected_results);

        $display("Starting Testcase: Encrypt two blocks in one go.");

        initial_cmp_cnt = comparison_cnt;

        // Encrypt
        aes128_in_blk =  AES_PLAINTEXT_1;
        // The values need to be swapped to match the values put by the kernel on the AXI bus
        aes128_in_blk = swap_blk(aes128_in_blk);

        tester::packed_to_unpacked(`ENCRYPT, data_tmp);
        tester::print_unpacked(data_tmp);
        gen_transaction(data_tmp);

        tester #($size(aes128_in_blk))::packed_to_unpacked(aes128_in_blk, data_tmp);
        tester::print_unpacked(data_tmp);
        gen_transaction(data_tmp);

        aes128_in_blk = AES_PLAINTEXT_2;
        aes128_in_blk = swap_blk(aes128_in_blk);

        tester #($size(aes128_in_blk))::packed_to_unpacked(aes128_in_blk, data_tmp);
        tester::print_unpacked(data_tmp);
        gen_transaction(data_tmp, 1);

        // Now decrypt
        aes128_in_blk = AES_CIPHERTEXT_1;
        aes128_in_blk = swap_blk(aes128_in_blk);

        tester::packed_to_unpacked(`DECRYPT, data_tmp);
        tester::print_unpacked(data_tmp);
        gen_transaction(data_tmp);

        tester #($size(aes128_in_blk))::packed_to_unpacked(aes128_in_blk, data_tmp);
        tester::print_unpacked(data_tmp);
        gen_transaction(data_tmp);

        aes128_in_blk = AES_CIPHERTEXT_2;
        aes128_in_blk = swap_blk(aes128_in_blk);

        tester #($size(aes128_in_blk))::packed_to_unpacked(aes128_in_blk, data_tmp);
        tester::print_unpacked(data_tmp);
        gen_transaction(data_tmp, 1);

        wait(comparison_cnt == initial_cmp_cnt + 16);
        for (i = initial_cmp_cnt, j=0; i < comparison_cnt; i=i+1, j=j+1) begin
                tester::verify_output(results[i], expected_results[j]);
        end

        $display("Testcase 2 done with %d errors.\n", error_cnt);
        if (error_cnt != 0)
                $finish;

        // No cleanup
endtask
