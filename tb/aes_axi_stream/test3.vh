// Test 3
// Second independent encryption operation with the same key.
task testcase3();
        integer initial_cmp_cnt; // testcase comparison counter

        $display("Starting Testcase: Second independent encryption operation with the same key.");

        initial_cmp_cnt = comparison_cnt;
        aes_plaintext =  {
                8'h54, 8'h77, 8'h6F, 8'h20,
                8'h4F, 8'h6E, 8'h65, 8'h20,
                8'h4E, 8'h69, 8'h6E, 8'h65,
                8'h20, 8'h54, 8'h77, 8'h6F
        };
        aes_plaintext = swap_blk(aes_plaintext);

        tester #(32)::packed_to_unpacked(`ENCRYPT, data_tmp);
        tester::print_unpacked(data_tmp);
        gen_transaction(data_tmp);

        tester #($size(aes_plaintext))::packed_to_unpacked(aes_plaintext, data_tmp);
        tester::print_unpacked(data_tmp);
        gen_transaction(data_tmp, 1);

        wait(comparison_cnt == initial_cmp_cnt + 4);

        $display("Testcase 3 done with %d errors.\n", error_cnt);
        if (error_cnt != 0)
                $finish;

        // No cleanup
endtask
