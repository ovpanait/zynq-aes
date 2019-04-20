// Test 1
// Test Key Expansion
task testcase1();
        integer initial_cmp_cnt; // testcase comparison counter

        $display("Starting Testcase: Key expansion");

        initial_cmp_cnt = comparison_cnt;

        aes_key =  {
                8'h54, 8'h68, 8'h61, 8'h74,
                8'h73, 8'h20, 8'h6D, 8'h79,
                8'h20, 8'h4B, 8'h75, 8'h6E,
                8'h67, 8'h20, 8'h46, 8'h75
        };

        aes_key = swap_blk(aes_key);

        // Key expansion
        tester #(32)::packed_to_unpacked(`SET_KEY, data_tmp);
        tester::print_unpacked(data_tmp);
        gen_transaction(data_tmp);

        tester #($size(aes_key))::packed_to_unpacked(aes_key, data_tmp);
        tester::print_unpacked(data_tmp);
        gen_transaction(data_tmp, 1);

        wait(comparison_cnt == initial_cmp_cnt + 4);

        $display("Testcase 1 done with %d errors.\n", error_cnt);
        if (error_cnt != 0)
                $finish;

        // No cleanup
endtask
