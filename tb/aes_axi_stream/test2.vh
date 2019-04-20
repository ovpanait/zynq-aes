// Test 1
// Encrypt two blocks in one go
task testcase2();
        integer initial_cmp_cnt; // testcase comparison counter

        $display("Starting Testcase: Encrypt two blocks in one go.");

        initial_cmp_cnt = comparison_cnt;
        aes_plaintext =  {
                8'h54, 8'h77, 8'h6F, 8'h20,
                8'h4F, 8'h6E, 8'h65, 8'h20,
                8'h4E, 8'h69, 8'h6E, 8'h65,
                8'h20, 8'h54, 8'h77, 8'h6F
        };

        // The values need to be swapped to match the values put by the kernel on the AXI bus
        aes_plaintext = swap_blk(aes_plaintext);

        tester #(32)::packed_to_unpacked(`ENCRYPT, data_tmp);
        tester::print_unpacked(data_tmp);
        gen_transaction(data_tmp);

        tester #($size(aes_plaintext))::packed_to_unpacked(aes_plaintext, data_tmp);
        tester::print_unpacked(data_tmp);
        gen_transaction(data_tmp);

        aes_plaintext = {
                8'h12, 8'h34, 8'h56, 8'h78,
                8'h91, 8'h11, 8'h23, 8'h45,
                8'h67, 8'h89, 8'h01, 8'h23,
                8'h45, 8'h67, 8'h89, 8'h01
        };
        aes_plaintext = swap_blk(aes_plaintext);

        tester #($size(aes_plaintext))::packed_to_unpacked(aes_plaintext, data_tmp);
        tester::print_unpacked(data_tmp);
        gen_transaction(data_tmp, 1);

        wait(comparison_cnt == initial_cmp_cnt + 8);

        $display("Testcase 2 done with %d errors.\n", error_cnt);
        if (error_cnt != 0)
                $finish;

        // No cleanup
endtask
