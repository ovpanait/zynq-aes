// Test 3
// Second independent encryption operation with the same key.
task testcase3();
        integer initial_cmp_cnt; // testcase comparison counter
        integer i, j;
        reg [0:`WORD_S-1] expected_results[$] = {
                // Test 3
                32'h29c3505f,
                32'h571420f6,
                32'h402299b3,
                32'h1a02d73a
        };

        $display("Starting Testcase: Second independent encryption operation with the same key.");

        initial_cmp_cnt = comparison_cnt;
        aes128_in_blk =  {
                8'h54, 8'h77, 8'h6F, 8'h20,
                8'h4F, 8'h6E, 8'h65, 8'h20,
                8'h4E, 8'h69, 8'h6E, 8'h65,
                8'h20, 8'h54, 8'h77, 8'h6F
        };
        aes128_in_blk = swap_blk(aes128_in_blk);

        tester #(32)::packed_to_unpacked(`ENCRYPT, data_tmp);
        tester::print_unpacked(data_tmp);
        gen_transaction(data_tmp);

        tester #($size(aes128_in_blk))::packed_to_unpacked(aes128_in_blk, data_tmp);
        tester::print_unpacked(data_tmp);
        gen_transaction(data_tmp, 1);

        wait(comparison_cnt == initial_cmp_cnt + 4);

        for (i = initial_cmp_cnt, j=0; i < comparison_cnt; i=i+1, j=j+1) begin
                tester #(`WORD_S)::verify_output(results[i], expected_results[j]);
        end

        $display("Testcase 3 done with %d errors.\n", error_cnt);
        if (error_cnt != 0)
                $finish;

        // No cleanup
endtask
