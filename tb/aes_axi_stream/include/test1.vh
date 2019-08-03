// Test 1
// Test Key Expansion
task testcase1();
        integer initial_cmp_cnt; // testcase comparison counter
        integer i, j;
        reg [0:`WORD_S-1] expected_results[$] = {
                32'h0,
                32'h0,
                32'h0,
                32'h0
        };

        $display("Starting Testcase: Key expansion");

        initial_cmp_cnt = comparison_cnt;

        aes128_in_blk =  {
                8'h54, 8'h68, 8'h61, 8'h74,
                8'h73, 8'h20, 8'h6D, 8'h79,
                8'h20, 8'h4B, 8'h75, 8'h6E,
                8'h67, 8'h20, 8'h46, 8'h75
        };

        aes128_in_blk = swap_blk(aes128_in_blk);

        // Key expansion
        tester #(32)::packed_to_unpacked(`SET_KEY_128, data_tmp);
        tester::print_unpacked(data_tmp);
        gen_transaction(data_tmp);

        tester #($size(aes128_in_blk))::packed_to_unpacked(aes128_in_blk, data_tmp);
        tester::print_unpacked(data_tmp);
        gen_transaction(data_tmp, 1);

        wait(comparison_cnt == initial_cmp_cnt + 4);

        for (i = initial_cmp_cnt, j=0; i < comparison_cnt; i=i+1, j=j+1) begin
                tester #(`WORD_S)::verify_output(results[i], expected_results[j], errors);
        end

        $display("Testcase 1 done with %d errors.\n", errors);
        if (errors != 0)
                $finish;

        // No cleanup
endtask
