// Test 1
// Encrypt two blocks in one go
task testcase2();
        integer initial_cmp_cnt; // testcase comparison counter
        integer i, j;
        reg [0:`WORD_S-1] expected_results[$] ={
                // Test 1
                32'h29c3505f,
                32'h571420f6,
                32'h402299b3,
                32'h1a02d73a,

                // Test 2
                32'h2914b146,
                32'h6013ba1e,
                32'h48d6d795,
                32'he97d3e15
        };

        $display("Starting Testcase: Encrypt two blocks in one go.");

        initial_cmp_cnt = comparison_cnt;
        aes128_in_blk =  {
                8'h54, 8'h77, 8'h6F, 8'h20,
                8'h4F, 8'h6E, 8'h65, 8'h20,
                8'h4E, 8'h69, 8'h6E, 8'h65,
                8'h20, 8'h54, 8'h77, 8'h6F
        };

        // The values need to be swapped to match the values put by the kernel on the AXI bus
        aes128_in_blk = swap_blk(aes128_in_blk);

        tester #(32)::packed_to_unpacked(`ENCRYPT, data_tmp);
        tester::print_unpacked(data_tmp);
        gen_transaction(data_tmp);

        tester #($size(aes128_in_blk))::packed_to_unpacked(aes128_in_blk, data_tmp);
        tester::print_unpacked(data_tmp);
        gen_transaction(data_tmp);

        aes128_in_blk = {
                8'h12, 8'h34, 8'h56, 8'h78,
                8'h91, 8'h11, 8'h23, 8'h45,
                8'h67, 8'h89, 8'h01, 8'h23,
                8'h45, 8'h67, 8'h89, 8'h01
        };
        aes128_in_blk = swap_blk(aes128_in_blk);

        tester #($size(aes128_in_blk))::packed_to_unpacked(aes128_in_blk, data_tmp);
        tester::print_unpacked(data_tmp);
        gen_transaction(data_tmp, 1);

        wait(comparison_cnt == initial_cmp_cnt + 8);
        for (i = initial_cmp_cnt, j=0; i < comparison_cnt; i=i+1, j=j+1) begin
                tester #(`WORD_S)::verify_output(results[i], expected_results[j]);
        end

        $display("Testcase 2 done with %d errors.\n", error_cnt);
        if (error_cnt != 0)
                $finish;

        // No cleanup
endtask