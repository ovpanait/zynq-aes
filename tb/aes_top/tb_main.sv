
`timescale 1ns/1ns
`define PERIOD 5

`include "aes.vh"

module tb_main();

// Module instantiation
reg clk;
reg reset;
reg en;

reg [0:`WORD_S-1] aes_cmd;
reg [0:`KEY_S-1] aes_key;
reg [0:`BLK_S-1] aes_in_blk;

wire [0:`BLK_S-1] aes_out_blk;
wire 	     en_o;

aes_top DUT (
        .clk(clk),
        .reset(reset),
        .en(en),

        .aes_cmd(aes_cmd),
        .aes_key(aes_key),
        .aes_in_blk(aes_in_blk),

        .aes_out_blk(aes_out_blk),
        .en_o(en_o)
);

// Test functions
`include "test_fc.vh"

// Auxiliary counters
integer 	     i;

// Test results
initial begin
        clk <= 0;
        forever #(`PERIOD) clk = ~clk;
end

initial begin
        reset <= 0;
        @(posedge clk); //may need several cycles for reset
        @(negedge clk) reset = 1;
end

initial begin
        errors = 0; // reset error count

        // Testcase init
        wait(reset)
        @(posedge clk);
        @(negedge clk) reset = 0;

        // Set key
        @(negedge clk) begin
                en = 1'b1;
                aes_cmd = `SET_KEY;
                aes_key =  {
                        8'h54, 8'h68, 8'h61, 8'h74,
                        8'h73, 8'h20, 8'h6D, 8'h79,
                        8'h20, 8'h4B, 8'h75, 8'h6E,
                        8'h67, 8'h20, 8'h46, 8'h75
                };
        end

        @(negedge clk) begin
                en = 0;
        end

        @(posedge en_o);

        // Test en_o clock cycle
        @(negedge clk);
        @(negedge clk);
        tester #($size(en_o))::verify_output(en_o, 1'b0);

        // Testcase 1
        `define T1_AES_PLAINTEXT `BLK_S'h54776f204f6e65204e696e652054776f
        `define T1_AES_CIPHERTEXT `BLK_S'h29c3505f571420f6402299b31a02d73a

        @(negedge clk) begin
                en = 1'b1;
                aes_cmd = `ENCRYPT;
                aes_key = {`KEY_S{1'b0}};
                aes_in_blk = `T1_AES_PLAINTEXT;
        end;

        @(negedge clk);
        en = 1'b0;

        // Test ciphertext output
        @(posedge en_o);

        @(negedge clk) begin
                tester #($size(aes_out_blk))::verify_output(aes_out_blk, `T1_AES_CIPHERTEXT);
        end

        // Test en_o clock cycle
        @(negedge clk);
        tester #($size(en_o))::verify_output(en_o, 1'h0);

        // Test decryption
        @(negedge clk) begin
                en = 1'b1;
                aes_cmd = `DECRYPT;
                aes_in_blk = `T1_AES_CIPHERTEXT;
        end

        @(negedge clk) begin
                en = 1'b0;
        end

        @(posedge en_o);
        @(negedge clk) begin
                tester #($size(aes_out_blk))::verify_output(aes_out_blk, `T1_AES_PLAINTEXT);
        end

        // Test en_o clock cycle
        @(negedge clk);
        tester #($size(en_o))::verify_output(en_o, 1'h0);

        // Testcase 2
        // Test encryption without changing keys
        `define T2_AES_PLAINTEXT `BLK_S'h12345678911123456789012345678901
        `define T2_AES_CIPHERTEXT `BLK_S'h2914b1466013ba1e48d6d795e97d3e15
        @(negedge clk) begin
                en = 1'b1;
        
                aes_cmd = `ENCRYPT;
                aes_key = {`KEY_S{1'b0}};
                aes_in_blk = `T2_AES_PLAINTEXT;
        end

        @(negedge clk) begin
                en = 1'b0;
        end

        @(posedge en_o);
        @(negedge clk); 
        tester #($size(aes_out_blk))::verify_output(aes_out_blk, `T2_AES_CIPHERTEXT);

        // Test en_o clock cycle
        @(negedge clk);
        tester #($size(en_o))::verify_output(en_o, 1'h0);

        // Test decryption
        @(negedge clk) begin
                en = 1'b1;
                aes_cmd = `DECRYPT;
                aes_in_blk = `T2_AES_CIPHERTEXT;
        end

        @(negedge clk) begin
                en = 1'b0;
        end

        @(posedge en_o);
        @(negedge clk) begin
                tester #($size(aes_out_blk))::verify_output(aes_out_blk, `T2_AES_PLAINTEXT);
        end

        // Test en_o clock cycle
        @(negedge clk);
        tester #($size(en_o))::verify_output(en_o, 1'h0);


        // Testcase end
        @(negedge clk) reset = 1;
        @(negedge clk);

        $display("\nSimulation completed with %d errors\n", errors);
        $stop;
end // initial begin
endmodule
