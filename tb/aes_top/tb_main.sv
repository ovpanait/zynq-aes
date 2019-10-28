`timescale 1ns/1ns
`define PERIOD 5

`include "aes.vh"

module tb_main();

reg clk;
reg reset;
reg en;

reg decipher_mode;
reg cipher_mode;
reg key_exp_mode;

reg [`KEY_S-1:0]  aes_key;
reg [`BLK_S-1:0]  aes_in_blk;

wire [`BLK_S-1:0] aes_out_blk;
wire              en_o;

aes_top DUT (
        .clk(clk),
        .reset(reset),
        .en(en),

        .aes_key(aes_key),
        .aes_in_blk(aes_in_blk),

        .cipher_mode(cipher_mode),
        .decipher_mode(decipher_mode),
        .key_exp_mode(key_exp_mode),

        .aes_out_blk(aes_out_blk),
        .en_o(en_o)
);

`include "test_fc.vh"

integer i;

initial begin
        clk <= 0;
        forever #(`PERIOD) clk = ~clk;
end

initial begin
        reset <= 0;
        @(posedge clk);
        @(negedge clk) reset = 1;
end

initial begin
        // Testcase init
        wait(reset)
        @(posedge clk);
        @(negedge clk) reset = 0;

        @(negedge clk) begin
                cipher_mode = 1'b0;
                decipher_mode = 1'b0;
                key_exp_mode = 1'b1;
                en = 1'b1;
                aes_key = `KEY_S'h754620676e754b20796d207374616854;
        end

        @(negedge clk) begin
                en = 0;
        end

        @(posedge en_o);

        // Test en_o clock cycle
        @(negedge clk);
        @(negedge clk);
        `VERIFY(en_o, 1'b0);

        // Testcase 1
        `define T1_AES_PLAINTEXT `BLK_S'h6F775420656E694E20656E4F206F7754
        `define T1_AES_CIPHERTEXT `BLK_S'h3ad7021ab3992240f62014575f50c329

        @(negedge clk) begin
                cipher_mode = 1'b1;
                decipher_mode = 1'b0;
                key_exp_mode = 1'b0;

                en = 1'b1;
                aes_key = {`KEY_S{1'b0}};
                aes_in_blk = `T1_AES_PLAINTEXT;
        end;

        @(negedge clk);
        en = 1'b0;

        // Test ciphertext output
        @(posedge en_o);
        @(negedge clk) begin
                `VERIFY(aes_out_blk, `T1_AES_CIPHERTEXT);
        end

        // Test en_o clock cycle
        @(negedge clk);
        `VERIFY(en_o, 1'h0);

        // Test decryption
        @(negedge clk) begin
                cipher_mode = 1'b0;
                decipher_mode = 1'b1;
                key_exp_mode = 1'b0;

                en = 1'b1;
                aes_in_blk = `T1_AES_CIPHERTEXT;
        end

        @(negedge clk) begin
                en = 1'b0;
        end

        @(posedge en_o);
        @(negedge clk) begin
                `VERIFY(aes_out_blk, `T1_AES_PLAINTEXT);
        end

        // TODO
        // Test en_o clock cycle
        //@(negedge clk);
        //`VERIFY(en_o, 1'h0);

        // Testcase 2
        `define T2_AES_PLAINTEXT `BLK_S'h01896745230189674523119178563412
        `define T2_AES_CIPHERTEXT `BLK_S'h153e7de995d7d6481eba136046b11429
        @(negedge clk) begin
                en = 1'b1;

                cipher_mode = 1'b1;
                decipher_mode = 1'b0;
                key_exp_mode = 1'b0;

                aes_key = {`KEY_S{1'b0}};
                aes_in_blk = `T2_AES_PLAINTEXT;
        end

        @(negedge clk) begin
                en = 1'b0;
        end

        @(posedge en_o);
        @(negedge clk);
        `VERIFY(aes_out_blk, `T2_AES_CIPHERTEXT);

        // Test en_o clock cycle
        @(negedge clk);
        `VERIFY(en_o, 1'h0);

        // Test decryption
        @(negedge clk) begin
                cipher_mode = 1'b0;
                decipher_mode = 1'b1;
                key_exp_mode = 1'b0;

                en = 1'b1;
                aes_in_blk = `T2_AES_CIPHERTEXT;
        end

        @(negedge clk) begin
                en = 1'b0;
        end

        @(posedge en_o);
        @(negedge clk) begin
                `VERIFY(aes_out_blk, `T2_AES_PLAINTEXT);
        end

        // TODO
        // Test en_o clock cycle
        //@(negedge clk);
        //`VERIFY(en_o, 1'h0);

        // Testcase end
        @(negedge clk) reset = 1;
        @(negedge clk);

        $display("Testcase: PASS!");
        $finish;
end
endmodule
