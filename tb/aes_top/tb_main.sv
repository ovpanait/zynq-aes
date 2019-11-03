`timescale 1ns/1ns
`define PERIOD 5

`include "aes.vh"

module tb_main();

reg clk;
reg reset;
reg en;

reg aes128_mode;
reg aes256_mode;

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

        .aes128_mode(aes128_mode),
        .aes256_mode(aes256_mode),

        .aes_key(aes_key),
        .aes_in_blk(aes_in_blk),

        .cipher_mode(cipher_mode),
        .decipher_mode(decipher_mode),
        .key_exp_mode(key_exp_mode),

        .aes_out_blk(aes_out_blk),
        .en_o(en_o)
);

`include "test_fc.vh"

localparam [`KEY_S-1:0] key_128 = 'h00000000000000000000000000000000754620676e754b20796d207374616854;
localparam [`KEY_S-1:0] key_256 = 'h1f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100;

localparam [`BLK_S-1:0] plaintext_256_t1 = 'hffeeddccbbaa99887766554433221100;
localparam [`BLK_S-1:0] ciphertext_256_t1 = 'h8960494b9049fceabf456751cab7a28e;
localparam [`BLK_S-1:0] plaintext_128_t1 = 'h6F775420656E694E20656E4F206F7754;
localparam [`BLK_S-1:0] ciphertext_128_t1 = 'h3ad7021ab3992240f62014575f50c329;
localparam [`BLK_S-1:0] plaintext_128_t2 = 'h01896745230189674523119178563412;
localparam [`BLK_S-1:0] ciphertext_128_t2 = 'h153e7de995d7d6481eba136046b11429;

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

        test_aes(1'b1, 1'b0, key_128, plaintext_128_t1, ciphertext_128_t1);
        test_aes(1'b1, 1'b0, key_128, plaintext_128_t2, ciphertext_128_t2);
        test_aes(1'b0, 1'b1, key_256, plaintext_256_t1, ciphertext_256_t1);

        // Testcase end
        @(negedge clk) reset = 1;
        @(negedge clk);

        $display("Testcase: PASS!");
        $finish;
end

task test_aes(
	input aes128,
	input aes256,
	input [`KEY_S-1:0] key,
	input [`BLK_S-1:0] plaintext,
	input [`BLK_S-1:0] ciphertext
	);

        @(negedge clk) begin
                aes128_mode = aes128;
                aes256_mode = aes256;

                cipher_mode = 1'b0;
                decipher_mode = 1'b0;
                key_exp_mode = 1'b1;
                en = 1'b1;
                aes_key = key;
        end

        @(negedge clk) begin
                en = 0;
        end

        @(posedge en_o);

        // Test en_o clock cycle
        @(negedge clk);
        @(negedge clk);
        `VERIFY(en_o, 1'b0);

        // Encrypt
        @(negedge clk) begin
                cipher_mode = 1'b1;
                decipher_mode = 1'b0;
                key_exp_mode = 1'b0;

                en = 1'b1;
                aes_key = {`KEY_S{1'b0}};
                aes_in_blk = plaintext;
        end;

        @(negedge clk);
        en = 1'b0;

        // Test ciphertext output
        @(posedge en_o);
        @(negedge clk) begin
                `VERIFY(aes_out_blk, ciphertext);
        end

        // Test en_o clock cycle
        @(negedge clk);
        `VERIFY(en_o, 1'h0);

        // Decrypt
        @(negedge clk) begin
                cipher_mode = 1'b0;
                decipher_mode = 1'b1;
                key_exp_mode = 1'b0;

                en = 1'b1;
                aes_in_blk = ciphertext;
        end

        @(negedge clk) begin
                en = 1'b0;
        end

        @(posedge en_o);
        @(negedge clk) begin
                `VERIFY(aes_out_blk, plaintext);
        end

        // TODO
        // Test en_o clock cycle
        //@(negedge clk);
        //`VERIFY(en_o, 1'h0);
endtask

endmodule
