`timescale 1ns/1ns
`define PERIOD 5

`include "aes.vh"

module tb_main();

reg clk;
reg reset;

reg en_cipher;
reg en_decipher;
reg en_key;

reg aes128_mode;
reg aes256_mode;

reg [`KEY_S-1:0]  aes_key;
reg [`BLK_S-1:0]  aes_in_blk;

wire [`BLK_S-1:0] aes_out_blk;
wire              en_o;

aes_top DUT (
        .clk(clk),
        .reset(reset),

	.en_cipher(en_cipher),
	.en_decipher(en_decipher),
	.en_key(en_key),

        .aes128_mode(aes128_mode),
        .aes256_mode(aes256_mode),

        .aes_key(aes_key),
        .aes_in_blk(aes_in_blk),

        .aes_out_blk(aes_out_blk),
        .en_o(en_o)
);

`include "test_fc.vh"

localparam [`KEY_S-1:0] key_128 = 'h000102030405060708090a0b0c0d0e0f00000000000000000000000000000000;
localparam [`KEY_S-1:0] key_256 = 'h000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f;

localparam [`BLK_S-1:0] plaintext_256_t1 = 'h00112233445566778899aabbccddeeff;
localparam [`BLK_S-1:0] ciphertext_256_t1 = 'h8ea2b7ca516745bfeafc49904b496089;
localparam [`BLK_S-1:0] plaintext_128_t1 = 'h00112233445566778899aabbccddeeff;
localparam [`BLK_S-1:0] ciphertext_128_t1 = 'h69c4e0d86a7b0430d8cdb78070b4c55a;
localparam [`BLK_S-1:0] plaintext_128_t2 = 'h01896745230189674523119178563412;
localparam [`BLK_S-1:0] ciphertext_128_t2 = 'h14aa0d560e4a7b60d52bba86dece5277;

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
        test_aes(1'b0, 1'b1, key_256, plaintext_256_t1, ciphertext_256_t1);
        test_aes(1'b1, 1'b0, key_128, plaintext_128_t2, ciphertext_128_t2);

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

		en_cipher = 1'b0;
		en_decipher = 1'b0;
		en_key = 1'b1;

                aes_key = key;
        end

        @(negedge clk) begin
		en_key = 0;
        end

        @(posedge en_o);

        // Test en_o clock cycle
        @(negedge clk);
        @(negedge clk);
        `VERIFY(en_o, 1'b0);

        // Encrypt
        @(negedge clk) begin
		en_cipher = 1'b1;
		en_decipher = 1'b0;
		en_key = 1'b0;

                aes_key = {`KEY_S{1'b0}};
                aes_in_blk = plaintext;
        end;

        @(negedge clk);
		en_cipher = 1'b0;

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
		en_cipher = 1'b0;
		en_decipher = 1'b1;
		en_key = 1'b0;

                aes_in_blk = ciphertext;
        end

        @(negedge clk) begin
		en_decipher = 1'b0;
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
