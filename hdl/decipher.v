`include "aes.vh"

module decipher (
        input clk,
        input reset,
        input en,

        input [0:`BLK_S-1] ciphertext,
        input [0:`KEY_S-1] round_key,

        output reg r_e,
        output [0:`Nk-1] round_no,
        output reg [0:`BLK_S-1] plaintext,
        output reg en_o
);

localparam IDLE = 2'b0,
        INIT_SRAM =2'b1,
        FIRST_DECRYPT_ROUND = 2'b10,
        DECRYPT_ROUND = 2'b11;

reg [0:`Nk-1] _round_no;
assign round_no = _round_no - 1'b1;

reg [0:1] fsm_state;

reg [0:`BLK_S-1] decrypt_inv_shift_rows;
reg [0:`BLK_S-1] decrypt_inv_sub_bytes;
reg [0:`BLK_S-1] decrypt_add_round_key;
reg [0:`BLK_S-1] decrypt_inv_mix_columns;
reg [0:`BLK_S-1] decrypt_round_state;

`include "aes_functions.vh"

always @(*) begin
          decrypt_inv_shift_rows = inv_shift_rows(plaintext);
          decrypt_inv_sub_bytes = inv_sub_bytes(decrypt_inv_shift_rows);
          decrypt_add_round_key = decrypt_inv_sub_bytes ^ round_key;
          decrypt_inv_mix_columns = (_round_no == 1'b0) ? decrypt_add_round_key : inv_mix_cols(decrypt_add_round_key);

          decrypt_round_state = decrypt_inv_mix_columns;
end

always @(posedge clk) begin
        if (reset == 1'b1) begin
                r_e <= 1'b0;
                _round_no <= 1'b0;
                plaintext <= 1'b0;
                en_o <= 1'b0;
        end else begin
                en_o <= 1'b0;

                case (fsm_state)
                IDLE:
                begin
                        r_e <= 1'b0;

                        if (en == 1'b1) begin
                                plaintext <= ciphertext;
                                _round_no <= `Nr + 1;

                                fsm_state <= INIT_SRAM;
                                r_e <= 1'b1;
                        end
                end
                INIT_SRAM:
                // Wait one clock cycle for the block RAM data to be available
                begin
                        fsm_state <= FIRST_DECRYPT_ROUND;
                        r_e <= 1'b1;
                        
                        _round_no <= round_no;
                end
                FIRST_DECRYPT_ROUND:
                begin
                        r_e <= 1'b1;
                        _round_no <= round_no;

                        plaintext <= plaintext ^ round_key;

                        fsm_state <= DECRYPT_ROUND;
                end
                DECRYPT_ROUND:
                begin
                        r_e <= 1'b1;
                        _round_no <= round_no;

                        plaintext <= decrypt_round_state;

                        if (_round_no == 1'b0) begin
                                fsm_state <= IDLE;
                                en_o <= 1'b1;
                                r_e <= 1'b0;
                        end
                end
                default:
                begin
                        fsm_state <= IDLE;
                end
                endcase
        end
end

endmodule
