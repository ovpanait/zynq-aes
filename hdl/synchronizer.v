module synchronizer #(
	parameter WIDTH = 1,
	parameter RESET_STATE = 0
)(
	input                      clk,
	input                      reset,

	input [WIDTH - 1:0]        data_i,
	output reg [WIDTH - 1:0]   data_o
);

    reg [WIDTH - 1:0] sync0;
    reg [WIDTH - 1:0] sync1;

    always @(posedge clk, posedge reset) begin
        if (reset) begin
            sync0 <= {WIDTH{RESET_STATE}};
            sync1 <= {WIDTH{RESET_STATE}};
            data_o <= {WIDTH{RESET_STATE}};
        end else begin
            sync0 <= data_i;
            sync1 <= sync0;
            data_o <= sync1;
        end
    end

endmodule
