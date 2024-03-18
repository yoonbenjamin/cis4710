/* INSERT NAME AND PENNKEY HERE */
/* BENJAMIN YOON / YOONB */

`timescale 1ns / 1ns

// quotient = dividend / divisor

module divider_unsigned_pipelined (
    input wire clk, rst,
    input  wire [31:0] i_dividend,
    input  wire [31:0] i_divisor,
    output wire [31:0] o_remainder,
    output wire [31:0] o_quotient
);

    // TODO: your code here
    wire [31:0] dividend_1stage[0:16], remainder_1stage[0:16], quotient_1stage[0:16];
    wire [31:0] dividend_2stage[0:16], remainder_2stage[0:16], quotient_2stage[0:16];

    // intermediate regs
    reg [31:0] out_remainder, out_quotient;

    // initialize 1st elements
    assign dividend_1stage[0] = i_dividend;
    assign remainder_1stage[0] = 0;
    assign quotient_1stage[0] = 0;

    genvar i;
    // generate loop
    generate
        for (i = 0; i < 16; i++) begin : logic_1stage
            divu_1iter divu_1stage (
                .i_dividend(dividend_1stage[i]),
                .i_divisor(i_divisor), // divisor doesn't change
                .i_remainder(remainder_1stage[i]),
                .i_quotient(quotient_1stage[i]),
                .o_dividend(dividend_1stage[i+1]),
                .o_remainder(remainder_1stage[i+1]),
                .o_quotient(quotient_1stage[i+1])
            );
        end
    endgenerate

    // initialize 1st elements for stage 2
    assign dividend_2stage[0] = dividend_1stage[16];
    assign remainder_2stage[0] = remainder_1stage[16];
    assign quotient_2stage[0] = quotient_1stage[16];

    // generate loop for stage 2
    generate
        for (i = 0; i < 16; i++) begin : logic_2stage
            divu_1iter divu_2stage (
                .i_dividend(dividend_2stage[i]),
                .i_divisor(i_divisor), // divisor doesn't change
                .i_remainder(remainder_2stage[i]),
                .i_quotient(quotient_2stage[i]),
                .o_dividend(dividend_2stage[i+1]),
                .o_remainder(remainder_2stage[i+1]),
                .o_quotient(quotient_2stage[i+1])
            );
        end
    endgenerate

    // assign outputs
    always @(posedge clk or posedge rst) begin
        if (rst) begin
            out_remainder <= 0;
            out_quotient <= 0;
        end else begin
            out_remainder <= remainder_2stage[16];
            out_quotient <= quotient_2stage[16];
        end
    end

    // continuous assignments
    assign o_remainder = out_remainder;
    assign o_quotient = out_quotient;

endmodule


module divu_1iter (
    input  wire [31:0] i_dividend,
    input  wire [31:0] i_divisor,
    input  wire [31:0] i_remainder,
    input  wire [31:0] i_quotient,
    output wire [31:0] o_dividend,
    output wire [31:0] o_remainder,
    output wire [31:0] o_quotient
);

  // TODO: copy your code from HW2A here
  wire [31:0] e_bit = {31'b0, i_dividend[31]};
  wire [31:0] s_remainder = (i_remainder << 1) | e_bit;

  // Shifted remainder greater than or equal to divisor?
  wire comparison = s_remainder >= i_divisor;

  // Extend to 32 bits & calculate new remainder/quotient
  assign o_remainder = comparison ? s_remainder - i_divisor : s_remainder;
  assign o_quotient = (i_quotient << 1) | {31'b0, comparison};

  // Shift dividend left for next iteration
  assign o_dividend = i_dividend << 1;

endmodule
