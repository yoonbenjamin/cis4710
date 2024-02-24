/* INSERT NAME AND PENNKEY HERE */
/* BENJAMIN YOON / YOONB */

`timescale 1ns / 1ns

// quotient = dividend / divisor

module divider_unsigned (
    input  wire [31:0] i_dividend,
    input  wire [31:0] i_divisor,
    output wire [31:0] o_remainder,
    output wire [31:0] o_quotient
);

    // TODO: your code here
    wire [31:0] dividend[0:32];
    wire [31:0] remainder[0:32];
    wire [31:0] quotient[0:32];

    // Initialize 1st inputs
    assign dividend[0] = i_dividend;
    assign remainder[0] = 0;
    assign quotient[0] = 0;

    genvar i;
    generate
        for (i = 0; i < 32; i = i + 1) begin : d_block
            divu_1iter u_1iter (
                .i_dividend(dividend[i]),
                .i_divisor(i_divisor),
                .i_remainder(remainder[i]),
                .i_quotient(quotient[i]),
                .o_dividend(dividend[i + 1]),
                .o_remainder(remainder[i + 1]),
                .o_quotient(quotient[i + 1])
            );
        end
    endgenerate

    // Final outputs
    assign o_remainder = remainder[32];
    assign o_quotient = quotient[32];

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
  /*
    for (int i = 0; i < 32; i++) {
        remainder = (remainder << 1) | ((dividend >> 31) & 0x1);
        if (remainder < divisor) {
            quotient = (quotient << 1);
        } else {
            quotient = (quotient << 1) | 0x1;
            remainder = remainder - divisor;
        }
        dividend = dividend << 1;
    }
    */

    // TODO: your code here
    // Extend to 32 bits
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
