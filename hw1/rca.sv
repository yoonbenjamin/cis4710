// Tell the simulator that we express delays at nanosecond granularity, and that
// it should track timing at nanosecond granularity as well.
`timescale 1ns / 1ns

// prevents undeclared wires from being inferred
`default_nettype none

/* A half-adder that adds two 1-bit numbers and produces a 2-bit result (as sum
 * and carry-out) */
module halfadder(input wire  a,
                 input wire  b,
                 output wire s,
                 output wire cout);
   assign s = a ^ b;
   assign cout = a & b;
endmodule

/* A full adder adds three 1-bit numbers (a, b, carry-in) and produces a 2-bit
 * result (as sum and carry-out) */
module fulladder(input wire  cin,
                 input wire  a,
                 input wire  b,
                 output wire s,
                 output wire cout);
   wire s_tmp, cout_tmp1, cout_tmp2;
   halfadder h0(.a(a), .b(b), .s(s_tmp), .cout(cout_tmp1));  // corrected output
   halfadder h1(.a(s_tmp), .b(cin), .s(s), .cout(cout_tmp2));
   assign cout = cout_tmp1 | cout_tmp2;
endmodule

/* A full adder that adds 2-bit numbers. Builds upon the 1-bit full adder. */
module fulladder2(input wire        cin,
                  input wire  [1:0] a,
                  input wire  [1:0] b,
                  output wire [1:0] s,
                  output wire       cout);
   wire cout_tmp;
   // Corrected connection of fulladder a0 output wires to s[0] and cout_tmp
   fulladder a0(.cin(cin), .a(a[0]), .b(b[0]), .s(s[0]), .cout(cout_tmp));
   // Corrected connection of fulladder a1 output wires to s[1] and cout
   fulladder a1(.cin(cout_tmp), .a(a[1]), .b(b[1]), .s(s[1]), .cout(cout));
endmodule

/* 4-bit ripple-carry adder that adds two 4-bit numbers (taken from the
 * ZedBoard's switches) and produces a 4-bit result (displayed on the ZedBoard's
 * LEDs) */
module rca4(input wire  [7:0] SWITCH,
            output wire [7:0] LED);
   wire cout0, ignored;
   // Corrected fulladder2 a0 input wire cin to be 0
   fulladder2 a0(.cin(1'b0), .a(SWITCH[1:0]), .b(SWITCH[5:4]), .s(LED[1:0]), .cout(cout0));
   // Corrected fulladder2 a3 input wire a signal
   fulladder2 a3(.cin(cout0), .a(SWITCH[3:2]), .b(SWITCH[7:6]), .s(LED[3:2]), .cout(ignored));
   assign LED[7:4] = 4'h0;
endmodule
