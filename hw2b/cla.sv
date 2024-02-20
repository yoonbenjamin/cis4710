`timescale 1ns / 1ps

/**
 * @param a first 1-bit input
 * @param b second 1-bit input
 * @param g whether a and b generate a carry
 * @param p whether a and b would propagate an incoming carry
 */
module gp1(input wire a, b,
           output wire g, p);
   assign g = a & b;
   assign p = a | b;
endmodule

/**
 * Computes aggregate generate/propagate signals over a 4-bit window.
 * @param gin incoming generate signals
 * @param pin incoming propagate signals
 * @param cin the incoming carry
 * @param gout whether these 4 bits collectively generate a carry (takes cin into account)
 * @param pout whether these 4 bits collectively would propagate an incoming carry (ignoring cin)
 * @param cout the carry outs for the low-order 3 bits
 */
module gp4(input wire [3:0] gin, pin,
           input wire cin,
           output wire gout, pout,
           output wire [2:0] cout);

   // TODO: your code here
   assign pout = &pin;
   
   // Aggregate generate
   assign gout = gin[3] | (pin[3] & gin[2]) | (pin[3] & pin[2] & gin[1]) | (pin[3] & pin[2] & pin[1] & gin[0]);
   
   // Compute carry outs
   assign cout[0] = gin[0] | (pin[0] & cin);
   assign cout[1] = gin[1] | (pin[1] & (gin[0] | (pin[0] & cin)));
   assign cout[2] = gin[2] | (pin[2] & (gin[1] | (pin[1] & (gin[0] | (pin[0] & cin)))));

endmodule

/** Same as gp4 but for an 8-bit window instead */
module gp8(input wire [7:0] gin, pin,
           input wire cin,
           output wire gout, pout,
           output wire [6:0] cout);

   // TODO: your code here
   assign pout = &pin;
   
   // Aggregate generate
   assign gout = gin[7] | (pin[7] & gin[6]) | (pin[7] & pin[6] & gin[5]) | (pin[7] & pin[6] & pin[5] & gin[4])
                        | (pin[7] & pin[6] & pin[5] & pin[4] & gin[3]) | (pin[7] & pin[6] & pin[5] & pin[4] & pin[3] & gin[2])
                        | (pin[7] & pin[6] & pin[5] & pin[4] & pin[3] & pin[2] & gin[1]) | (pin[7] & pin[6] & pin[5] & pin[4] & pin[3] & pin[2] & pin[1] & gin[0]);
                        
   // Compute carry outs
   assign cout[0] = gin[0] | (pin[0] & cin);
   assign cout[1] = gin[1] | (pin[1] & (gin[0] | (pin[0] & cin)));
   assign cout[2] = gin[2] | (pin[2] & (gin[1] | (pin[1] & (gin[0] | (pin[0] & cin)))));
   assign cout[3] = gin[3] | (pin[3] & (gin[2] | (pin[2] & (gin[1] | (pin[1] & (gin[0] | (pin[0] & cin)))))));
   assign cout[4] = gin[4] | (pin[4] & (gin[3] | (pin[3] & (gin[2] | (pin[2] & (gin[1] | (pin[1] & (gin[0] | (pin[0] & cin)))))))));
   assign cout[5] = gin[5] | (pin[5] & (gin[4] | (pin[4] & (gin[3] | (pin[3] & (gin[2] | (pin[2] & (gin[1] | (pin[1] & (gin[0] | (pin[0] & cin)))))))))));
   assign cout[6] = gin[6] | (pin[6] & (gin[5] | (pin[5] & (gin[4] | (pin[4] & (gin[3] | (pin[3] & (gin[2] | (pin[2] & (gin[1] | (pin[1] & (gin[0] | (pin[0] & cin)))))))))))));

endmodule

module cla
  (input wire [31:0]  a, b,
   input wire         cin,
   output wire [31:0] sum);

   // TODO: your code here
   wire [31:0] g, p;      // Generate and Propagate
   wire [7:0] g4, p4;     // Aggregate G&P from gp4 
   wire [31:0] c;     // Carry
   wire g8, p8;           // Aggregate G&P from gp8
   wire [6:0] c8;      // Carry outs from gp8
   
   // Generate G&P signals
   genvar i;
   generate
    for (i = 0; i < 32; i = i + 1) begin : gp1g
        gp1 gp1i(.a(a[i]), .b(b[i]), .g(g[i]), .p(p[i]));
    end
   endgenerate
   
   // Aggregate G&P signals using gp4, manually instantiate modules
   gp4 gp4i0(.gin(g[3:0]), .pin(p[3:0]), .cin(c[0]), .gout(g4[0]), .pout(p4[0]), .cout({c[3], c[2], c[1]}));
   gp4 gp4i1(.gin(g[7:4]), .pin(p[7:4]), .cin(c[4]), .gout(g4[1]), .pout(p4[1]), .cout({c[7], c[6], c[5]}));
   gp4 gp4i2(.gin(g[11:8]), .pin(p[11:8]), .cin(c[8]), .gout(g4[2]), .pout(p4[2]), .cout({c[11], c[10], c[9]}));
   gp4 gp4i3(.gin(g[15:12]), .pin(p[15:12]), .cin(c[12]), .gout(g4[3]), .pout(p4[3]), .cout({c[15], c[14], c[13]}));
   gp4 gp4i4(.gin(g[19:16]), .pin(p[19:16]), .cin(c[16]), .gout(g4[4]), .pout(p4[4]), .cout({c[19], c[18], c[17]}));
   gp4 gp4i5(.gin(g[23:20]), .pin(p[23:20]), .cin(c[20]), .gout(g4[5]), .pout(p4[5]), .cout({c[23], c[22], c[21]}));
   gp4 gp4i6(.gin(g[27:24]), .pin(p[27:24]), .cin(c[24]), .gout(g4[6]), .pout(p4[6]), .cout({c[27], c[26], c[25]}));
   gp4 gp4i7(.gin(g[31:28]), .pin(p[31:28]), .cin(c[28]), .gout(g4[7]), .pout(p4[7]), .cout({c[31], c[30], c[29]}));
   
   // Use gp8 to aggregate G&P signals from gp4 blocks
   gp8 gp8i(.gin(g4), .pin(p4), .cin(cin), .gout(g8), .pout(p8), .cout(c8));
   
   // Hook up carries b/w gp4 blocks, driven by gp8 couts
   assign c[0] = cin; // Initial carry-in
   assign c[4] = c8[0];
   assign c[8] = c8[1];
   assign c[12] = c8[2];
   assign c[16] = c8[3];
   assign c[20] = c8[4];
   assign c[24] = c8[5];
   assign c[28] = c8[6];
   
   // Compute sum
   assign sum = a ^ b ^ c;

endmodule
