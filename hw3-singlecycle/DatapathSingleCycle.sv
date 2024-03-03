`timescale 1ns / 1ns

// registers are 32 bits in RV32
`define REG_SIZE 31:0

// RV opcodes are 7 bits
`define OPCODE_SIZE 6:0

`include "../hw2a/divider_unsigned.sv"
`include "../hw2b/cla.sv"

module RegFile (
    input logic [4:0] rd,
    input logic [`REG_SIZE] rd_data,
    input logic [4:0] rs1,
    output logic [`REG_SIZE] rs1_data,
    input logic [4:0] rs2,
    output logic [`REG_SIZE] rs2_data,

    input logic clk,
    input logic we,
    input logic rst
);
  localparam int NumRegs = 32;
  logic [`REG_SIZE] regs[NumRegs];

  // TODO: your code here
  always_ff @(posedge clk or posedge rst) begin
    if (rst) begin
      for (int idx = 0; idx < NumRegs; idx++) begin
        regs[idx] <= 0;
      end
    end else if (we && rd != 0) begin
      // Write data
      regs[rd] <= rd_data;
    end
  end

  // Read data
  always_comb begin
    rs1_data = (rs1 == 0) ? 0 : regs[rs1];
    rs2_data = (rs2 == 0) ? 0 : regs[rs2];
  end

endmodule

module DatapathSingleCycle (
    input wire clk,
    input wire rst,
    output logic halt,
    output logic [`REG_SIZE] pc_to_imem,
    input wire [`REG_SIZE] insn_from_imem,
    // addr_to_dmem is a read-write port
    output wire [`REG_SIZE] addr_to_dmem,
    input logic [`REG_SIZE] load_data_from_dmem,
    output wire [`REG_SIZE] store_data_to_dmem,
    output wire [3:0] store_we_to_dmem
);

  // components of the instruction
  wire [6:0] insn_funct7;
  wire [4:0] insn_rs2;
  wire [4:0] insn_rs1;
  wire [2:0] insn_funct3;
  wire [4:0] insn_rd;
  wire [`OPCODE_SIZE] insn_opcode;

  // split R-type instruction - see section 2.2 of RiscV spec
  assign {insn_funct7, insn_rs2, insn_rs1, insn_funct3, insn_rd, insn_opcode} = insn_from_imem;

  // setup for I, S, B & J type instructions
  // I - short immediates and loads
  wire [11:0] imm_i;
  assign imm_i = insn_from_imem[31:20];
  wire [ 4:0] imm_shamt = insn_from_imem[24:20];

  // S - stores
  wire [11:0] imm_s;
  assign imm_s[11:5] = insn_funct7, imm_s[4:0] = insn_rd;

  // B - conditionals
  wire [12:0] imm_b;
  assign {imm_b[12], imm_b[10:5]} = insn_funct7, {imm_b[4:1], imm_b[11]} = insn_rd, imm_b[0] = 1'b0;

  // J - unconditional jumps
  wire [20:0] imm_j;
  assign {imm_j[20], imm_j[10:1], imm_j[11], imm_j[19:12], imm_j[0]} = {insn_from_imem[31:12], 1'b0};

  wire [`REG_SIZE] imm_i_sext = {{20{imm_i[11]}}, imm_i[11:0]};
  wire [`REG_SIZE] imm_s_sext = {{20{imm_s[11]}}, imm_s[11:0]};
  wire [`REG_SIZE] imm_b_sext = {{19{imm_b[12]}}, imm_b[12:0]};
  wire [`REG_SIZE] imm_j_sext = {{11{imm_j[20]}}, imm_j[20:0]};

  // opcodes - see section 19 of RiscV spec
  localparam bit [`OPCODE_SIZE] OpLoad = 7'b00_000_11;
  localparam bit [`OPCODE_SIZE] OpStore = 7'b01_000_11;
  localparam bit [`OPCODE_SIZE] OpBranch = 7'b11_000_11;
  localparam bit [`OPCODE_SIZE] OpJalr = 7'b11_001_11;
  localparam bit [`OPCODE_SIZE] OpMiscMem = 7'b00_011_11;
  localparam bit [`OPCODE_SIZE] OpJal = 7'b11_011_11;

  localparam bit [`OPCODE_SIZE] OpRegImm = 7'b00_100_11;
  localparam bit [`OPCODE_SIZE] OpRegReg = 7'b01_100_11;
  localparam bit [`OPCODE_SIZE] OpEnviron = 7'b11_100_11;

  localparam bit [`OPCODE_SIZE] OpAuipc = 7'b00_101_11;
  localparam bit [`OPCODE_SIZE] OpLui = 7'b01_101_11;

  wire insn_lui = insn_opcode == OpLui;
  wire insn_auipc = insn_opcode == OpAuipc;
  wire insn_jal = insn_opcode == OpJal;
  wire insn_jalr = insn_opcode == OpJalr;

  wire insn_beq = insn_opcode == OpBranch && insn_from_imem[14:12] == 3'b000;
  wire insn_bne = insn_opcode == OpBranch && insn_from_imem[14:12] == 3'b001;
  wire insn_blt = insn_opcode == OpBranch && insn_from_imem[14:12] == 3'b100;
  wire insn_bge = insn_opcode == OpBranch && insn_from_imem[14:12] == 3'b101;
  wire insn_bltu = insn_opcode == OpBranch && insn_from_imem[14:12] == 3'b110;
  wire insn_bgeu = insn_opcode == OpBranch && insn_from_imem[14:12] == 3'b111;

  wire insn_lb = insn_opcode == OpLoad && insn_from_imem[14:12] == 3'b000;
  wire insn_lh = insn_opcode == OpLoad && insn_from_imem[14:12] == 3'b001;
  wire insn_lw = insn_opcode == OpLoad && insn_from_imem[14:12] == 3'b010;
  wire insn_lbu = insn_opcode == OpLoad && insn_from_imem[14:12] == 3'b100;
  wire insn_lhu = insn_opcode == OpLoad && insn_from_imem[14:12] == 3'b101;

  wire insn_sb = insn_opcode == OpStore && insn_from_imem[14:12] == 3'b000;
  wire insn_sh = insn_opcode == OpStore && insn_from_imem[14:12] == 3'b001;
  wire insn_sw = insn_opcode == OpStore && insn_from_imem[14:12] == 3'b010;

  wire insn_addi = insn_opcode == OpRegImm && insn_from_imem[14:12] == 3'b000;
  wire insn_slti = insn_opcode == OpRegImm && insn_from_imem[14:12] == 3'b010;
  wire insn_sltiu = insn_opcode == OpRegImm && insn_from_imem[14:12] == 3'b011;
  wire insn_xori = insn_opcode == OpRegImm && insn_from_imem[14:12] == 3'b100;
  wire insn_ori = insn_opcode == OpRegImm && insn_from_imem[14:12] == 3'b110;
  wire insn_andi = insn_opcode == OpRegImm && insn_from_imem[14:12] == 3'b111;

  wire insn_slli = insn_opcode == OpRegImm && insn_from_imem[14:12] == 3'b001 && insn_from_imem[31:25] == 7'd0;
  wire insn_srli = insn_opcode == OpRegImm && insn_from_imem[14:12] == 3'b101 && insn_from_imem[31:25] == 7'd0;
  wire insn_srai = insn_opcode == OpRegImm && insn_from_imem[14:12] == 3'b101 && insn_from_imem[31:25] == 7'b0100000;

  wire insn_add = insn_opcode == OpRegReg && insn_from_imem[14:12] == 3'b000 && insn_from_imem[31:25] == 7'd0;
  wire insn_sub  = insn_opcode == OpRegReg && insn_from_imem[14:12] == 3'b000 && insn_from_imem[31:25] == 7'b0100000;
  wire insn_sll = insn_opcode == OpRegReg && insn_from_imem[14:12] == 3'b001 && insn_from_imem[31:25] == 7'd0;
  wire insn_slt = insn_opcode == OpRegReg && insn_from_imem[14:12] == 3'b010 && insn_from_imem[31:25] == 7'd0;
  wire insn_sltu = insn_opcode == OpRegReg && insn_from_imem[14:12] == 3'b011 && insn_from_imem[31:25] == 7'd0;
  wire insn_xor = insn_opcode == OpRegReg && insn_from_imem[14:12] == 3'b100 && insn_from_imem[31:25] == 7'd0;
  wire insn_srl = insn_opcode == OpRegReg && insn_from_imem[14:12] == 3'b101 && insn_from_imem[31:25] == 7'd0;
  wire insn_sra  = insn_opcode == OpRegReg && insn_from_imem[14:12] == 3'b101 && insn_from_imem[31:25] == 7'b0100000;
  wire insn_or = insn_opcode == OpRegReg && insn_from_imem[14:12] == 3'b110 && insn_from_imem[31:25] == 7'd0;
  wire insn_and = insn_opcode == OpRegReg && insn_from_imem[14:12] == 3'b111 && insn_from_imem[31:25] == 7'd0;

  wire insn_mul    = insn_opcode == OpRegReg && insn_from_imem[31:25] == 7'd1 && insn_from_imem[14:12] == 3'b000;
  wire insn_mulh   = insn_opcode == OpRegReg && insn_from_imem[31:25] == 7'd1 && insn_from_imem[14:12] == 3'b001;
  wire insn_mulhsu = insn_opcode == OpRegReg && insn_from_imem[31:25] == 7'd1 && insn_from_imem[14:12] == 3'b010;
  wire insn_mulhu  = insn_opcode == OpRegReg && insn_from_imem[31:25] == 7'd1 && insn_from_imem[14:12] == 3'b011;
  wire insn_div    = insn_opcode == OpRegReg && insn_from_imem[31:25] == 7'd1 && insn_from_imem[14:12] == 3'b100;
  wire insn_divu   = insn_opcode == OpRegReg && insn_from_imem[31:25] == 7'd1 && insn_from_imem[14:12] == 3'b101;
  wire insn_rem    = insn_opcode == OpRegReg && insn_from_imem[31:25] == 7'd1 && insn_from_imem[14:12] == 3'b110;
  wire insn_remu   = insn_opcode == OpRegReg && insn_from_imem[31:25] == 7'd1 && insn_from_imem[14:12] == 3'b111;

  wire insn_ecall = insn_opcode == OpEnviron && insn_from_imem[31:7] == 25'd0;
  wire insn_fence = insn_opcode == OpMiscMem;

  // synthesis translate_off
  // this code is only for simulation, not synthesis
  `include "RvDisassembler.sv"
  string disasm_string;
  always_comb begin
    disasm_string = rv_disasm(insn_from_imem);
  end
  // HACK: get disasm_string to appear in GtkWave, which can apparently show only wire/logic...
  wire [(8*32)-1:0] disasm_wire;
  genvar i;
  for (i = 0; i < 32; i = i + 1) begin : gen_disasm
    assign disasm_wire[(((i+1))*8)-1:((i)*8)] = disasm_string[31-i];
  end
  // synthesis translate_on

  // program counter
  logic [`REG_SIZE] pcNext, pcCurrent;
  always @(posedge clk) begin
    if (rst) begin
      pcCurrent <= 32'd0;
    end else begin
      pcCurrent <= pcNext;
    end
  end
  assign pc_to_imem = pcCurrent;

  // cycle/insn_from_imem counters
  logic [`REG_SIZE] cycles_current, num_insns_current;
  always @(posedge clk) begin
    if (rst) begin
      cycles_current <= 0;
      num_insns_current <= 0;
    end else begin
      cycles_current <= cycles_current + 1;
      if (!rst) begin
        num_insns_current <= num_insns_current + 1;
      end
    end
  end

  logic illegal_insn;

  // Declare signals as logic
  logic [`REG_SIZE] rd_data; // Data to write
  logic we; // Write enable
  logic [`REG_SIZE] rs1_data, rs2_data; // Data from source

  // Instantiate RegFile w/ instance name 'rf'
  RegFile rf (
    .rd(insn_rd),
    .rd_data(rd_data),
    .rs1(insn_rs1),
    .rs1_data(rs1_data),
    .rs2(insn_rs2),
    .rs2_data(rs2_data),
    .clk(clk),
    .we(we),
    .rst(rst)
  );

  // Declare signals for CLA adder
  logic [31:0] a, b, sum;
  logic cin;

  // Instantiate CLA adder
  cla adder (
    .a(a),
    .b(b),
    .cin(cin),
    .sum(sum)
  );

  always @(posedge clk) begin
    if (rst) begin
        pcCurrent <= 32'd0; // Reset condition
    end else begin
        pcCurrent <= pcNext; // Default next PC value
    end
  end

  logic [31:0] o_quotient, o_remainder;
  logic [31:0] i_dividend, i_divisor;

  divider_unsigned divider (
    .i_dividend(i_dividend),
    .i_divisor(i_divisor),
    .o_remainder(o_remainder),
    .o_quotient(o_quotient)
  );

  logic [31:0] abs_dividend, abs_divisor;
  logic neg_dividend, neg_divisor, neg_result;

  // if inputs negative
  always_comb begin
    neg_dividend = rs1_data[31];
    neg_divisor = rs2_data[31];

    // compute absolute values
    abs_dividend = neg_dividend ? (~rs1_data + 1) : rs1_data;
    abs_divisor = neg_divisor ? (~rs2_data + 1) : rs2_data;

    // if result should be negative
    neg_result = neg_dividend ^ neg_divisor;
  end

  logic [63:0] mul1_ext, mul2_ext; // 64-bit variables to store multiplication reuslt

  // unadjusted exact address
  logic [31:0] exact_addr_dmem;

  logic [`REG_SIZE] my_store_data_to_dmem_logic, my_addr_to_dmem_logic;
  logic [3:0] my_store_we_to_dmem_logic;

  assign store_data_to_dmem = my_store_data_to_dmem_logic;
  assign store_we_to_dmem = my_store_we_to_dmem_logic;
  assign addr_to_dmem = my_addr_to_dmem_logic;


  always_comb begin
    illegal_insn = 1'b0;

    // Default assignments
    we = 1'b0; 
    rd_data = 32'b0; 
    a = 32'b0;
    b = 32'b0;
    cin = 1'b0;
    pcNext = pcCurrent + 4;
    halt = 1'b0;
    i_dividend = rs1_data;
    i_divisor = rs2_data;
    my_store_data_to_dmem_logic = 32'b0;
    my_store_we_to_dmem_logic = 4'b0;
    my_addr_to_dmem_logic = 32'b0; 

    case (insn_opcode)
      OpLui: begin
        // TODO: start here by implementing lui
        rd_data = {insn_from_imem[31:12], 12'b0}; // Immediate is in top 20 bits
        we = 1'b1; // Enable writing
      end
      OpRegImm: begin
        if (insn_addi) begin
          // ADDI:
          a = rs1_data; // Src reg data
          b = imm_i_sext; // Sign-extended immediate
          rd_data = sum; // Result of addition
          we = 1'b1; // Enable write
        end else if (insn_slti) begin
          // SLTI:
          rd_data = $signed(rs1_data) < $signed(imm_i_sext) ? 32'd1 : 32'd0;
          we = 1'b1; // Enable write back to reg
        end else if (insn_sltiu) begin
          // SLTIU:
          rd_data = ($unsigned(rs1_data) < $unsigned(imm_i_sext)) ? 32'd1 : 32'd0;
          we = 1'b1; // Enable writing
        end else if (insn_xori) begin
          // XORI:
          rd_data = rs1_data ^ imm_i_sext; // Perform bitwise XOR
          we = 1'b1; // Enable write back to reg
        end else if (insn_ori) begin
          // ORI:
          rd_data = rs1_data | imm_i_sext; 
          we = 1'b1; // Enable write back to reg
        end else if (insn_andi) begin
          // ANDI:
          rd_data = rs1_data & imm_i_sext; // Perform bitwise AND
          we = 1'b1; // Enable writing to dest reg
        end else if (insn_slli) begin
          // SLLI:
          rd_data = rs1_data << imm_i[4:0]; // Shift left logical
          we = 1'b1; // Enable writing to dest reg
        end else if (insn_srli) begin
          // SRLI:
          rd_data = rs1_data >> imm_i[4:0]; // Shift rs1_data right
          we = 1'b1; // Enable write back to dest reg
        end else if (insn_srai) begin
          // SRAI:
          rd_data = $signed(rs1_data) >>> imm_i[4:0];
          we = 1'b1; // Enable writing to dest reg
        end else begin
          illegal_insn = 1'b1;
        end
      end
      OpRegReg: begin // This indicates R-type insn
        if (insn_add) begin
          // ADD:
          a = rs1_data; // Data from src reg 1
          b = rs2_data; // Data from src reg 2
          cin = 1'b0; // Carry-in for add
          // result stored in sum
          rd_data = sum;
          we = 1'b1; // Enable write back to reg
        end else if (insn_sub) begin
          // SUB:
          a = rs1_data; // Data from src reg 1
          b = rs2_data; // Data from src reg 2
          b = ~rs2_data; // Invert bits of 2nd operand for sub
          cin = 1'b1; // Carry-in for sub
          // result stored in sum
          rd_data = sum;
          we = 1'b1; // Enable write back to reg
        end else if (insn_mul) begin
          // MUL:
          rd_data = rs1_data * rs2_data;
          we = 1'b1;
        end else if (insn_and) begin
          // AND:
          rd_data = rs1_data & rs2_data; // Perform bitwise AND
          we = 1'b1; // Enable write back to reg
        end else if (insn_remu) begin
          // REMU:
          rd_data = o_remainder; // use remainder
          we = 1'b1;
        end else if (insn_sll) begin
          // SLL:
          rd_data = rs1_data << rs2_data[4:0]; // Shift left
          we = 1'b1; // Enable write back to dest reg
        end else if (insn_mulh) begin
          // MULH:
          mul1_ext = ($signed(rs1_data) * $signed(rs2_data));
          rd_data = mul1_ext[63:32];
          we = 1'b1;
        end else if (insn_slt) begin
          // SLT:
          rd_data = $signed(rs1_data) < $signed(rs2_data) ? 32'd1 : 32'd0;
          we = 1'b1; // Enable write back to dest reg
        end else if (insn_mulhsu) begin
          // MULHSU:
          mul2_ext = {{32{rs1_data[31]}}, rs1_data};
          mul1_ext = mul2_ext * {{32'b0}, rs2_data};
          //mul1_ext = ($signed(rs1_data) * $unsigned(rs2_data));
          rd_data = mul1_ext[63:32];
          we = 1'b1;
        end else if (insn_sltu) begin
          // SLTU:
          rd_data = ($unsigned(rs1_data) < $unsigned(rs2_data)) ? 32'd1 : 32'd0;
          we = 1'b1; // Enable write back to dest reg
        end else if (insn_mulhu) begin
          // MULHU:
          mul1_ext = ($unsigned(rs1_data) * $unsigned(rs2_data));
          rd_data = mul1_ext[63:32];
          we = 1'b1;
        end else if (insn_xor) begin
          // XOR:
          rd_data = rs1_data ^ rs2_data; // Perform bitwise XOR
          we = 1'b1; // Enable write back to dest reg
        end else if (insn_div) begin
          // DIV:
          if (rs2_data == 0) begin
            // division by zero, quotient all ones
            rd_data = {32{1'b1}}; // max value
          end else begin
            // normal division case
            i_dividend = abs_dividend;
            i_divisor = abs_divisor;
            // adjust sign for result
            rd_data = neg_result ? (~o_quotient + 1) : o_quotient;
          end
          we = 1'b1; // enable writing
        end else if (insn_srl) begin
          // SRL:
          rd_data = rs1_data >> rs2_data[4:0]; // Logical shift right
          we = 1'b1; // Enable write back to dest reg
        end else if (insn_sra) begin
          // SRA:
          rd_data = $signed(rs1_data) >>> rs2_data[4:0];
          we = 1'b1;
        end else if (insn_divu) begin
          // DIVU:
          rd_data = o_quotient; // use quotient
          we = 1'b1;
        end if (insn_or) begin
          // OR:
          rd_data = rs1_data | rs2_data;
          we = 1'b1; // Enable write back to dest reg
        end else if (insn_rem) begin
          // REM:
          i_dividend = abs_dividend;
          i_divisor = abs_divisor;
          // adjust sign
          rd_data = neg_dividend ? (~o_remainder + 1) : o_remainder;
          we = 1'b1;
        end else begin
          illegal_insn = 1'b1;
        end
      end
      OpBranch: begin
        if (insn_beq) begin
          // BEQ:
          if (rs1_data == rs2_data) begin
            pcNext = pcCurrent + imm_b_sext;
          end
        end else if (insn_bgeu) begin
          // BGEU:
          if ($unsigned(rs1_data) >= $unsigned(rs2_data)) begin
            pcNext = pcCurrent + imm_b_sext;
          end
        end else if (insn_bne) begin
          // BNE:
          if (rs1_data != rs2_data) begin
            pcNext = pcCurrent + imm_b_sext;
          end
        end else if (insn_blt) begin
          // BLT:
          if ($signed(rs1_data) < $signed(rs2_data)) begin
            pcNext = pcCurrent + imm_b_sext;
          end
        end else if (insn_bge) begin
          // BGE:
          if ($signed(rs1_data) >= $signed(rs2_data)) begin
            pcNext = pcCurrent + imm_b_sext;
          end
        end else if (insn_bltu) begin
          // BLTU:
          if ($unsigned(rs1_data) < $unsigned(rs2_data)) begin
            pcNext = pcCurrent + imm_b_sext;
          end
        end else begin 
          illegal_insn = 1'b1;
        end
      end
      OpEnviron: begin
        if (insn_ecall) begin
          // ECALL:
          halt = 1'b1; // Set halt to 1
        end else begin
          illegal_insn = 1'b1; // Mark as illegal
        end
      end
      OpMiscMem: begin
        if (insn_fence) begin
        end
      end
      OpJal: begin
        // JAL:
        rd_data = pcCurrent + 4; // save return address
        pcNext = pcCurrent + imm_j_sext;
        we = 1'b1; // write enable
      end
      OpJalr: begin
        // JALR:
        rd_data = pcCurrent + 4; // save return address
        pcNext = (rs1_data + imm_i_sext) & 32'hfffffffe;
        we = 1'b1; // write enable
      end
      OpAuipc: begin
        // AUPIC:
        rd_data = pcCurrent + {insn_from_imem[31:12], 12'b0};
        we = 1'b1; // enable writing
      end
      OpLoad: begin
        if (insn_lb) begin 
          // LB:
          exact_addr_dmem = rs1_data + imm_i_sext; // calculate address

          my_addr_to_dmem_logic = rs1_data + imm_i_sext;
          my_addr_to_dmem_logic[1:0] = 2'b00; // align address to 4B boundary

          // fetch 32-bit word
          case (exact_addr_dmem[1:0])
            2'b00: rd_data = {{24{load_data_from_dmem[7]}}, load_data_from_dmem[7:0]};
            2'b01: rd_data = {{24{load_data_from_dmem[15]}}, load_data_from_dmem[15:8]};
            2'b10: rd_data = {{24{load_data_from_dmem[23]}}, load_data_from_dmem[23:16]};
            2'b11: rd_data = {{24{load_data_from_dmem[31]}}, load_data_from_dmem[31:24]};
            default: illegal_insn = 1'b1; // misaligned
          endcase

          // enable writing back
          we = 1'b1;
        end else if (insn_lh) begin 
          // LH:
          exact_addr_dmem = rs1_data + imm_i_sext; // calculate address

          my_addr_to_dmem_logic = rs1_data + imm_i_sext;
          my_addr_to_dmem_logic[1:0] = 2'b00; // align address to 4B boundary

          // fetch 32-bit word
          case (exact_addr_dmem[1:0])
            2'b00: rd_data = {{16{load_data_from_dmem[15]}}, load_data_from_dmem[15:0]}; // lower half-word
            2'b10: rd_data = {{16{load_data_from_dmem[31]}}, load_data_from_dmem[31:16]}; // upper half-word
            default: illegal_insn = 1'b1; // misaligned
          endcase

          // enable writing back
          we = 1'b1;
        end else if (insn_lw) begin 
          // LW:
          exact_addr_dmem = rs1_data + imm_i_sext; // calculate address

          // check word alignment
          if (exact_addr_dmem[1:0] != 2'b00) begin
            illegal_insn = 1'b1; // misaligned
          end else begin
            my_addr_to_dmem_logic = rs1_data + imm_i_sext;
            rd_data = load_data_from_dmem; // directly write loaded data

            // enable writing back
            we = 1'b1;
          end
        end else if (insn_lbu) begin 
          // LBU:
          exact_addr_dmem = rs1_data + imm_i_sext; // calculate address

          my_addr_to_dmem_logic = rs1_data + imm_i_sext;
          my_addr_to_dmem_logic[1:0] = 2'b00; // align address to 4B boundary

          // fetch 32-bit word
          case(exact_addr_dmem[1:0])
            2'b00: rd_data = {24'b0, load_data_from_dmem[7:0]};
            2'b01: rd_data = {24'b0, load_data_from_dmem[15:8]};
            2'b10: rd_data = {24'b0, load_data_from_dmem[23:16]};
            2'b11: rd_data = {24'b0, load_data_from_dmem[31:24]};
            default: illegal_insn = 1'b1; // misaligned
          endcase

          // enable writing back
          we = 1'b1;
        end else if (insn_lhu) begin
          // LHU:
          exact_addr_dmem = rs1_data + imm_i_sext; // calculate address

          my_addr_to_dmem_logic = rs1_data + imm_i_sext;
          my_addr_to_dmem_logic[1:0] = 2'b00; // align address to 4B boundary

          // fetch 32-bit word
          case(exact_addr_dmem[1:0])
            2'b00: rd_data = {16'b0, load_data_from_dmem[15:0]};  // lower half-word
            2'b10: rd_data = {16'b0, load_data_from_dmem[31:16]}; // upper half-word
            default: illegal_insn = 1'b1; // misaligned
          endcase

          // enable writing back
          we = 1'b1;
        end else begin
          illegal_insn = 1'b1;
        end
      end
      OpStore: begin
        if (insn_sb) begin
          // SB:
          exact_addr_dmem = rs1_data + imm_s_sext; // calculate address
          
          // prepare store_data_to_dmem & align addr_to_dmem
          my_addr_to_dmem_logic = rs1_data + imm_s_sext;
          my_addr_to_dmem_logic[1:0] = 2'b00; // align address to 4B boundary
          
          // select byte & set corresponding byte enable bit
          case (exact_addr_dmem[1:0])
            2'b00: begin
              my_store_data_to_dmem_logic = {24'b0, rs2_data[7:0]}; // prepare byte 0
              my_store_we_to_dmem_logic = 4'b0001;
            end
            2'b01: begin
              my_store_data_to_dmem_logic = {16'b0, rs2_data[7:0], 8'b0}; // prepare byte 1
              my_store_we_to_dmem_logic = 4'b0010;
            end
            2'b10: begin
              my_store_data_to_dmem_logic = {8'b0, rs2_data[7:0], 16'b0}; // prepare byte 2
              my_store_we_to_dmem_logic = 4'b0100;
            end
            2'b11: begin
              my_store_data_to_dmem_logic = {rs2_data[7:0], 24'b0}; // prepare byte 3
              my_store_we_to_dmem_logic = 4'b1000;
            end
            default: illegal_insn = 1'b1; // should never happen
          endcase
        end else if (insn_sh) begin
          // SH:
          exact_addr_dmem = rs1_data + imm_s_sext; // calculate address
          
          // prepare store_data_to_dmem & align addr_to_dmem
          my_addr_to_dmem_logic = rs1_data + imm_s_sext;
          my_addr_to_dmem_logic[1:0] = 2'b00; // align address to 4B boundary
          
          // select half-word & set corresponding byte enable bit
          case (exact_addr_dmem[1:0])
            2'b00: begin
              my_store_data_to_dmem_logic = {16'b0, rs2_data[15:0]}; // lower half-word
              my_store_we_to_dmem_logic = 4'b0011; // enable writing
            end
            2'b10: begin
              my_store_data_to_dmem_logic = {rs2_data[15:0], 16'b0}; // upper half-word
              my_store_we_to_dmem_logic = 4'b1100; // enable writing
            end
            default: illegal_insn = 1'b1; // should never happen
          endcase
        end else if (insn_sw) begin
          // SW:
          exact_addr_dmem = rs1_data + imm_s_sext; // calculate address

          // check word alignment
          if (exact_addr_dmem[1:0] != 2'b00) begin
            // raise illegal instruction flag
            illegal_insn = 1'b1;
          end else begin
            my_addr_to_dmem_logic = rs1_data + imm_s_sext;
            // store entire word
            my_store_data_to_dmem_logic = rs2_data;
            // enable writing
            my_store_we_to_dmem_logic = 4'b1111;
          end
        end else begin
          illegal_insn = 1'b1;
        end
      end
      default: begin
        illegal_insn = 1'b1;
      end
    endcase
  end

endmodule

/* A memory module that supports 1-cycle reads and writes, with one read-only port
 * and one read+write port.
 */
module MemorySingleCycle #(
    parameter int NUM_WORDS = 512
) (
    // rst for both imem and dmem
    input wire rst,

    // clock for both imem and dmem. See RiscvProcessor for clock details.
    input wire clock_mem,

    // must always be aligned to a 4B boundary
    input wire [`REG_SIZE] pc_to_imem,

    // the value at memory location pc_to_imem
    output logic [`REG_SIZE] insn_from_imem,

    // must always be aligned to a 4B boundary
    input wire [`REG_SIZE] addr_to_dmem,

    // the value at memory location addr_to_dmem
    output logic [`REG_SIZE] load_data_from_dmem,

    // the value to be written to addr_to_dmem, controlled by store_we_to_dmem
    input wire [`REG_SIZE] store_data_to_dmem,

    // Each bit determines whether to write the corresponding byte of store_data_to_dmem to memory location addr_to_dmem.
    // E.g., 4'b1111 will write 4 bytes. 4'b0001 will write only the least-significant byte.
    input wire [3:0] store_we_to_dmem
);

  // memory is arranged as an array of 4B words
  logic [`REG_SIZE] mem[NUM_WORDS];

  initial begin
    $readmemh("mem_initial_contents.hex", mem, 0);
  end

  always_comb begin
    // memory addresses should always be 4B-aligned
    assert (pc_to_imem[1:0] == 2'b00);
    assert (addr_to_dmem[1:0] == 2'b00);
  end

  localparam int AddrMsb = $clog2(NUM_WORDS) + 1;
  localparam int AddrLsb = 2;

  always @(posedge clock_mem) begin
    if (rst) begin
    end else begin
      insn_from_imem <= mem[{pc_to_imem[AddrMsb:AddrLsb]}];
    end
  end

  always @(negedge clock_mem) begin
    if (rst) begin
    end else begin
      if (store_we_to_dmem[0]) begin
        mem[addr_to_dmem[AddrMsb:AddrLsb]][7:0] <= store_data_to_dmem[7:0];
      end
      if (store_we_to_dmem[1]) begin
        mem[addr_to_dmem[AddrMsb:AddrLsb]][15:8] <= store_data_to_dmem[15:8];
      end
      if (store_we_to_dmem[2]) begin
        mem[addr_to_dmem[AddrMsb:AddrLsb]][23:16] <= store_data_to_dmem[23:16];
      end
      if (store_we_to_dmem[3]) begin
        mem[addr_to_dmem[AddrMsb:AddrLsb]][31:24] <= store_data_to_dmem[31:24];
      end
      // dmem is "read-first": read returns value before the write
      load_data_from_dmem <= mem[{addr_to_dmem[AddrMsb:AddrLsb]}];
    end
  end
endmodule

/*
This shows the relationship between clock_proc and clock_mem. The clock_mem is
phase-shifted 90° from clock_proc. You could think of one proc cycle being
broken down into 3 parts. During part 1 (which starts @posedge clock_proc)
the current PC is sent to the imem. In part 2 (starting @posedge clock_mem) we
read from imem. In part 3 (starting @negedge clock_mem) we read/write memory and
prepare register/PC updates, which occur at @posedge clock_proc.

        ____
 proc: |    |______
           ____
 mem:  ___|    |___
*/
module RiscvProcessor (
    input  wire  clock_proc,
    input  wire  clock_mem,
    input  wire  rst,
    output logic halt
);

  wire [`REG_SIZE] pc_to_imem, insn_from_imem, mem_data_addr, mem_data_loaded_value, mem_data_to_write;
  wire [3:0] mem_data_we;

  MemorySingleCycle #(
      .NUM_WORDS(8192)
  ) mem (
      .rst      (rst),
      .clock_mem (clock_mem),
      // imem is read-only
      .pc_to_imem(pc_to_imem),
      .insn_from_imem(insn_from_imem),
      // dmem is read-write
      .addr_to_dmem(mem_data_addr),
      .load_data_from_dmem(mem_data_loaded_value),
      .store_data_to_dmem (mem_data_to_write),
      .store_we_to_dmem  (mem_data_we)
  );

  DatapathSingleCycle datapath (
      .clk(clock_proc),
      .rst(rst),
      .pc_to_imem(pc_to_imem),
      .insn_from_imem(insn_from_imem),
      .addr_to_dmem(mem_data_addr),
      .store_data_to_dmem(mem_data_to_write),
      .store_we_to_dmem(mem_data_we),
      .load_data_from_dmem(mem_data_loaded_value),
      .halt(halt)
  );

endmodule
