`timescale 1ns / 1ns

// registers are 32 bits in RV32
`define REG_SIZE 31:0

// insns are 32 bits in RV32IM
`define INSN_SIZE 31:0

// RV opcodes are 7 bits
`define OPCODE_SIZE 6:0

`ifndef RISCV_FORMAL
`include "../hw2b/cla.sv"
`include "../hw3-singlecycle/RvDisassembler.sv"
`include "../hw4-multicycle/divider_unsigned_pipelined.sv"
`endif

module Disasm #(
    byte PREFIX = "D"
) (
    input wire [31:0] insn,
    output wire [(8*32)-1:0] disasm
);
  // synthesis translate_off
  // this code is only for simulation, not synthesis
  string disasm_string;
  always_comb begin
    disasm_string = rv_disasm(insn);
  end
  // HACK: get disasm_string to appear in GtkWave, which can apparently show only wire/logic. Also,
  // string needs to be reversed to render correctly.
  genvar i;
  for (i = 3; i < 32; i = i + 1) begin : gen_disasm
    assign disasm[((i+1-3)*8)-1-:8] = disasm_string[31-i];
  end
  assign disasm[255-:8] = PREFIX;
  assign disasm[247-:8] = ":";
  assign disasm[239-:8] = " ";
  // synthesis translate_on
endmodule

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
  genvar i;
  logic [`REG_SIZE] regs[NumRegs];

  // TODO: your code here
  always_ff @(posedge clk or posedge rst) begin
    if (rst) begin
      // reset all regs
      for (int i = 0; i < NumRegs; i++) begin
        regs[i] <= 0;
      end
    end else if (we && rd != 0) begin
      // write data to rd
      regs[rd] <= rd_data;
    end
  end

  // reading data and implementing wd bypass
  always_comb begin
    // wd bypass rs1
    if (we && rd == rs1) begin
      rs1_data = rd_data;
    end else begin
      rs1_data = (rs1 == 0) ? 0 : regs[rs1];
    end

    // wd bypass rs2
    if (we && rd == rs2) begin
      rs2_data = rd_data;
    end else begin
      rs2_data = (rs2 == 0) ? 0 : regs[rs2];
    end
  end
endmodule

/**
 * This enum is used to classify each cycle as it comes through the Writeback stage, identifying
 * if a valid insn is present or, if it is a stall cycle instead, the reason for the stall. The
 * enum values are mutually exclusive: only one should be set for any given cycle. These values
 * are compared against the trace-*.json files to ensure that the datapath is running with the
 * correct timing.
 *
 * You will need to set these values at various places within your pipeline, and propagate them
 * through the stages until they reach Writeback where they can be checked.
 */
typedef enum {
  /** invalid value, this should never appear after the initial reset sequence completes */
  CYCLE_INVALID = 0,
  /** a stall cycle that arose from the initial reset signal */
  CYCLE_RESET = 1,
  /** not a stall cycle, a valid insn is in Writeback */
  CYCLE_NO_STALL = 2,
  /** a stall cycle that arose from a taken branch/jump */
  CYCLE_TAKEN_BRANCH = 4,

  // the values below are only needed in HW5B

  /** a stall cycle that arose from a load-to-use stall */
  CYCLE_LOAD2USE = 8,
  /** a stall cycle that arose from a div/rem-to-use stall */
  CYCLE_DIV2USE = 16,
  /** a stall cycle that arose from a fence.i insn */
  CYCLE_FENCEI = 32
} cycle_status_e;

/** state at the start of Decode stage */
typedef struct packed {
  logic [`REG_SIZE] pc;
  logic [`INSN_SIZE] insn;
  cycle_status_e cycle_status;
} stage_decode_t;

/** state at the start of Execute stage */
typedef struct packed {
  logic [`REG_SIZE] pc;
  logic [`INSN_SIZE] insn;
  cycle_status_e cycle_status;
  logic [`OPCODE_SIZE] insn_opcode;
  logic [`REG_SIZE] rs1_data;
  logic [`REG_SIZE] rs2_data;
  logic [4:0] insn_rs1;
  logic [4:0] insn_rs2;
  logic [11:0] imm;
  logic [`REG_SIZE] imm_i_sext;
  logic [`REG_SIZE] imm_b_sext;
  logic [`REG_SIZE] imm_j_sext;
  logic [6:0] insn_funct7;
  logic [2:0] insn_funct3;
  logic [4:0] insn_rd;
  logic [`REG_SIZE] b_rs1_data;
  logic [`REG_SIZE] b_rs2_data;
  logic u_b_rs1_data;
  logic u_b_rs2_data;
} stage_execute_t;

/** state at the start of Memory stage */
typedef struct packed {
  logic [`REG_SIZE] pc;
  logic [`INSN_SIZE] insn;
  cycle_status_e cycle_status;
  logic [`REG_SIZE] rd_data;
  logic [4:0] insn_rd;
  logic we; 
} stage_memory_t;

/** state at the start of Writeback stage */
typedef struct packed {
  logic [`REG_SIZE] pc;
  logic [`INSN_SIZE] insn;
  cycle_status_e cycle_status;
  logic [`REG_SIZE] rd_data;
  logic [4:0] insn_rd;
  logic we; 
} stage_writeback_t;

module DatapathPipelined (
    input wire clk,
    input wire rst,
    output logic [`REG_SIZE] pc_to_imem,
    input wire [`INSN_SIZE] insn_from_imem,
    // dmem is read/write
    output logic [`REG_SIZE] addr_to_dmem,
    input wire [`REG_SIZE] load_data_from_dmem,
    output logic [`REG_SIZE] store_data_to_dmem,
    output logic [3:0] store_we_to_dmem,

    output logic halt,

    // The PC of the insn currently in Writeback. 0 if not a valid insn.
    output logic [`REG_SIZE] trace_writeback_pc,
    // The bits of the insn currently in Writeback. 0 if not a valid insn.
    output logic [`INSN_SIZE] trace_writeback_insn,
    // The status of the insn (or stall) currently in Writeback. See cycle_status_e enum for valid values.
    output cycle_status_e trace_writeback_cycle_status
);

  // opcodes - see section 19 of RiscV spec
  localparam bit [`OPCODE_SIZE] OpcodeLoad = 7'b00_000_11;
  localparam bit [`OPCODE_SIZE] OpcodeStore = 7'b01_000_11;
  localparam bit [`OPCODE_SIZE] OpcodeBranch = 7'b11_000_11;
  localparam bit [`OPCODE_SIZE] OpcodeJalr = 7'b11_001_11;
  localparam bit [`OPCODE_SIZE] OpcodeMiscMem = 7'b00_011_11;
  localparam bit [`OPCODE_SIZE] OpcodeJal = 7'b11_011_11;

  localparam bit [`OPCODE_SIZE] OpcodeRegImm = 7'b00_100_11;
  localparam bit [`OPCODE_SIZE] OpcodeRegReg = 7'b01_100_11;
  localparam bit [`OPCODE_SIZE] OpcodeEnviron = 7'b11_100_11;

  localparam bit [`OPCODE_SIZE] OpcodeAuipc = 7'b00_101_11;
  localparam bit [`OPCODE_SIZE] OpcodeLui = 7'b01_101_11;

  // cycle counter, not really part of any stage but useful for orienting within GtkWave
  // do not rename this as the testbench uses this value
  logic [`REG_SIZE] cycles_current;
  always_ff @(posedge clk) begin
    if (rst) begin
      cycles_current <= 0;
    end else begin
      cycles_current <= cycles_current + 1;
    end
  end

  /***************/
  /* FETCH STAGE */
  /***************/

  logic [`REG_SIZE] f_pc_current;
  wire [`REG_SIZE] f_insn;
  cycle_status_e f_cycle_status;

  // signal to indicate flush due to taken branch
  logic branch_taken;
  logic [`REG_SIZE] branch_target;

  // program counter
  always_ff @(posedge clk) begin
    if (rst) begin
      f_pc_current <= 32'd0;
      // NB: use CYCLE_NO_STALL since this is the value that will persist after the last reset cycle
      f_cycle_status <= CYCLE_NO_STALL;
    end else if (branch_taken) begin
      f_pc_current <= branch_target; // set pc
      f_cycle_status <= CYCLE_TAKEN_BRANCH;
    end else begin
      f_cycle_status <= CYCLE_NO_STALL;
      f_pc_current <= f_pc_current + 4;
    end
  end
  // send PC to imem
  assign pc_to_imem = f_pc_current;
  assign f_insn = insn_from_imem;

  // Here's how to disassemble an insn into a string you can view in GtkWave.
  // Use PREFIX to provide a 1-character tag to identify which stage the insn comes from.
  Disasm #(
      .PREFIX("F")
  ) disasm_0fetch (
      .insn  (f_insn),
      .disasm()
  );

  /****************/
  /* DECODE STAGE */
  /****************/

  // this shows how to package up state in a `struct packed`, and how to pass it between stages
  stage_decode_t decode_state;
  always_ff @(posedge clk) begin
    if (rst) begin
      decode_state <= '{
        pc: 0,
        insn: 0,
        cycle_status: CYCLE_RESET
      };
    end else if (branch_taken) begin
      decode_state <= '{
        pc: 0,
        insn: 0,
        cycle_status: CYCLE_TAKEN_BRANCH
      };
    end else begin
      begin
        decode_state <= '{
          pc: f_pc_current,
          insn: f_insn,
          cycle_status: f_cycle_status
        };
      end
    end
  end
  Disasm #(
      .PREFIX("D")
  ) disasm_1decode (
      .insn  (decode_state.insn),
      .disasm()
  );

  // TODO: your code here, though you will also need to modify some of the code above
  // TODO: the testbench requires that your register file instance is named `rf`
  wire [6:0] insn_funct7;
  wire [4:0] insn_rs2;
  wire [4:0] insn_rs1;
  wire [2:0] insn_funct3;
  wire [4:0] insn_rd;
  wire [`OPCODE_SIZE] insn_opcode;

  // split R-type instruction - see section 2.2 of RiscV spec
  assign {insn_funct7, insn_rs2, insn_rs1, insn_funct3, insn_rd, insn_opcode} = decode_state.insn;

  // setup for I, B & J type instructions
  // I - short immediates and loads
  wire [11:0] imm_i;
  assign imm_i = decode_state.insn[31:20];
  wire [ 4:0] imm_shamt = decode_state.insn[24:20];

  // B - conditionals
  wire [12:0] imm_b;
  assign {imm_b[12], imm_b[10:5]} = insn_funct7, {imm_b[4:1], imm_b[11]} = insn_rd, imm_b[0] = 1'b0;

  // J - unconditional jumps
  wire [20:0] imm_j;
  assign {imm_j[20], imm_j[10:1], imm_j[11], imm_j[19:12], imm_j[0]} = {decode_state.insn[31:12], 1'b0};

  wire [`REG_SIZE] imm_i_sext = {{20{imm_i[11]}}, imm_i[11:0]};
  wire [`REG_SIZE] imm_b_sext = {{19{imm_b[12]}}, imm_b[12:0]};
  wire [`REG_SIZE] imm_j_sext = {{11{imm_j[20]}}, imm_j[20:0]};

  // Declare signals as logic
  logic [`REG_SIZE] rd_data; // Data to write
  logic we; // Write enable
  logic [`REG_SIZE] rs1_data, rs2_data; // Data from source
  logic [4:0] wb_insn_rd;

  // Instantiate RegFile w/ instance name 'rf'
  RegFile rf (
    .rd(wb_insn_rd),
    .rd_data(rd_data),
    .rs1(insn_rs1),
    .rs1_data(rs1_data),
    .rs2(insn_rs2),
    .rs2_data(rs2_data),
    .clk(clk),
    .we(we),
    .rst(rst)
  );

  logic [`REG_SIZE] d_b_rs1_data; 
  logic [`REG_SIZE] d_b_rs2_data; 
  logic d_u_b_rs1_data; 
  logic d_u_b_rs2_data; 

  always_comb begin
    // default not using bypass values
    d_b_rs1_data = 0;
    d_b_rs2_data = 0;
    d_u_b_rs1_data = 0;
    d_u_b_rs2_data = 0;

    // wx bypass logic
    if (memory_state.we) begin
      if (insn_rs1 == memory_state.insn_rd) begin
        d_b_rs1_data = memory_state.rd_data;
        d_u_b_rs1_data = 1;
      end
      if (insn_rs2 == memory_state.insn_rd) begin
        d_b_rs2_data = memory_state.rd_data;
        d_u_b_rs2_data = 1;
      end
    end
  end

  /*****************/
  /* EXECUTE STAGE */
  /*****************/

  // package up state
  stage_execute_t execute_state;
  always_ff @(posedge clk) begin
    if (rst) begin
      execute_state <= '{
        pc: 0,
        insn: 0,
        cycle_status: CYCLE_RESET,
        insn_opcode: 0,
        insn_rs1: 0,
        insn_rs2: 0,
        rs1_data: 0,
        rs2_data: 0,
        imm: 0,
        imm_i_sext: 0,
        imm_b_sext: 0,
        imm_j_sext: 0,
        insn_funct7: 0,
        insn_funct3: 0,
        insn_rd: 0,
        b_rs1_data: 0,
        b_rs2_data: 0,
        u_b_rs1_data: 0,
        u_b_rs2_data: 0
      };
    end else begin
      begin
        execute_state <= '{
          pc: decode_state.pc,
          insn: decode_state.insn,
          cycle_status: decode_state.cycle_status,
          insn_opcode: insn_opcode,
          insn_rs1: insn_rs1,
          insn_rs2: insn_rs2,
          rs1_data: rs1_data,
          rs2_data: rs2_data,
          imm: imm_i,
          imm_i_sext: imm_i_sext,
          imm_b_sext: imm_b_sext,
          imm_j_sext: imm_j_sext,
          insn_funct7: insn_funct7,
          insn_funct3: insn_funct3,
          insn_rd: insn_rd,
          b_rs1_data: d_b_rs1_data,
          b_rs2_data: d_b_rs2_data,
          u_b_rs1_data: d_u_b_rs1_data,
          u_b_rs2_data: d_u_b_rs2_data
        };
      end
    end
  end

  logic illegal_insn;

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

  // Declare signals as logic
  logic [`REG_SIZE] e_rd_data; // Data to write
  logic e_we; // Write enable

  logic [`REG_SIZE] e_rs1_data, e_rs2_data;

  // bypass logic
  always_comb begin
    // default original register data
    e_rs1_data = execute_state.rs1_data;
    e_rs2_data = execute_state.rs2_data;

    // check mx bypass conditions directly
    if (memory_state.we) begin
      // mx bypass rs1
      if (execute_state.insn_rs1 == memory_state.insn_rd) begin
        e_rs1_data = memory_state.rd_data;
      end
      // mx bypass rs2
      if (execute_state.insn_rs2 == memory_state.insn_rd) begin
        e_rs2_data = memory_state.rd_data;
      end
    end

    // wx logic
    if (execute_state.u_b_rs1_data) begin
      e_rs1_data = execute_state.b_rs1_data;
    end
    if (execute_state.u_b_rs2_data) begin
      e_rs2_data = execute_state.b_rs2_data;
    end
  end

  always_comb begin
    illegal_insn = 1'b0;

    // Default assignments
    e_we = 1'b0;
    e_rd_data = 32'b0;
    a = 32'b0;
    b = 32'b0;
    cin = 1'b0;
    branch_taken = 1'b0;
    branch_target = execute_state.pc + 4;
    
    case (execute_state.insn_opcode)
      OpcodeLui: begin
        // TODO: start here by implementing lui
        e_rd_data = {execute_state.insn[31:12], 12'b0}; // Immediate is in top 20 bits
        e_we = 1'b1; // Enable writing
      end
      OpcodeRegImm: begin
        if (execute_state.insn_funct3 == 3'b000) begin
          // ADDI:
          a = e_rs1_data; // Src reg data
          b = execute_state.imm_i_sext; // Sign-extended immediate
          e_rd_data = sum; // Result of addition
          e_we = 1'b1; // Enable write
        end else if (execute_state.insn_funct3 == 3'b010) begin
          // SLTI:
          e_rd_data = $signed(e_rs1_data) < $signed(execute_state.imm_i_sext) ? 32'd1 : 32'd0;
          e_we = 1'b1; // Enable write back to reg
        end else if (execute_state.insn_funct3 == 3'b011) begin
          // SLTIU:
          e_rd_data = ($unsigned(e_rs1_data) < $unsigned(execute_state.imm_i_sext)) ? 32'd1 : 32'd0;
          e_we = 1'b1; // Enable writing
        end else if (execute_state.insn_funct3 == 3'b100) begin
          // XORI:
          e_rd_data = e_rs1_data ^ execute_state.imm_i_sext; // Perform bitwise XOR
          e_we = 1'b1; // Enable write back to reg
        end else if (execute_state.insn_funct3 == 3'b110) begin
          // ORI:
          e_rd_data = e_rs1_data | execute_state.imm_i_sext; 
          e_we = 1'b1; // Enable write back to reg
        end else if (execute_state.insn_funct3 == 3'b111) begin
          // ANDI:
          e_rd_data = e_rs1_data & execute_state.imm_i_sext; // Perform bitwise AND
          e_we = 1'b1; // Enable writing to dest reg
        end else if (execute_state.insn_funct3 == 3'b001 && execute_state.insn_funct7 == 7'd0) begin
          // SLLI:
          e_rd_data = e_rs1_data << execute_state.imm[4:0]; // Shift left logical
          e_we = 1'b1; // Enable writing to dest reg
        end else if (execute_state.insn_funct3 == 3'b101 && execute_state.insn_funct7 == 7'd0) begin
          // SRLI:
          e_rd_data = e_rs1_data >> execute_state.imm[4:0]; // Shift rs1_data right
          e_we = 1'b1; // Enable write back to dest reg
        end else if (execute_state.insn_funct3 == 3'b101 && execute_state.insn_funct7 == 7'b0100000) begin
          // SRAI:
          e_rd_data = $signed(e_rs1_data) >>> execute_state.imm[4:0];
          e_we = 1'b1; // Enable writing to dest reg
        end else begin
          illegal_insn = 1'b1;
        end
      end
      OpcodeRegReg: begin // This indicates R-type insn
        if (execute_state.insn_funct3 == 3'b000 && execute_state.insn_funct7 == 7'd0) begin
          // ADD:
          a = e_rs1_data; // Data from src reg 1
          b = e_rs2_data; // Data from src reg 2
          cin = 1'b0; // Carry-in for add
          // result stored in sum
          e_rd_data = sum;
          e_we = 1'b1; // Enable write back to reg
        end else if (execute_state.insn_funct3 == 3'b000 && execute_state.insn_funct7 == 7'b0100000) begin
          // SUB:
          a = e_rs1_data; // Data from src reg 1
          b = e_rs2_data; // Data from src reg 2
          b = ~e_rs2_data; // Invert bits of 2nd operand for sub
          cin = 1'b1; // Carry-in for sub
          // result stored in sum
          e_rd_data = sum;
          e_we = 1'b1; // Enable write back to reg
        end else if (execute_state.insn_funct3 == 3'b111 && execute_state.insn_funct7 == 7'd0) begin
          // AND:
          e_rd_data = e_rs1_data & e_rs2_data; // Perform bitwise AND
          e_we = 1'b1; // Enable write back to reg
        end else if (execute_state.insn_funct3 == 3'b001 && execute_state.insn_funct7 == 7'd0) begin
          // SLL:
          e_rd_data = e_rs1_data << e_rs2_data[4:0]; // Shift left
          e_we = 1'b1; // Enable write back to dest reg
        end else if (execute_state.insn_funct3 == 3'b010 && execute_state.insn_funct7 == 7'd0) begin
          // SLT:
          e_rd_data = $signed(e_rs1_data) < $signed(e_rs2_data) ? 32'd1 : 32'd0;
          e_we = 1'b1; // Enable write back to dest reg
        end else if (execute_state.insn_funct3 == 3'b011 && execute_state.insn_funct7 == 7'd0) begin
          // SLTU:
          e_rd_data = ($unsigned(e_rs1_data) < $unsigned(e_rs2_data)) ? 32'd1 : 32'd0;
          e_we = 1'b1; // Enable write back to dest reg
        end else if (execute_state.insn_funct3 == 3'b100 && execute_state.insn_funct7 == 7'd0) begin
          // XOR:
          e_rd_data = e_rs1_data ^ e_rs2_data; // Perform bitwise XOR
          e_we = 1'b1; // Enable write back to dest reg
        end else if (execute_state.insn_funct3 == 3'b101 && execute_state.insn_funct7 == 7'd0) begin
          // SRL:
          e_rd_data = e_rs1_data >> e_rs2_data[4:0]; // Logical shift right
          e_we = 1'b1; // Enable write back to dest reg
        end else if (execute_state.insn_funct3 == 3'b101 && execute_state.insn_funct7 == 7'b0100000) begin
          // SRA:
          e_rd_data = $signed(e_rs1_data) >>> e_rs2_data[4:0];
          e_we = 1'b1;
        end else if (execute_state.insn_funct3 == 3'b110 && execute_state.insn_funct7 == 7'd0) begin
          // OR:
          e_rd_data = e_rs1_data | e_rs2_data;
          e_we = 1'b1; // Enable write back to dest reg
        end else begin
          illegal_insn = 1'b1;
        end
      end
      OpcodeBranch: begin
        if (execute_state.insn_funct3 == 3'b000) begin
          // BEQ:
          if (e_rs1_data == e_rs2_data) begin
            branch_target = execute_state.pc + execute_state.imm_b_sext;
            branch_taken = 1'b1;
          end
        end else if (execute_state.insn_funct3 == 3'b111) begin
          // BGEU:
          if ($unsigned(e_rs1_data) >= $unsigned(e_rs2_data)) begin
            branch_target = execute_state.pc + execute_state.imm_b_sext;
            branch_taken = 1'b1;
          end
        end else if (execute_state.insn_funct3 == 3'b001) begin
          // BNE:
          if (e_rs1_data != e_rs2_data) begin
            branch_target = execute_state.pc + execute_state.imm_b_sext;
            branch_taken = 1'b1;
          end
        end else if (execute_state.insn_funct3 == 3'b100) begin
          // BLT:
          if ($signed(e_rs1_data) < $signed(e_rs2_data)) begin
            branch_target = execute_state.pc + execute_state.imm_b_sext;
            branch_taken = 1'b1;
          end
        end else if (execute_state.insn_funct3 == 3'b101) begin
          // BGE:
          if ($signed(e_rs1_data) >= $signed(e_rs2_data)) begin
            branch_target = execute_state.pc + execute_state.imm_b_sext;
            branch_taken = 1'b1;
          end
        end else if (execute_state.insn_funct3 == 3'b110) begin
          // BLTU:
          if ($unsigned(e_rs1_data) < $unsigned(e_rs2_data)) begin
            branch_target = execute_state.pc + execute_state.imm_b_sext;
            branch_taken = 1'b1;
          end
        end else begin 
          illegal_insn = 1'b1;
        end
      end
      OpcodeJal: begin
        // JAL:
        e_rd_data = execute_state.pc + 4; // save return address
        branch_target = execute_state.pc + execute_state.imm_j_sext;
        branch_taken = 1'b1;
        e_we = 1'b1; // write enable
      end
      default: begin
        illegal_insn = 1'b1;
      end
    endcase
  end

  /*******************/
  /* MEMORY STAGE */
  /*******************/

  // package up state
  stage_memory_t memory_state;
  always_ff @(posedge clk) begin
    if (rst) begin
      memory_state <= '{
        pc: 0,
        insn: 0,
        cycle_status: CYCLE_RESET,
        rd_data: 0,
        insn_rd: 0,
        we: 0
      };
    end else begin
      begin
        memory_state <= '{
          pc: execute_state.pc,
          insn: execute_state.insn,
          cycle_status: execute_state.cycle_status,
          rd_data: e_rd_data,
          insn_rd: execute_state.insn_rd,
          we: e_we
        };
      end
    end
  end

  /*******************/
  /* WRITEBACK STAGE */
  /*******************/

  // package up state
  stage_writeback_t writeback_state;
  always_ff @(posedge clk) begin
    if (rst) begin
      writeback_state <= '{
        pc: 0,
        insn: 0,
        cycle_status: CYCLE_RESET,
        rd_data: 0,
        insn_rd: 0,
        we: 0
      };
    end else begin
      begin
        writeback_state <= '{
          pc: memory_state.pc,
          insn: memory_state.insn,
          cycle_status: memory_state.cycle_status,
          rd_data: memory_state.rd_data,
          insn_rd: memory_state.insn_rd,
          we: memory_state.we
        };
      end
    end
  end

  assign wb_insn_rd = writeback_state.insn_rd;
  assign rd_data = writeback_state.rd_data;
  assign we = writeback_state.we; // signal triggers actual write
endmodule

module MemorySingleCycle #(
    parameter int NUM_WORDS = 512
) (
    // rst for both imem and dmem
    input wire rst,

    // clock for both imem and dmem. The memory reads/writes on @(negedge clk)
    input wire clk,

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

  always @(negedge clk) begin
    if (rst) begin
    end else begin
      insn_from_imem <= mem[{pc_to_imem[AddrMsb:AddrLsb]}];
    end
  end

  always @(negedge clk) begin
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

/* This design has just one clock for both processor and memory. */
module RiscvProcessor (
    input  wire  clk,
    input  wire  rst,
    output logic halt,
    output wire [`REG_SIZE] trace_writeback_pc,
    output wire [`INSN_SIZE] trace_writeback_insn,
    output cycle_status_e trace_writeback_cycle_status
);

  wire [`INSN_SIZE] insn_from_imem;
  wire [`REG_SIZE] pc_to_imem, mem_data_addr, mem_data_loaded_value, mem_data_to_write;
  wire [3:0] mem_data_we;

  MemorySingleCycle #(
      .NUM_WORDS(8192)
  ) mem (
      .rst                (rst),
      .clk                (clk),
      // imem is read-only
      .pc_to_imem         (pc_to_imem),
      .insn_from_imem     (insn_from_imem),
      // dmem is read-write
      .addr_to_dmem       (mem_data_addr),
      .load_data_from_dmem(mem_data_loaded_value),
      .store_data_to_dmem (mem_data_to_write),
      .store_we_to_dmem   (mem_data_we)
  );

  DatapathPipelined datapath (
      .clk(clk),
      .rst(rst),
      .pc_to_imem(pc_to_imem),
      .insn_from_imem(insn_from_imem),
      .addr_to_dmem(mem_data_addr),
      .store_data_to_dmem(mem_data_to_write),
      .store_we_to_dmem(mem_data_we),
      .load_data_from_dmem(mem_data_loaded_value),
      .halt(halt),
      .trace_writeback_pc(trace_writeback_pc),
      .trace_writeback_insn(trace_writeback_insn),
      .trace_writeback_cycle_status(trace_writeback_cycle_status)
  );

endmodule
