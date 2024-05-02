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
  // TODO: copy your RegFile code here
  localparam int NumRegs = 32;
  // genvar i;
  logic [`REG_SIZE] regs[NumRegs];

  // TODO: your code here
  assign rs1_data = regs[rs1];
  assign rs2_data = regs[rs2];

  always_ff @(posedge clk) begin
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
endmodule

/** NB: ARESETn is active-low, i.e., reset when this input is ZERO */
interface axi_clkrst_if (
    input wire ACLK,
    input wire ARESETn
);
endinterface

interface axi_if #(
      parameter int ADDR_WIDTH = 32
    , parameter int DATA_WIDTH = 32
);
  logic                      ARVALID;
  logic                      ARREADY;
  logic [    ADDR_WIDTH-1:0] ARADDR;
  logic [               2:0] ARPROT;

  logic                      RVALID;
  logic                      RREADY;
  logic [    DATA_WIDTH-1:0] RDATA;
  logic [               1:0] RRESP;

  logic                      AWVALID;
  logic                      AWREADY;
  logic [    ADDR_WIDTH-1:0] AWADDR;
  logic [               2:0] AWPROT;

  logic                      WVALID;
  logic                      WREADY;
  logic [    DATA_WIDTH-1:0] WDATA;
  logic [(DATA_WIDTH/8)-1:0] WSTRB;

  logic                      BVALID;
  logic                      BREADY;
  logic [               1:0] BRESP;

  modport manager(
      input ARREADY, RVALID, RDATA, RRESP, AWREADY, WREADY, BVALID, BRESP,
      output ARVALID, ARADDR, ARPROT, RREADY, AWVALID, AWADDR, AWPROT, WVALID, WDATA, WSTRB, BREADY
  );
  modport subord(
      input ARVALID, ARADDR, ARPROT, RREADY, AWVALID, AWADDR, AWPROT, WVALID, WDATA, WSTRB, BREADY,
      output ARREADY, RVALID, RDATA, RRESP, AWREADY, WREADY, BVALID, BRESP
  );
endinterface

module MemoryAxiLite #(
    parameter int NUM_WORDS  = 32,
    parameter int ADDR_WIDTH = 32,
    parameter int DATA_WIDTH = 32
) (
    axi_clkrst_if axi,
    axi_if.subord insn,
    axi_if.subord data
);

  // memory is an array of 4B words
  logic [DATA_WIDTH-1:0] mem_array[NUM_WORDS];
  localparam int AddrMsb = $clog2(NUM_WORDS) + 1;
  localparam int AddrLsb = 2;

  // [BR]RESP codes, from Section A 3.4.4 of AXI4 spec
  localparam bit [1:0] ResponseOkay = 2'b00;
  // localparam bit [1:0] ResponseSubordinateError = 2'b10;
  // localparam bit [1:0] ResponseDecodeError = 2'b11;

`ifndef FORMAL
  always_comb begin
    // memory addresses should always be 4B-aligned
    assert (!insn.ARVALID || insn.ARADDR[1:0] == 2'b00);
    assert (!data.ARVALID || data.ARADDR[1:0] == 2'b00);
    assert (!data.AWVALID || data.AWADDR[1:0] == 2'b00);
    // we don't use the protection bits
    assert (insn.ARPROT == 3'd0);
    assert (data.ARPROT == 3'd0);
    assert (data.AWPROT == 3'd0);
    assert(ADDR_WIDTH == 32);
  end
`endif

  // TODO: changes will be needed throughout this module

  // Assume always ready for simplicity based on system assumptions
  assign insn.ARREADY = 1'b1;
  assign data.ARREADY = 1'b1;
  assign data.AWREADY = 1'b1;
  assign data.WREADY = 1'b1;

  always_ff @(posedge axi.ACLK) begin
    if (!axi.ARESETn) begin
      // Synchronous active low reset
      insn.RVALID <= 1'b0;
      data.RVALID <= 1'b0;
      data.BVALID <= 1'b0;
      insn.RDATA <= 0;
    end else begin
      // Handle instruction read request
      if (insn.ARVALID) begin
        insn.RDATA <= mem_array[insn.ARADDR[AddrMsb:AddrLsb]];
        insn.RRESP <= ResponseOkay;
        insn.RVALID <= 1'b1;
      end else begin
        insn.RVALID <= 1'b0;
      end

      // Handle data read request
      if (data.ARVALID) begin
        data.RDATA <= mem_array[data.ARADDR[AddrMsb:AddrLsb]];
        data.RRESP <= ResponseOkay;
        data.RVALID <= 1'b1;
      end else begin
        data.RVALID <= 1'b0;
      end

      // Handle data write request
      if (data.AWVALID && data.WVALID) begin
        mem_array[data.AWADDR[AddrMsb:AddrLsb]] <= data.WDATA;
        data.BRESP <= ResponseOkay;
        data.BVALID <= 1'b1;
      end else begin
        data.BVALID <= 1'b0;
      end
    end
  end

endmodule

/** This is used for testing MemoryAxiLite in simulation, since Verilator doesn't allow
SV interfaces in top-level modules. We expose all of the AXIL signals here so that tests
can interact with them. */
module MemAxiLiteTester #(
    parameter int NUM_WORDS  = 32,
    parameter int ADDR_WIDTH = 32,
    parameter int DATA_WIDTH = 32
) (
    input wire ACLK,
    input wire ARESETn,

    input  wire                   I_ARVALID,
    output logic                  I_ARREADY,
    input  wire  [ADDR_WIDTH-1:0] I_ARADDR,
    input  wire  [           2:0] I_ARPROT,
    output logic                  I_RVALID,
    input  wire                   I_RREADY,
    output logic [ADDR_WIDTH-1:0] I_RDATA,
    output logic [           1:0] I_RRESP,

    input  wire                       I_AWVALID,
    output logic                      I_AWREADY,
    input  wire  [    ADDR_WIDTH-1:0] I_AWADDR,
    input  wire  [               2:0] I_AWPROT,
    input  wire                       I_WVALID,
    output logic                      I_WREADY,
    input  wire  [    DATA_WIDTH-1:0] I_WDATA,
    input  wire  [(DATA_WIDTH/8)-1:0] I_WSTRB,
    output logic                      I_BVALID,
    input  wire                       I_BREADY,
    output logic [               1:0] I_BRESP,

    input  wire                   D_ARVALID,
    output logic                  D_ARREADY,
    input  wire  [ADDR_WIDTH-1:0] D_ARADDR,
    input  wire  [           2:0] D_ARPROT,
    output logic                  D_RVALID,
    input  wire                   D_RREADY,
    output logic [ADDR_WIDTH-1:0] D_RDATA,
    output logic [           1:0] D_RRESP,

    input  wire                       D_AWVALID,
    output logic                      D_AWREADY,
    input  wire  [    ADDR_WIDTH-1:0] D_AWADDR,
    input  wire  [               2:0] D_AWPROT,
    input  wire                       D_WVALID,
    output logic                      D_WREADY,
    input  wire  [    DATA_WIDTH-1:0] D_WDATA,
    input  wire  [(DATA_WIDTH/8)-1:0] D_WSTRB,
    output logic                      D_BVALID,
    input  wire                       D_BREADY,
    output logic [               1:0] D_BRESP
);

  axi_clkrst_if axi (.*);
  axi_if #(
      .ADDR_WIDTH(ADDR_WIDTH),
      .DATA_WIDTH(DATA_WIDTH)
  ) insn ();
  assign insn.manager.ARVALID = I_ARVALID;
  assign I_ARREADY = insn.manager.ARREADY;
  assign insn.manager.ARADDR = I_ARADDR;
  assign insn.manager.ARPROT = I_ARPROT;
  assign I_RVALID = insn.manager.RVALID;
  assign insn.manager.RREADY = I_RREADY;
  assign I_RRESP = insn.manager.RRESP;
  assign I_RDATA = insn.manager.RDATA;

  axi_if #(
      .ADDR_WIDTH(ADDR_WIDTH),
      .DATA_WIDTH(DATA_WIDTH)
  ) data ();
  assign data.manager.ARVALID = D_ARVALID;
  assign D_ARREADY = data.manager.ARREADY;
  assign data.manager.ARADDR = D_ARADDR;
  assign data.manager.ARPROT = D_ARPROT;
  assign D_RVALID = data.manager.RVALID;
  assign data.manager.RREADY = D_RREADY;
  assign D_RRESP = data.manager.RRESP;
  assign D_RDATA = data.manager.RDATA;

  assign data.manager.AWVALID = D_AWVALID;
  assign D_AWREADY = data.manager.AWREADY;
  assign data.manager.AWADDR = D_AWADDR;
  assign data.manager.AWPROT = D_AWPROT;
  assign data.manager.WVALID = D_WVALID;
  assign D_WREADY = data.manager.WREADY;
  assign data.manager.WDATA = D_WDATA;
  assign data.manager.WSTRB = D_WSTRB;
  assign D_BVALID = data.manager.BVALID;
  assign data.manager.BREADY = D_BREADY;
  assign D_BRESP = data.manager.BRESP;

  MemoryAxiLite #(
      .NUM_WORDS(NUM_WORDS)
  ) mem (
      .axi (axi),
      .insn(insn.subord),
      .data(data.subord)
  );
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
  /** a stall cycle that arose from a load-to-use stall */
  CYCLE_LOAD2USE = 8,
  /** a stall cycle that arose from a div/rem-to-use stall */
  CYCLE_DIV2USE = 16,
  /** a stall cycle that arose from a fence insn */
  CYCLE_FENCE = 32
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
  logic [4:0] insn_rs1;
  logic [4:0] insn_rs2;
  logic [4:0] insn_rd;
  logic [`REG_SIZE] rs1_data;
  logic [`REG_SIZE] rs2_data;
  logic [`REG_SIZE] imm_i_sext;
  logic [`REG_SIZE] imm_b_sext;
  logic [`REG_SIZE] imm_j_sext;
  logic [`REG_SIZE] imm_s_sext;
} stage_execute_t;

/** state at the start of Memory stage */
typedef struct packed {
  logic [`REG_SIZE] pc;
  logic [`INSN_SIZE] insn;
  cycle_status_e cycle_status;
  logic [`OPCODE_SIZE] insn_opcode;
  logic [4:0] insn_rs1;
  logic [4:0] insn_rs2;
  logic [4:0] insn_rd;
  logic [`REG_SIZE] rs1_data;
  logic [`REG_SIZE] rs2_data;
  logic [`REG_SIZE] rd_data;
  logic we;
  logic halt;
  logic [`REG_SIZE] my_addr_to_dmem_logic;
  logic load;
  logic store;
  logic div;
  logic [2:0] load_type;
  logic [2:0] store_type;
  logic [2:0] div_type;
} stage_memory_t;

/** state at the start of Writeback stage */
typedef struct packed {
  logic [`REG_SIZE] pc;
  logic [`INSN_SIZE] insn;
  cycle_status_e cycle_status;
  logic [`OPCODE_SIZE] insn_opcode;
  logic [4:0] insn_rd;
  logic [`REG_SIZE] rd_data;
  logic we;
  logic halt;
  logic [`REG_SIZE] my_araddr_logic;
  logic [`REG_SIZE] my_awaddr_logic;
  logic load;
  logic store;
  logic div;
  logic [2:0] load_type;
  logic [2:0] store_type;
  logic [`REG_SIZE] rs2_data;
} stage_writeback_t;

module DatapathAxilMemory (
    input wire clk,
    input wire rst,

    // Start by replacing this interface to imem...
    // output logic [`REG_SIZE] pc_to_imem,
    // input wire [`INSN_SIZE] insn_from_imem,
    // ...with this AXIL one.
    axi_if.manager imem,

    // Once imem is working, replace this interface to dmem...
    // output logic [`REG_SIZE] addr_to_dmem,
    // input wire [`REG_SIZE] load_data_from_dmem,
    // output logic [`REG_SIZE] store_data_to_dmem,
    // output logic [3:0] store_we_to_dmem,
    // ...with this AXIL one
    axi_if.manager dmem,

    output logic halt,

    // The PC of the insn currently in Writeback. 0 if not a valid insn.
    output logic [`REG_SIZE] trace_writeback_pc,
    // The bits of the insn currently in Writeback. 0 if not a valid insn.
    output logic [`INSN_SIZE] trace_writeback_insn,
    // The status of the insn (or stall) currently in Writeback. See cycle_status_e enum for valid values.
    output cycle_status_e trace_writeback_cycle_status
);

  // TODO: your code here
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
  // wire [`REG_SIZE] f_insn;
  cycle_status_e f_cycle_status;

  // signals to indicate stalls
  logic taken_branch;
  logic [`REG_SIZE] branch_taken;
  logic load2use;
  logic div2use;
  logic fencei;

  // program counter
  always_ff @(posedge clk) begin
    if (rst) begin
      f_pc_current <= 32'd0;
      // NB: use CYCLE_NO_STALL since this is the value that will persist after the last reset cycle
      f_cycle_status <= CYCLE_NO_STALL;
    end else if (taken_branch) begin
      f_cycle_status <= CYCLE_NO_STALL;
      f_pc_current <= branch_taken;
    end else if (load2use) begin
      f_cycle_status <= CYCLE_NO_STALL;
      f_pc_current <= f_pc_current;
    end else if (div2use) begin
      f_cycle_status <= CYCLE_NO_STALL;
      f_pc_current <= f_pc_current;
    end else if (fencei) begin 
      f_cycle_status <= CYCLE_NO_STALL;
      f_pc_current <= f_pc_current;
    end else begin
      f_cycle_status <= CYCLE_NO_STALL;
      f_pc_current <= f_pc_current + 4;
    end
  end

  // Setup AXI read address channel
  assign imem.ARVALID = 1'b1;
  assign imem.ARADDR = f_pc_current;
  assign imem.ARPROT = 3'b00;

  // Ready signal to accept the instruction
  assign imem.RREADY = 1'b1;  // Always ready to accept data

  // send PC to imem
  // assign pc_to_imem = f_pc_current;
  // assign f_insn = insn_from_imem;

  // Here's how to disassemble an insn into a string you can view in GtkWave.
  // Use PREFIX to provide a 1-character tag to identify which stage the insn comes from.
  wire [255:0] f_disasm;
  Disasm #(
      .PREFIX("F")
  ) disasm_0fetch (
      .insn  (0),
      .disasm(f_disasm)
  );

  /****************/
  /* DECODE STAGE */
  /****************/
  wire [`REG_SIZE] d_insn;

  // Signals to indicate stalls
  logic d_taken_branch;
  logic d_load2use;
  logic [`REG_SIZE] d_prev_insn;
  logic fence;
  logic d_div2use;

  // this shows how to package up state in a `struct packed`, and how to pass it between stages
  stage_decode_t decode_state;
  always_ff @(posedge clk) begin
    d_taken_branch <= 1'b0;
    d_load2use <= 1'b0;
    d_prev_insn <= d_insn;
    fence <= 1'b0;
    d_div2use <= 1'b0;
    if (rst) begin
      decode_state <= '{
        pc: 0,
        insn: 0,
        cycle_status: CYCLE_RESET
      };
      d_prev_insn <= 0;
    end else if (taken_branch) begin
      decode_state <= '{
        pc: 0,
        insn: 0,
        cycle_status: CYCLE_TAKEN_BRANCH
      };
      d_taken_branch <= 1'b1;
    end else if (load2use || div2use) begin
      // maintain current state
      decode_state <= decode_state;
      d_load2use <= 1'b1;
    end else if (fencei) begin
      decode_state <= decode_state;
      fence <= 1'b1;
    end else if (div2use) begin
      decode_state <= decode_state;
      d_div2use <= 1'b1;
    end else begin
        begin
          decode_state <= '{
            pc: f_pc_current,
            insn: imem.RDATA,
            cycle_status: f_cycle_status
          };
        end
    end
  end

  assign d_insn = d_taken_branch ? 0 : (d_load2use ? d_prev_insn : (fence ? d_prev_insn : (d_div2use ? d_prev_insn : imem.RDATA)));

  wire [255:0] d_disasm;
  Disasm #(
      .PREFIX("D")
  ) disasm_1decode (
      .insn  (imem.RDATA),
      .disasm(d_disasm)
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
  assign {insn_funct7, insn_rs2, insn_rs1, insn_funct3, insn_rd, insn_opcode} = d_insn;

  // setup for I, S, B & J type instructions
  // I - short immediates and loads
  wire [11:0] imm_i;
  assign imm_i = d_insn[31:20];
  wire [ 4:0] imm_shamt = d_insn[24:20];

  // S - stores
  wire [11:0] imm_s;
  assign imm_s[11:5] = insn_funct7, imm_s[4:0] = insn_rd;

  // B - conditionals
  wire [12:0] imm_b;
  assign {imm_b[12], imm_b[10:5]} = insn_funct7, {imm_b[4:1], imm_b[11]} = insn_rd, imm_b[0] = 1'b0;

  // J - unconditional jumps
  wire [20:0] imm_j;
  assign {imm_j[20], imm_j[10:1], imm_j[11], imm_j[19:12], imm_j[0]} = {d_insn[31:12], 1'b0};

  wire [`REG_SIZE] imm_i_sext = {{20{imm_i[11]}}, imm_i[11:0]};
  wire [`REG_SIZE] imm_s_sext = {{20{imm_s[11]}}, imm_s[11:0]};
  wire [`REG_SIZE] imm_b_sext = {{19{imm_b[12]}}, imm_b[12:0]};
  wire [`REG_SIZE] imm_j_sext = {{11{imm_j[20]}}, imm_j[20:0]};

  // declare signals logic for regfile
  logic [`REG_SIZE] rs1_data, rs2_data, rd_data;
  logic we;
  logic [4:0] w_insn_rd;

  // instantiate regfile
  RegFile rf (
    .rd(w_insn_rd),
    .rd_data(rd_data),
    .rs1(insn_rs1),
    .rs1_data(rs1_data),
    .rs2(insn_rs2),
    .rs2_data(rs2_data),
    .clk(clk),
    .we(we),
    .rst(rst)
  );

  // implementing wd bypass 
  logic [`REG_SIZE] d_rs1_data, d_rs2_data;
  always_comb begin
    // wd bypass rs1
    if (insn_rs1 == writeback_state.insn_rd && insn_rs1 != 0 && 
        writeback_state.insn_opcode != OpcodeBranch && writeback_state.insn_opcode != OpcodeStore) begin
      d_rs1_data = writeback_state.rd_data;
    end else begin
      d_rs1_data = rs1_data;
    end

    // wd bypass rs2
    if (insn_rs2 == writeback_state.insn_rd && insn_rs2 != 0 && 
        writeback_state.insn_opcode != OpcodeBranch && writeback_state.insn_opcode != OpcodeStore) begin
      d_rs2_data = writeback_state.rd_data;
    end else begin
      d_rs2_data = rs2_data;
    end
  end

  // load2use depedency
  always_comb begin
    if (execute_state.insn_opcode == OpcodeLoad && 
        ((insn_rs1 != 0 && execute_state.insn_rd == insn_rs1) || 
        (insn_rs2 == execute_state.insn_rd && insn_rs2 != 0 && insn_opcode != OpcodeLoad && insn_opcode != OpcodeStore && insn_opcode != OpcodeRegImm))) begin
      load2use = 1;
    end else begin
      load2use = 0;
    end
  end

  // div2use dependency
  always_comb begin
    if ((insn_div || insn_divu || insn_rem || insn_remu) && 
        ((insn_rs1 == execute_state.insn_rd && insn_rs1 != 0) || 
        (insn_rs2 == execute_state.insn_rd && insn_rs2 != 0 && insn_opcode != OpcodeRegImm))) begin
      div2use = 1;
    end else begin
      div2use = 0;
    end
  end

  // fencei dependency
  always_comb begin 
    if (insn_opcode == OpcodeMiscMem && 
        (execute_state.insn_opcode == OpcodeStore || memory_state.insn_opcode == OpcodeStore)) begin 
      fencei = 1;
    end else begin 
      fencei = 0;
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
        insn_rd : 0,
        rs1_data: 0,
        rs2_data: 0,
        imm_i_sext: 0,
        imm_b_sext: 0,
        imm_j_sext: 0,
        imm_s_sext: 0
      };
    end else if (taken_branch) begin
      execute_state <= '{
        pc: 0,
        insn: 0,
        cycle_status: CYCLE_TAKEN_BRANCH,
        insn_opcode: 0,
        insn_rs1: 0,  
        insn_rs2: 0,
        insn_rd : 0,
        rs1_data: 0,
        rs2_data: 0,
        imm_i_sext: 0,
        imm_b_sext: 0,
        imm_j_sext: 0,
        imm_s_sext: 0
      };
    end else if (load2use) begin
      execute_state <= '{
        pc: 0,
        insn: 0,
        cycle_status: CYCLE_LOAD2USE,
        insn_opcode: 0,
        insn_rs1: 0,  
        insn_rs2: 0,
        insn_rd : 0,
        rs1_data: 0,
        rs2_data: 0,
        imm_i_sext: 0,
        imm_b_sext: 0,
        imm_j_sext: 0,
        imm_s_sext: 0
      };
    end else if (div2use) begin
      execute_state <= '{
        pc: 0,
        insn: 0,
        cycle_status: CYCLE_DIV2USE,
        insn_opcode: 0,
        insn_rs1: 0,  
        insn_rs2: 0,
        insn_rd : 0,
        rs1_data: 0,
        rs2_data: 0,
        imm_i_sext: 0,
        imm_b_sext: 0,
        imm_j_sext: 0,
        imm_s_sext: 0
      };
    end else if (fencei) begin
      execute_state <= '{
        pc: 0,
        insn: 0,
        cycle_status: CYCLE_FENCE,
        insn_opcode: 0,
        insn_rs1: 0,  
        insn_rs2: 0,
        insn_rd : 0,
        rs1_data: 0,
        rs2_data: 0,
        imm_i_sext: 0,
        imm_b_sext: 0,
        imm_j_sext: 0,
        imm_s_sext: 0
      };
    end else begin
      execute_state <= '{
        pc: decode_state.pc,
        insn: d_insn,
        cycle_status: decode_state.cycle_status,
        insn_opcode: insn_opcode,
        insn_rs1: insn_rs1,
        insn_rs2: insn_rs2,
        insn_rd: insn_rd,
        rs1_data: d_rs1_data,
        rs2_data: d_rs2_data,
        imm_i_sext: imm_i_sext,
        imm_b_sext: imm_b_sext,
        imm_j_sext: imm_j_sext,
        imm_s_sext: imm_s_sext
      };
    end
  end

  wire insn_beq = execute_state.insn_opcode == OpcodeBranch && execute_state.insn[14:12] == 3'b000;
  wire insn_bne = execute_state.insn_opcode == OpcodeBranch && execute_state.insn[14:12] == 3'b001;
  wire insn_blt = execute_state.insn_opcode == OpcodeBranch && execute_state.insn[14:12] == 3'b100;
  wire insn_bge = execute_state.insn_opcode == OpcodeBranch && execute_state.insn[14:12] == 3'b101;
  wire insn_bltu = execute_state.insn_opcode == OpcodeBranch && execute_state.insn[14:12] == 3'b110;
  wire insn_bgeu = execute_state.insn_opcode == OpcodeBranch && execute_state.insn[14:12] == 3'b111;

  wire insn_lb = execute_state.insn_opcode == OpcodeLoad && execute_state.insn[14:12] == 3'b000;
  wire insn_lh = execute_state.insn_opcode == OpcodeLoad && execute_state.insn[14:12] == 3'b001;
  wire insn_lw = execute_state.insn_opcode == OpcodeLoad && execute_state.insn[14:12] == 3'b010;
  wire insn_lbu = execute_state.insn_opcode == OpcodeLoad && execute_state.insn[14:12] == 3'b100;
  wire insn_lhu = execute_state.insn_opcode == OpcodeLoad && execute_state.insn[14:12] == 3'b101;

  wire insn_sb = execute_state.insn_opcode == OpcodeStore && execute_state.insn[14:12] == 3'b000;
  wire insn_sh = execute_state.insn_opcode == OpcodeStore && execute_state.insn[14:12] == 3'b001;
  wire insn_sw = execute_state.insn_opcode == OpcodeStore && execute_state.insn[14:12] == 3'b010;

  wire insn_addi = execute_state.insn_opcode == OpcodeRegImm && execute_state.insn[14:12] == 3'b000;
  wire insn_slti = execute_state.insn_opcode == OpcodeRegImm && execute_state.insn[14:12] == 3'b010;
  wire insn_sltiu = execute_state.insn_opcode == OpcodeRegImm && execute_state.insn[14:12] == 3'b011;
  wire insn_xori = execute_state.insn_opcode == OpcodeRegImm && execute_state.insn[14:12] == 3'b100;
  wire insn_ori = execute_state.insn_opcode == OpcodeRegImm && execute_state.insn[14:12] == 3'b110;
  wire insn_andi = execute_state.insn_opcode == OpcodeRegImm && execute_state.insn[14:12] == 3'b111;

  wire insn_slli = execute_state.insn_opcode == OpcodeRegImm && execute_state.insn[14:12] == 3'b001 && execute_state.insn[31:25] == 7'd0;
  wire insn_srli = execute_state.insn_opcode == OpcodeRegImm && execute_state.insn[14:12] == 3'b101 && execute_state.insn[31:25] == 7'd0;
  wire insn_srai = execute_state.insn_opcode == OpcodeRegImm && execute_state.insn[14:12] == 3'b101 && execute_state.insn[31:25] == 7'b0100000;

  wire insn_add = execute_state.insn_opcode == OpcodeRegReg && execute_state.insn[14:12] == 3'b000 && execute_state.insn[31:25] == 7'd0;
  wire insn_sub  = execute_state.insn_opcode == OpcodeRegReg && execute_state.insn[14:12] == 3'b000 && execute_state.insn[31:25] == 7'b0100000;
  wire insn_sll = execute_state.insn_opcode == OpcodeRegReg && execute_state.insn[14:12] == 3'b001 && execute_state.insn[31:25] == 7'd0;
  wire insn_slt = execute_state.insn_opcode == OpcodeRegReg && execute_state.insn[14:12] == 3'b010 && execute_state.insn[31:25] == 7'd0;
  wire insn_sltu = execute_state.insn_opcode == OpcodeRegReg && execute_state.insn[14:12] == 3'b011 && execute_state.insn[31:25] == 7'd0;
  wire insn_xor = execute_state.insn_opcode == OpcodeRegReg && execute_state.insn[14:12] == 3'b100 && execute_state.insn[31:25] == 7'd0;
  wire insn_srl = execute_state.insn_opcode == OpcodeRegReg && execute_state.insn[14:12] == 3'b101 && execute_state.insn[31:25] == 7'd0;
  wire insn_sra  = execute_state.insn_opcode == OpcodeRegReg && execute_state.insn[14:12] == 3'b101 && execute_state.insn[31:25] == 7'b0100000;
  wire insn_or = execute_state.insn_opcode == OpcodeRegReg && execute_state.insn[14:12] == 3'b110 && execute_state.insn[31:25] == 7'd0;
  wire insn_and = execute_state.insn_opcode == OpcodeRegReg && execute_state.insn[14:12] == 3'b111 && execute_state.insn[31:25] == 7'd0;

  wire insn_mul    = execute_state.insn_opcode == OpcodeRegReg && execute_state.insn[31:25] == 7'd1 && execute_state.insn[14:12] == 3'b000;
  wire insn_mulh   = execute_state.insn_opcode == OpcodeRegReg && execute_state.insn[31:25] == 7'd1 && execute_state.insn[14:12] == 3'b001;
  wire insn_mulhsu = execute_state.insn_opcode == OpcodeRegReg && execute_state.insn[31:25] == 7'd1 && execute_state.insn[14:12] == 3'b010;
  wire insn_mulhu  = execute_state.insn_opcode == OpcodeRegReg && execute_state.insn[31:25] == 7'd1 && execute_state.insn[14:12] == 3'b011;
  wire insn_div    = execute_state.insn_opcode == OpcodeRegReg && execute_state.insn[31:25] == 7'd1 && execute_state.insn[14:12] == 3'b100;
  wire insn_divu   = execute_state.insn_opcode == OpcodeRegReg && execute_state.insn[31:25] == 7'd1 && execute_state.insn[14:12] == 3'b101;
  wire insn_rem    = execute_state.insn_opcode == OpcodeRegReg && execute_state.insn[31:25] == 7'd1 && execute_state.insn[14:12] == 3'b110;
  wire insn_remu   = execute_state.insn_opcode == OpcodeRegReg && execute_state.insn[31:25] == 7'd1 && execute_state.insn[14:12] == 3'b111;

  wire insn_ecall = execute_state.insn_opcode == OpcodeEnviron && execute_state.insn[31:7] == 25'd0;

  // bypass logic
  logic [`REG_SIZE] x_rs1_data, x_rs2_data;
  always_comb begin
    // mx bypass rs1
    if (execute_state.insn_rs1 == memory_state.insn_rd && execute_state.insn_rs1 != 0 && 
        memory_state.insn_opcode != OpcodeBranch && memory_state.insn_opcode != OpcodeStore) begin
      x_rs1_data = m_rd_data;
    // check wx bypass conditions directly rs1
    end else if (execute_state.insn_rs1 == writeback_state.insn_rd && execute_state.insn_rs1 != 0 && 
        writeback_state.insn_opcode != OpcodeBranch && writeback_state.insn_opcode != OpcodeStore) begin
      x_rs1_data = rd_data;
    end else begin
      x_rs1_data = execute_state.rs1_data;
    end

    // mx bypass rs2
    if (execute_state.insn_rs2 == memory_state.insn_rd && execute_state.insn_rs2 != 0 &&
        memory_state.insn_opcode != OpcodeBranch && memory_state.insn_opcode != OpcodeStore) begin
      x_rs2_data = m_rd_data;
    // check wx bypass conditions directly rs2
    end else if (execute_state.insn_rs2 == writeback_state.insn_rd && execute_state.insn_rs2 != 0 &&
        writeback_state.insn_opcode != OpcodeBranch && writeback_state.insn_opcode != OpcodeStore) begin
      x_rs2_data = rd_data;
    end else begin
      x_rs2_data = execute_state.rs2_data;
    end
  end

  logic illegal_insn;

  // declare signals for cla adder
  logic [`REG_SIZE] sum, imm_sum, difference;

  // instantiate cla adders
  cla adder (
    .a(x_rs1_data),
    .b(x_rs2_data),
    .cin(1'b0),
    .sum(sum)
  );
  cla imm_adder (
    .a(x_rs1_data),
    .b(execute_state.imm_i_sext),
    .cin(1'b0),
    .sum(imm_sum)
  );
  cla subtractor (
    .a({x_rs1_data}),
    .b(~{x_rs2_data} + 1),
    .cin(1'b0),
    .sum(difference)
  );

  // declare signals for divider unsigned pipelined
  logic [`REG_SIZE] i_dividend, i_divisor, o_quotient, o_remainder;

  divider_unsigned_pipelined divider (
    .i_dividend(i_dividend),
    .i_divisor(i_divisor),
    .o_remainder(o_remainder),
    .o_quotient(o_quotient),
    .clk(clk),
    .rst(rst)
  );

  // declare signals logic
  logic [`REG_SIZE] x_rd_data, x_addr_to_dmem_logic, x_w_addr;
  logic x_we, x_halt, load, store, div;
  logic [2:0] load_type, store_type, div_type;

  always_comb begin
    // default assignments
    illegal_insn = 1'b0;
    taken_branch = 1'b0;
    branch_taken = 32'b0;
    i_dividend = 32'b0;
    i_divisor = 32'b0;
    x_rd_data = 32'b0;
    x_addr_to_dmem_logic = 0;
    x_we = 1'b0;
    x_halt = 1'b0;
    load = 1'b0;
    store = 1'b0;
    div = 1'b0;
    load_type = 3'b000;
    store_type = 3'b000;
    div_type = 3'b000;
    x_w_addr = 0;

    case (execute_state.insn_opcode)
      OpcodeLui: begin
        // LUI:
        x_rd_data = {{execute_state.insn[31:12]}, 12'b0};
        x_we = 1'b1;
      end
      OpcodeRegImm: begin
        if (insn_addi) begin
          // ADDI:
          x_rd_data = imm_sum;
          x_we = 1'b1;
        end else if (insn_slti) begin
          // SLTI:
          x_rd_data = $signed(x_rs1_data) < $signed(execute_state.imm_i_sext) ? 1 : 0;
          x_we = 1'b1;
        end else if (insn_sltiu) begin
          // SLTIU:
          x_rd_data = x_rs1_data < execute_state.imm_i_sext ? 1 : 0;
          x_we = 1'b1;
        end else if (insn_xori) begin
          // XORI:
          x_rd_data = x_rs1_data ^ execute_state.imm_i_sext;
          x_we = 1'b1;
        end else if (insn_ori) begin
          // ORI:
          x_rd_data = x_rs1_data | execute_state.imm_i_sext;
          x_we = 1'b1;
        end else if (insn_andi) begin
          // ANDI:
          x_rd_data = x_rs1_data & execute_state.imm_i_sext;
          x_we = 1'b1;
        end else if (insn_slli) begin
          // SLLI:
          x_rd_data = x_rs1_data << execute_state.imm_i_sext[4:0];
          x_we = 1'b1;
        end else if (insn_srli) begin
          // SRLI:
          x_rd_data = x_rs1_data >> execute_state.imm_i_sext[4:0];
          x_we = 1'b1;
        end else if (insn_srai) begin
          // SRAI:
          x_rd_data = $signed(x_rs1_data) >>> execute_state.imm_i_sext[4:0];
          x_we = 1'b1;
        end else begin
          illegal_insn = 1'b1;
        end
      end
      OpcodeRegReg: begin
        if (insn_add) begin
          // ADD:
          x_rd_data = sum;
          x_we = 1'b1;
        end else if (insn_sub) begin
          // SUB:
          x_rd_data = difference;
          x_we = 1'b1;
        end else if (insn_and) begin
          // AND:
          x_rd_data = x_rs1_data & x_rs2_data;
          x_we = 1'b1;
        end else if (insn_sll) begin
          // SLL:
          x_rd_data = x_rs1_data << x_rs2_data[4:0];
          x_we = 1'b1;
        end else if (insn_slt) begin
          // SLT:
          x_rd_data = ($signed(x_rs1_data) < $signed(x_rs2_data) ? 1 : 0);
          x_we = 1'b1;
        end else if (insn_sltu) begin
          // SLTU:
          x_rd_data = (x_rs1_data < x_rs2_data ? 1 : 0);
          x_we = 1'b1;
        end else if (insn_xor) begin
          // XOR:
          x_rd_data = x_rs1_data ^ x_rs2_data;
          x_we = 1'b1;
        end else if (insn_srl) begin
          // SRL:
          x_rd_data = x_rs1_data >> x_rs2_data[4:0];
          x_we = 1'b1;
        end else if (insn_sra) begin
          // SRA:
          x_rd_data = $signed(x_rs1_data) >>> x_rs2_data[4:0];
          x_we = 1'b1;
        end else if (insn_or) begin
          // OR:
          x_rd_data = x_rs1_data | x_rs2_data;
          x_we = 1'b1;
        end else if (insn_div) begin
          // DIV:
          i_dividend = x_rs1_data[31] ? ~x_rs1_data + 1 : x_rs1_data;
          i_divisor = x_rs2_data[31] ? ~x_rs2_data + 1 : x_rs2_data;
          x_we = 1'b1;
          div = 1'b1;
          div_type = 3'b001;
        end else if (insn_divu) begin
          // DIVU:
          i_dividend = x_rs1_data;
          i_divisor = x_rs2_data;
          x_we = 1'b1;
          div = 1'b1;
          div_type = 3'b010;
        end else if (insn_rem) begin
          // REM:
          i_dividend = x_rs1_data[31] ? ~x_rs1_data + 1 : x_rs1_data;
          i_divisor = x_rs2_data[31] ? ~x_rs2_data + 1 : x_rs2_data;
          x_we = 1'b1;
          div = 1'b1;
          div_type = 3'b011;
        end else if (insn_remu) begin
          // REMU:
          i_dividend = x_rs1_data;
          i_divisor = x_rs2_data;
          x_we = 1'b1;
          div = 1'b1;
          div_type = 3'b100;
        end else if (insn_mul) begin 
          // MUL:
          x_rd_data = (x_rs1_data * x_rs2_data);
          x_we = 1'b1;
        end else if (insn_mulh) begin
          // MULH:
          x_rd_data = 32'({{{32{x_rs1_data[31]}}, x_rs1_data} * {{32{x_rs2_data[31]}}, x_rs2_data}} >> 32);
          x_we = 1'b1;
        end else if (insn_mulhsu) begin
          // MULHSU:
          x_rd_data = 32'({{{32{x_rs1_data[31]}}, x_rs1_data} * {32'b0, x_rs2_data}} >> 32);
          x_we = 1'b1;
        end else if (insn_mulhu) begin
          // MULHU:
          x_rd_data = 32'({{32'b0, x_rs1_data} * {32'b0, x_rs2_data}} >> 32);
          x_we = 1'b1;
        end else begin
          illegal_insn = 1'b1;
        end
      end
      OpcodeBranch: begin
        if (insn_beq) begin
          // BEQ:
          if (x_rs1_data == x_rs2_data) begin
            taken_branch = 1'b1;
            branch_taken = execute_state.pc + execute_state.imm_b_sext;
          end
        end else if (insn_bgeu) begin
          // BGEU:
          if (x_rs1_data >= x_rs2_data) begin
            taken_branch = 1'b1;
            branch_taken = execute_state.pc + execute_state.imm_b_sext;
          end
        end else if (insn_bne) begin
          // BNE:
          if (x_rs1_data != x_rs2_data) begin
            taken_branch = 1'b1;
            branch_taken = execute_state.pc + execute_state.imm_b_sext;
          end
        end else if (insn_blt) begin
          // BLT:
          if ($signed(x_rs1_data) < $signed(x_rs2_data)) begin
            taken_branch = 1'b1;
            branch_taken = execute_state.pc + execute_state.imm_b_sext;
          end
        end else if (insn_bge) begin
          // BGE:
          if ($signed(x_rs1_data) >= $signed(x_rs2_data)) begin
            taken_branch = 1'b1;
            branch_taken = execute_state.pc + execute_state.imm_b_sext;
          end
        end else if (insn_bltu) begin
          // BLTU:
          if (x_rs1_data < x_rs2_data) begin
            taken_branch = 1'b1;
            branch_taken = execute_state.pc + execute_state.imm_b_sext;
          end
        end else begin
          illegal_insn = 1'b1;
        end
      end
      OpcodeEnviron: begin
        if (insn_ecall) begin
          // ECALL:
          x_halt = 1'b1;
        end
      end
      OpcodeJal: begin
        // JAL:
        taken_branch = 1'b1;
        assert (execute_state.imm_j_sext[1:0] == 2'b00);
        branch_taken = execute_state.pc + execute_state.imm_j_sext;
        x_rd_data = execute_state.pc + 4;
        x_we = 1'b1;
      end
      OpcodeJalr: begin
        // JALR:
        taken_branch = 1'b1;
        branch_taken = (x_rs1_data + execute_state.imm_i_sext) & ~32'd1;
        x_rd_data = execute_state.pc + 4;
        x_we = 1'b1;
      end
      OpcodeAuipc: begin 
        // AUIPC:
        x_rd_data = execute_state.pc + {execute_state.insn[31:12], 12'b0};
        x_we = 1'b1;
      end
      OpcodeLoad: begin
        x_addr_to_dmem_logic = x_rs1_data + execute_state.imm_i_sext;
        x_we = 1'b1;
        load = 1'b1;
        if (insn_lb) begin
          // LB:
          load_type = 3'b001;
        end else if (insn_lh) begin
          // LH:
          load_type = 3'b010;
        end else if (insn_lw) begin
          // LW:
          load_type = 3'b011;
        end else if (insn_lbu) begin
          // LBU:
          load_type = 3'b100;
        end else if (insn_lhu) begin
          // LHU
          load_type = 3'b101;
        end else begin
          illegal_insn = 1'b1;
        end
      end
      OpcodeStore: begin
        x_w_addr = x_rs1_data + execute_state.imm_s_sext;
        store = 1'b1;
        if (insn_sb) begin
          // SB:
          store_type = 3'b001;
        end else if (insn_sh) begin
          // SH:
          store_type = 3'b010;
        end else if (insn_sw) begin
          // SW:
          store_type = 3'b011;
        end else begin
          illegal_insn = 1'b1;
        end
      end
      default: begin
        illegal_insn = 1'b1;
      end
    endcase
  end

  /****************/
  /* MEMORY STAGE */
  /****************/
  logic [`REG_SIZE] m_addr_to_dmem;
  logic [`REG_SIZE] w_addr;

  // package up state
  stage_memory_t memory_state;
  always_ff @(posedge clk) begin
    if (rst) begin
      memory_state <= '{
        pc: 0,
        insn: 0,
        cycle_status: CYCLE_RESET,
        insn_opcode: 0,
        insn_rs1: 0,
        insn_rs2: 0,
        insn_rd: 0,
        rs1_data: 0,
        rs2_data: 0,
        rd_data: 0,
        we: 0,
        halt: 0,
        my_addr_to_dmem_logic: 0,
        load: 0,
        store: 0,
        div: 0,
        load_type: 0,
        store_type: 0,
        div_type: 0
      };
      m_addr_to_dmem <= 0;
      w_addr <= 0;
    end else begin
      begin
        memory_state <= '{
          pc: execute_state.pc,
          insn: execute_state.insn,
          cycle_status: execute_state.cycle_status,
          insn_opcode: execute_state.insn_opcode,
          insn_rs1: execute_state.insn_rs1,
          insn_rs2: execute_state.insn_rs2,
          insn_rd: execute_state.insn_rd,
          rs1_data: x_rs1_data,
          rs2_data: x_rs2_data,
          rd_data: x_rd_data,
          we: x_we,
          halt: x_halt,
          my_addr_to_dmem_logic: x_addr_to_dmem_logic,
          load: load,
          store: store,
          div: div,
          load_type: load_type,
          store_type: store_type,
          div_type: div_type
        };
      end
      m_addr_to_dmem <= x_addr_to_dmem_logic;
      w_addr <= x_w_addr;
    end
  end

  // Setup AXI read address channel
  assign dmem.ARADDR = m_addr_to_dmem & ~32'b11;
  assign dmem.ARPROT = 3'b00;
  assign dmem.ARVALID = memory_state.load ? 1 : 0;

  // Ready signals to accept the data
  assign dmem.RREADY = 1'b1;  // Always ready to accept data
  assign dmem.BREADY = 1'b1;  // Always ready to accept data

  // Setup AXI write address channel
  assign dmem.AWADDR = w_addr & ~32'b11;
  assign dmem.AWPROT = 3'b00;
  assign dmem.WVALID = memory_state.store ? 1'b1 : 0;

  logic [`REG_SIZE] m_rd_data;
  logic [31:0] m_rs2_data;

  // bypass logic
  always_comb begin
    // wm bypass rs2
    if (memory_state.insn_rs2 == writeback_state.insn_rd && memory_state.insn_rs2 != 0 && 
      writeback_state.insn_opcode != OpcodeBranch && writeback_state.insn_opcode != OpcodeStore) begin
      m_rs2_data = rd_data;
    // default to original register data
    end else begin
      m_rs2_data = memory_state.rs2_data;
    end
  end

  always_comb begin
    m_rd_data = memory_state.rd_data;
    
    if (memory_state.div) begin
      if (memory_state.div_type == 3'b001) begin
        if (memory_state.rs2_data == 0) begin
          m_rd_data = -1;
        end else begin
          m_rd_data = (memory_state.rs1_data[31] != memory_state.rs2_data[31]) ? ~o_quotient + 1 : o_quotient;
        end
      end else if (memory_state.div_type == 3'b010) begin
        if (memory_state.rs2_data == 0) begin
          m_rd_data = -1;
        end else begin
          m_rd_data = o_quotient;
        end
      end else if (memory_state.div_type == 3'b011) begin
        if (memory_state.rs2_data == 0) begin
          m_rd_data = memory_state.rs1_data;
        end else begin
          m_rd_data = memory_state.rs1_data[31] ? ~o_remainder + 1 : o_remainder;
        end
      end else if (memory_state.div_type == 3'b100) begin
        if (memory_state.rs2_data == 0) begin
          m_rd_data = memory_state.rs1_data;
        end else begin
          m_rd_data = o_remainder;
        end
      end
    end
  end

  /*******************/
  /* WRITEBACK STAGE */
  /*******************/
  wire [`REG_SIZE] w_load_data_from_dmem;
  logic [`REG_SIZE] w_rs2_data;

  // package up state
  stage_writeback_t writeback_state;
  always_ff @(posedge clk) begin
    if (rst) begin
      writeback_state <= '{
        pc: 0,
        insn: 0,
        cycle_status: CYCLE_RESET,
        insn_opcode: 0,
        insn_rd: 0,
        rd_data: 0,
        we: 0,
        halt: 0,
        my_araddr_logic: 0,
        my_awaddr_logic: 0,
        load: 0,
        store: 0,
        div: 0,
        load_type: 0,
        store_type: 0,
        rs2_data: 0
      };
      w_rs2_data <= 0;
    end else begin
      begin
        writeback_state <= '{
          pc: memory_state.pc,
          insn: memory_state.insn,
          cycle_status: memory_state.cycle_status,
          insn_opcode: memory_state.insn_opcode,
          insn_rd: memory_state.insn_rd,
          rd_data: m_rd_data,
          we: memory_state.we,
          halt: memory_state.halt,
          my_araddr_logic: dmem.ARADDR,
          my_awaddr_logic: dmem.AWADDR,
          load: memory_state.load,
          store: memory_state.store,
          div: memory_state.div,
          load_type: memory_state.load_type,
          store_type: memory_state.store_type,
          rs2_data: m_rs2_data
        };
      end
      w_rs2_data <= m_rs2_data;
    end
  end

  assign w_load_data_from_dmem = writeback_state.load ? dmem.RDATA : 0;

  logic [31:0] w_load_data_from_dmem_logic;
  logic [1:0] addr_allign;

  always_comb begin
    w_insn_rd = writeback_state.insn_rd;
    rd_data = writeback_state.rd_data;
    we = writeback_state.we;
    halt = writeback_state.halt;
    w_load_data_from_dmem_logic = 32'b0;
    addr_allign = 2'b0;
    dmem.WSTRB = 0;
    dmem.WDATA = 0;

    if (writeback_state.load) begin
      w_load_data_from_dmem_logic = 32'(w_load_data_from_dmem >> (writeback_state.my_araddr_logic[1:0] * 8));
      if (writeback_state.load_type == 3'b001) begin
        rd_data = {{24{w_load_data_from_dmem_logic[7]}}, w_load_data_from_dmem_logic[7:0]};
      end else if (writeback_state.load_type == 3'b010) begin
        rd_data = {{16{w_load_data_from_dmem_logic[15]}}, w_load_data_from_dmem_logic[15:0]};
      end else if (writeback_state.load_type == 3'b011) begin
        rd_data = w_load_data_from_dmem_logic;
      end else if (writeback_state.load_type == 3'b100) begin
        rd_data = {24'b0, w_load_data_from_dmem_logic[7:0]};
      end else if (writeback_state.load_type == 3'b101) begin
        rd_data = {16'b0, w_load_data_from_dmem_logic[15:0]};
      end
    end else if (writeback_state.store) begin
      addr_allign = writeback_state.my_awaddr_logic[1:0];
      if (writeback_state.store_type == 3'b001) begin
        dmem.WSTRB = 4'b0001 << addr_allign;
        dmem.WDATA = w_rs2_data << (addr_allign * 8);
      end else if (writeback_state.store_type == 3'b010) begin
        dmem.WSTRB = 4'b0011 << addr_allign;
        dmem.WDATA = w_rs2_data << (addr_allign * 8);
      end else if (writeback_state.store_type == 3'b011) begin
        dmem.WSTRB = 4'b1111 << addr_allign;
        dmem.WDATA = w_rs2_data << (addr_allign * 8);
      end
    end

    // pc insn currently writeback 0 if not valid insn
    trace_writeback_pc = writeback_state.pc;
    // bits insn currently writeback 0 if not valid insn
    trace_writeback_insn = writeback_state.insn;
    // status of insn currently writeback
    trace_writeback_cycle_status = writeback_state.cycle_status;
  end

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
    input wire clk,
    input wire rst,
    output logic halt,
    output wire [`REG_SIZE] trace_writeback_pc,
    output wire [`INSN_SIZE] trace_writeback_insn,
    output cycle_status_e trace_writeback_cycle_status
);

  // HW5 memory interface
  wire [`INSN_SIZE] insn_from_imem;
  wire [`REG_SIZE] pc_to_imem, mem_data_addr, mem_data_loaded_value, mem_data_to_write;
  wire [3:0] mem_data_we;
  MemorySingleCycle #(
      .NUM_WORDS(8192)
  ) the_mem (
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

  // HW6 memory interface
  axi_clkrst_if axi_cr (.ACLK(clk), .ARESETn(~rst));
  axi_if axi_data ();
  axi_if axi_insn ();
  MemoryAxiLite #(.NUM_WORDS(8192)) mem (
    .axi(axi_cr),
    .insn(axi_insn.subord),
    .data(axi_data.subord)
  );

  DatapathAxilMemory datapath (
      .clk(clk),
      .rst(rst),
      .imem(axi_insn.manager),
      .dmem(axi_data.manager),
      .halt(halt),
      .trace_writeback_pc(trace_writeback_pc),
      .trace_writeback_insn(trace_writeback_insn),
      .trace_writeback_cycle_status(trace_writeback_cycle_status)
  );

endmodule
