// Project Carbon - Z480 P7 core scaffold
// z480_pkg: Common types and constants for the Z480 modular core.

package z480_pkg;
  import carbon_arch_pkg::*;

  // --------------------------------------------------------------------------
  // Privilege modes (matches csr_map.yaml encoding)
  // --------------------------------------------------------------------------
  typedef enum logic [1:0] {
    Z480_PRIV_U = 2'd0,
    Z480_PRIV_S = 2'd1,
    Z480_PRIV_H = 2'd2
  } z480_priv_e;

  // --------------------------------------------------------------------------
  // Z480 ISA v1 encoding (MIPS-like 32-bit fixed width)
  // --------------------------------------------------------------------------
  localparam logic [5:0] Z480_OP_SPECIAL  = 6'h00;
  localparam logic [5:0] Z480_OP_J        = 6'h02;
  localparam logic [5:0] Z480_OP_JAL      = 6'h03;
  localparam logic [5:0] Z480_OP_BEQ      = 6'h04;
  localparam logic [5:0] Z480_OP_BNE      = 6'h05;
  localparam logic [5:0] Z480_OP_ADDI     = 6'h08;
  localparam logic [5:0] Z480_OP_LDB      = 6'h20;
  localparam logic [5:0] Z480_OP_LDH      = 6'h21;
  localparam logic [5:0] Z480_OP_LDW      = 6'h23;
  localparam logic [5:0] Z480_OP_LDD      = 6'h24;
  localparam logic [5:0] Z480_OP_LDQ      = 6'h25;
  localparam logic [5:0] Z480_OP_STB      = 6'h28;
  localparam logic [5:0] Z480_OP_STH      = 6'h29;
  localparam logic [5:0] Z480_OP_STW      = 6'h2b;
  localparam logic [5:0] Z480_OP_STD      = 6'h2c;
  localparam logic [5:0] Z480_OP_STQ      = 6'h2d;
  localparam logic [5:0] Z480_OP_CSRR     = 6'h30;
  localparam logic [5:0] Z480_OP_CSRW     = 6'h31;
  localparam logic [5:0] Z480_OP_MODEUP   = 6'h32;
  localparam logic [5:0] Z480_OP_RETMD    = 6'h33;
  localparam logic [5:0] Z480_OP_FENCE    = 6'h34;
  localparam logic [5:0] Z480_OP_FENCE_IO = 6'h35;
  localparam logic [5:0] Z480_OP_RFE      = 6'h36;

  localparam logic [5:0] Z480_FUNCT_NOP   = 6'h00;
  localparam logic [5:0] Z480_FUNCT_JR    = 6'h08;
  localparam logic [5:0] Z480_FUNCT_ADD   = 6'h20;
  localparam logic [5:0] Z480_FUNCT_SUB   = 6'h22;
  localparam logic [5:0] Z480_FUNCT_AND   = 6'h24;
  localparam logic [5:0] Z480_FUNCT_OR    = 6'h25;
  localparam logic [5:0] Z480_FUNCT_XOR   = 6'h26;

  // --------------------------------------------------------------------------
  // Basic uop model (v1 scaffold)
  // --------------------------------------------------------------------------
  typedef enum logic [7:0] {
    Z480_UOP_NOP   = 8'h00,
    Z480_UOP_ADD   = 8'h01,
    Z480_UOP_LOAD  = 8'h02,
    Z480_UOP_STORE = 8'h03,
    Z480_UOP_JUMP  = 8'h04
  } z480_uop_op_e;

  typedef enum logic [2:0] {
    Z480_FU_INT    = 3'd0,
    Z480_FU_BRANCH = 3'd1,
    Z480_FU_MULDIV = 3'd2,
    Z480_FU_VEC    = 3'd3,
    Z480_FU_MEM    = 3'd4
  } z480_fu_e;

  typedef struct packed {
    logic [63:0] pc;
    logic [7:0]  op;
    z480_fu_e    fu;

    logic        rd_valid;
    logic [4:0]  rd;
    logic [4:0]  rs1;
    logic [4:0]  rs2;
    logic [63:0] imm;

    logic        is_load;
    logic        is_store;
    logic        is_branch;
    logic        is_vec;
  } z480_uop_t;

  typedef struct packed {
    z480_uop_t uop;
    logic [6:0] prs1;
    logic [6:0] prs2;
    logic [6:0] prd;
  } z480_uop_rn_t;

  typedef struct packed {
    z480_uop_rn_t uop;
    logic [5:0]   rob_idx;
  } z480_uop_tagged_t;

  typedef struct packed {
    logic [5:0]  rob_idx;
    logic        prd_valid;
    logic [6:0]  prd;
    logic [63:0] value;
    logic [31:0] flags;
  } z480_wb_t;

  typedef struct packed {
    logic [5:0]  rob_idx;
    logic [63:0] pc;
    logic        has_trap;
    logic [31:0] trap_cause;
    logic [63:0] trap_epc;
  } z480_commit_evt_t;

endpackage : z480_pkg
