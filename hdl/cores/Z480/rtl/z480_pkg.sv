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
