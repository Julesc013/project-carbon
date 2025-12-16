// Project Carbon - eZ90 P7 core scaffold
// ez90_pkg: Common types and constants for the eZ90 modular core.

package ez90_pkg;
  import carbon_arch_pkg::*;

  // --------------------------------------------------------------------------
  // Privilege modes (matches csr_map.yaml encoding)
  // --------------------------------------------------------------------------
  typedef enum logic [1:0] {
    EZ90_PRIV_U = 2'd0,
    EZ90_PRIV_S = 2'd1,
    EZ90_PRIV_H = 2'd2
  } ez90_priv_e;

  // --------------------------------------------------------------------------
  // Basic uop model (v1 scaffold)
  // --------------------------------------------------------------------------
  typedef enum logic [7:0] {
    EZ90_UOP_NOP   = 8'h00,
    EZ90_UOP_ADD   = 8'h01,
    EZ90_UOP_LOAD  = 8'h02,
    EZ90_UOP_STORE = 8'h03,
    EZ90_UOP_JUMP  = 8'h04
  } ez90_uop_op_e;

  typedef enum logic [2:0] {
    EZ90_FU_INT    = 3'd0,
    EZ90_FU_BRANCH = 3'd1,
    EZ90_FU_MULDIV = 3'd2,
    EZ90_FU_VEC    = 3'd3,
    EZ90_FU_MEM    = 3'd4
  } ez90_fu_e;

  typedef struct packed {
    logic [63:0] pc;
    logic [7:0]  op;
    ez90_fu_e    fu;

    logic        rd_valid;
    logic [4:0]  rd;
    logic [4:0]  rs1;
    logic [4:0]  rs2;
    logic [63:0] imm;

    logic        is_load;
    logic        is_store;
    logic        is_branch;
    logic        is_vec;
  } ez90_uop_t;

  typedef struct packed {
    ez90_uop_t uop;
    logic [6:0] prs1;
    logic [6:0] prs2;
    logic [6:0] prd;
  } ez90_uop_rn_t;

  typedef struct packed {
    ez90_uop_rn_t uop;
    logic [5:0]   rob_idx;
  } ez90_uop_tagged_t;

  typedef struct packed {
    logic [5:0]  rob_idx;
    logic        prd_valid;
    logic [6:0]  prd;
    logic [63:0] value;
    logic [31:0] flags;
  } ez90_wb_t;

  typedef struct packed {
    logic [5:0]  rob_idx;
    logic [63:0] pc;
    logic        has_trap;
    logic [31:0] trap_cause;
    logic [63:0] trap_epc;
  } ez90_commit_evt_t;

endpackage : ez90_pkg

