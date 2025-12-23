// Project Carbon - Am9513 accelerator (v1.0)
// am9513_pkg: Shared constants and opcode/flag encodings for the Am9513 core.

package am9513_pkg;
  import carbon_arch_pkg::*;

  // --------------------------------------------------------------------------
  // Personalities / tiers
  // --------------------------------------------------------------------------
  localparam logic [7:0] AM9513_P0_AM9511 = 8'(CARBON_AMD_FPU_TIER_P0_AM9511);
  localparam logic [7:0] AM9513_P1_AM9512 = 8'(CARBON_AMD_FPU_TIER_P1_AM9512);
  localparam logic [7:0] AM9513_P2_AM9513 = 8'(CARBON_AMD_FPU_TIER_P2_AM9513);
  localparam logic [7:0] AM9513_P3_AM9514 = 8'(CARBON_AMD_FPU_TIER_P3_AM9514);
  localparam logic [7:0] AM9513_P4_AM9515 = 8'(CARBON_AMD_FPU_TIER_P4_AM9515);

  // Feature mask snapshot (feature word 0 bits).
  localparam logic [31:0] AM9513_FEATURES_BASE =
      CARBON_AM9512_IEEE_MASK |
      CARBON_AM9513_ASYNC_MASK;

  // --------------------------------------------------------------------------
  // IEEE exception flags (sticky, per-context)
  // --------------------------------------------------------------------------
  localparam int unsigned AM9513_F_NV_BIT = 0;
  localparam int unsigned AM9513_F_DZ_BIT = 1;
  localparam int unsigned AM9513_F_OF_BIT = 2;
  localparam int unsigned AM9513_F_UF_BIT = 3;
  localparam int unsigned AM9513_F_NX_BIT = 4;

  localparam logic [4:0] AM9513_F_NV = 5'b00001;
  localparam logic [4:0] AM9513_F_DZ = 5'b00010;
  localparam logic [4:0] AM9513_F_OF = 5'b00100;
  localparam logic [4:0] AM9513_F_UF = 5'b01000;
  localparam logic [4:0] AM9513_F_NX = 5'b10000;

  // --------------------------------------------------------------------------
  // CAI opcode encoding (vendor range)
  //
  // - Bit 31 must be 1 (vendor opcode range per CAI spec).
  // - Bits [15:8] carry a primary format ID (CARBON_FMT_* from formats.yaml).
  // - Bits [7:0] carry a function selector.
  // - Additional format/behavior fields are carried in submit_desc.flags.
  // --------------------------------------------------------------------------
  localparam logic [31:0] AM9513_CAI_VENDOR_BIT = 32'h8000_0000;

  localparam int unsigned AM9513_OPC_FMT_LSB = 8;
  localparam int unsigned AM9513_OPC_FUNC_LSB = 0;

  typedef enum logic [7:0] {
    AM9513_FUNC_ADD    = 8'h01,
    AM9513_FUNC_SUB    = 8'h02,
    AM9513_FUNC_MUL    = 8'h03,
    AM9513_FUNC_DIV    = 8'h04,
    AM9513_FUNC_SQRT   = 8'h05,
    AM9513_FUNC_FMA    = 8'h06,
    AM9513_FUNC_CMP    = 8'h07,
    AM9513_FUNC_MIN    = 8'h08,
    AM9513_FUNC_MAX    = 8'h09,
    AM9513_FUNC_CLASS  = 8'h0A,

    AM9513_FUNC_CONV   = 8'h10,
    AM9513_FUNC_I32_TO_F32 = 8'h11,
    AM9513_FUNC_I64_TO_F64 = 8'h12,
    AM9513_FUNC_F32_TO_I32 = 8'h13,
    AM9513_FUNC_F64_TO_I64 = 8'h14,

    AM9513_FUNC_SIN    = 8'h20,
    AM9513_FUNC_COS    = 8'h21,
    AM9513_FUNC_SINCOS = 8'h22,
    AM9513_FUNC_EXP    = 8'h23,
    AM9513_FUNC_LOG    = 8'h24,
    AM9513_FUNC_POW    = 8'h25,
    AM9513_FUNC_ATAN2  = 8'h26,
    AM9513_FUNC_HYPOT  = 8'h27
  } am9513_func_e;

  function automatic logic [31:0] am9513_opcode(input logic [7:0] func, input logic [7:0] fmt);
    return AM9513_CAI_VENDOR_BIT | (32'(fmt) << AM9513_OPC_FMT_LSB) | (32'(func) << AM9513_OPC_FUNC_LSB);
  endfunction

  // --------------------------------------------------------------------------
  // Am9514 vector opcodes (CAI_OPGROUP_VECTOR)
  // --------------------------------------------------------------------------
  typedef enum logic [7:0] {
    AM9514_VEC_ADD        = 8'h01,
    AM9514_VEC_SUB        = 8'h02,
    AM9514_VEC_MUL        = 8'h03,
    AM9514_VEC_FMA        = 8'h04,
    AM9514_VEC_CONV       = 8'h05,
    AM9514_VEC_CMP        = 8'h06,
    AM9514_VEC_MIN        = 8'h07,
    AM9514_VEC_MAX        = 8'h08,
    AM9514_VEC_SHUF_SWAP  = 8'h09,
    AM9514_VEC_SHUF_BCAST = 8'h0A
  } am9514_vec_func_e;

  function automatic logic [31:0] am9514_opcode(input logic [7:0] func);
    return AM9513_CAI_VENDOR_BIT | (32'(func) << AM9513_OPC_FUNC_LSB);
  endfunction

  // --------------------------------------------------------------------------
  // Am9515 tensor opcodes (CAI_OPGROUP_TENSOR)
  // --------------------------------------------------------------------------
  typedef enum logic [7:0] {
    AM9515_TENSOR_GEMM = 8'h01,
    AM9515_TENSOR_DOT  = 8'h02,
    AM9515_TENSOR_SUM  = 8'h03
  } am9515_tensor_func_e;

  function automatic logic [31:0] am9515_opcode(input logic [7:0] func);
    return AM9513_CAI_VENDOR_BIT | (32'(func) << AM9513_OPC_FUNC_LSB);
  endfunction

  // --------------------------------------------------------------------------
  // CAI submit descriptor flags (am9513-specific; v1)
  // --------------------------------------------------------------------------
  localparam int unsigned AM9513_SUBMIT_FLAG_MODE_VALID_BIT = 0;
  localparam int unsigned AM9513_SUBMIT_FLAG_MODE_LSB = 1; // 3 bits: 0,1,2 (P0/P1/P2)
  localparam int unsigned AM9513_SUBMIT_FLAG_MODE_WIDTH = 3;

  localparam int unsigned AM9513_SUBMIT_FLAG_RESULT_REG_BIT = 4;
  localparam int unsigned AM9513_SUBMIT_FLAG_RESULT_REG_LSB = 8;
  localparam int unsigned AM9513_SUBMIT_FLAG_RESULT_REG_WIDTH = 4; // F0..F15

  // Conversion encoding (when func == AM9513_FUNC_CONV):
  // - opcode[15:8] is dst format
  // - flags[7:0] is src format
  localparam int unsigned AM9513_SUBMIT_FLAG_CONV_SRC_FMT_LSB = 0;
  localparam int unsigned AM9513_SUBMIT_FLAG_CONV_SRC_FMT_WIDTH = 8;

  // Operand descriptor flags (am9513-specific; v1)
  localparam int unsigned AM9513_OPERAND_FLAG_IS_REG_BIT = 0;
  localparam int unsigned AM9513_OPERAND_FLAG_REG_LSB = 8;
  localparam int unsigned AM9513_OPERAND_FLAG_REG_WIDTH = 4;

  // --------------------------------------------------------------------------
  // Legacy (CSR window) opcodes (v1)
  // --------------------------------------------------------------------------
  typedef enum logic [7:0] {
    AM9513_LEG_OP_ADD  = 8'h01,
    AM9513_LEG_OP_MUL  = 8'h02,
    AM9513_LEG_OP_DIV  = 8'h03,
    AM9513_LEG_OP_SQRT = 8'h04,
    AM9513_LEG_OP_FMA  = 8'h05
  } am9513_legacy_op_e;

endpackage : am9513_pkg
