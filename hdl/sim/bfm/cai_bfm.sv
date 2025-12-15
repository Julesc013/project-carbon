// Project Carbon - Simulation BFM
// cai_bfm: Basic helpers for CAI descriptor/completion formats.

package cai_bfm_pkg;
  import carbon_arch_pkg::*;

  localparam int unsigned SUBMIT_BITS = CARBON_CAI_SUBMIT_DESC_V1_SIZE_BYTES * 8;
  localparam int unsigned COMP_BITS   = CARBON_CAI_COMP_REC_V1_SIZE_BYTES * 8;

  task automatic build_submit_desc_v1(
      output logic [SUBMIT_BITS-1:0] desc,
      input  logic [31:0] opcode,
      input  logic [31:0] flags,
      input  logic [15:0] context_id,
      input  logic [15:0] operand_count,
      input  logic [31:0] tag,
      input  logic [63:0] operands_ptr,
      input  logic [63:0] result_ptr,
      input  logic [31:0] result_len,
      input  logic [31:0] result_stride
  );
    begin
      desc = '0;
      desc[(CARBON_CAI_SUBMIT_DESC_V1_OFF_DESC_VERSION*8) +: 16] = 16'(CARBON_CAI_SUBMIT_DESC_V1_VERSION);
      desc[(CARBON_CAI_SUBMIT_DESC_V1_OFF_DESC_SIZE_DW*8) +: 16] = 16'(CARBON_CAI_SUBMIT_DESC_V1_SIZE_BYTES / 4);
      desc[(CARBON_CAI_SUBMIT_DESC_V1_OFF_OPCODE*8) +: 32] = opcode;
      desc[(CARBON_CAI_SUBMIT_DESC_V1_OFF_FLAGS*8) +: 32] = flags;
      desc[(CARBON_CAI_SUBMIT_DESC_V1_OFF_CONTEXT_ID*8) +: 16] = context_id;
      desc[(CARBON_CAI_SUBMIT_DESC_V1_OFF_OPERAND_COUNT*8) +: 16] = operand_count;
      desc[(CARBON_CAI_SUBMIT_DESC_V1_OFF_TAG*8) +: 32] = tag;
      desc[(CARBON_CAI_SUBMIT_DESC_V1_OFF_OPERANDS_PTR*8) +: 64] = operands_ptr;
      desc[(CARBON_CAI_SUBMIT_DESC_V1_OFF_RESULT_PTR*8) +: 64] = result_ptr;
      desc[(CARBON_CAI_SUBMIT_DESC_V1_OFF_RESULT_LEN*8) +: 32] = result_len;
      desc[(CARBON_CAI_SUBMIT_DESC_V1_OFF_RESULT_STRIDE*8) +: 32] = result_stride;
    end
  endtask

  task automatic decode_comp_rec_v1(
      input  logic [COMP_BITS-1:0] rec,
      output logic [31:0] tag,
      output logic [15:0] status,
      output logic [15:0] ext_status,
      output logic [31:0] bytes_written
  );
    begin
      tag          = rec[(CARBON_CAI_COMP_REC_V1_OFF_TAG*8) +: 32];
      status       = rec[(CARBON_CAI_COMP_REC_V1_OFF_STATUS*8) +: 16];
      ext_status   = rec[(CARBON_CAI_COMP_REC_V1_OFF_EXT_STATUS*8) +: 16];
      bytes_written = rec[(CARBON_CAI_COMP_REC_V1_OFF_BYTES_WRITTEN*8) +: 32];
    end
  endtask

endpackage : cai_bfm_pkg

