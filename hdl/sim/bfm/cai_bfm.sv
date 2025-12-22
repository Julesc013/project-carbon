// Project Carbon - Simulation BFM
// cai_bfm: Basic helpers for CAI descriptor/completion formats.

package cai_bfm_pkg;
  import carbon_arch_pkg::*;

  localparam int unsigned SUBMIT_BITS = CARBON_CAI_SUBMIT_DESC_V1_SIZE_BYTES * 8;
  localparam int unsigned COMP_BITS   = CARBON_CAI_COMP_REC_V1_SIZE_BYTES * 8;
  localparam int unsigned TENSOR_BITS = CARBON_CAI_TENSOR_DESC_V1_SIZE_BYTES * 8;

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
      input  logic [31:0] result_stride,
      input  logic [7:0] opcode_group = 8'(CARBON_CAI_OPGROUP_SCALAR),
      input  logic [7:0] format_primary = 8'h00,
      input  logic [7:0] format_aux = 8'h00,
      input  logic [7:0] format_flags = 8'h00,
      input  logic [63:0] tensor_desc_ptr = 64'h0,
      input  logic [15:0] tensor_desc_len = 16'h0,
      input  logic [7:0] tensor_rank = 8'h0,
      input  logic [7:0] tensor_desc_flags = 8'h0
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
      desc[(CARBON_CAI_SUBMIT_DESC_V1_OFF_OPCODE_GROUP*8) +: 8] = opcode_group;
      desc[(CARBON_CAI_SUBMIT_DESC_V1_OFF_FORMAT_PRIMARY*8) +: 8] = format_primary;
      desc[(CARBON_CAI_SUBMIT_DESC_V1_OFF_FORMAT_AUX*8) +: 8] = format_aux;
      desc[(CARBON_CAI_SUBMIT_DESC_V1_OFF_FORMAT_FLAGS*8) +: 8] = format_flags;
      desc[(CARBON_CAI_SUBMIT_DESC_V1_OFF_OPERANDS_PTR*8) +: 64] = operands_ptr;
      desc[(CARBON_CAI_SUBMIT_DESC_V1_OFF_RESULT_PTR*8) +: 64] = result_ptr;
      desc[(CARBON_CAI_SUBMIT_DESC_V1_OFF_RESULT_LEN*8) +: 32] = result_len;
      desc[(CARBON_CAI_SUBMIT_DESC_V1_OFF_RESULT_STRIDE*8) +: 32] = result_stride;
      desc[(CARBON_CAI_SUBMIT_DESC_V1_OFF_TENSOR_DESC_PTR*8) +: 64] = tensor_desc_ptr;
      desc[(CARBON_CAI_SUBMIT_DESC_V1_OFF_TENSOR_DESC_LEN*8) +: 16] = tensor_desc_len;
      desc[(CARBON_CAI_SUBMIT_DESC_V1_OFF_TENSOR_RANK*8) +: 8] = tensor_rank;
      desc[(CARBON_CAI_SUBMIT_DESC_V1_OFF_TENSOR_DESC_FLAGS*8) +: 8] = tensor_desc_flags;
    end
  endtask

  task automatic build_tensor_desc_v1(
      output logic [TENSOR_BITS-1:0] desc,
      input  logic [7:0] rank,
      input  logic [7:0] elem_format,
      input  logic [31:0] shape0,
      input  logic [31:0] shape1,
      input  logic [31:0] shape2,
      input  logic [31:0] shape3,
      input  logic [31:0] stride0,
      input  logic [31:0] stride1,
      input  logic [31:0] stride2,
      input  logic [31:0] stride3
  );
    begin
      desc = '0;
      desc[(CARBON_CAI_TENSOR_DESC_V1_OFF_DESC_VERSION*8) +: 16] = 16'(CARBON_CAI_TENSOR_DESC_V1_VERSION);
      desc[(CARBON_CAI_TENSOR_DESC_V1_OFF_DESC_SIZE_DW*8) +: 16] = 16'(CARBON_CAI_TENSOR_DESC_V1_SIZE_BYTES / 4);
      desc[(CARBON_CAI_TENSOR_DESC_V1_OFF_RANK*8) +: 8] = rank;
      desc[(CARBON_CAI_TENSOR_DESC_V1_OFF_ELEM_FORMAT*8) +: 8] = elem_format;
      desc[(CARBON_CAI_TENSOR_DESC_V1_OFF_SHAPE0*8) +: 32] = shape0;
      desc[(CARBON_CAI_TENSOR_DESC_V1_OFF_SHAPE1*8) +: 32] = shape1;
      desc[(CARBON_CAI_TENSOR_DESC_V1_OFF_SHAPE2*8) +: 32] = shape2;
      desc[(CARBON_CAI_TENSOR_DESC_V1_OFF_SHAPE3*8) +: 32] = shape3;
      desc[(CARBON_CAI_TENSOR_DESC_V1_OFF_STRIDE0*8) +: 32] = stride0;
      desc[(CARBON_CAI_TENSOR_DESC_V1_OFF_STRIDE1*8) +: 32] = stride1;
      desc[(CARBON_CAI_TENSOR_DESC_V1_OFF_STRIDE2*8) +: 32] = stride2;
      desc[(CARBON_CAI_TENSOR_DESC_V1_OFF_STRIDE3*8) +: 32] = stride3;
    end
  endtask

  task automatic check_submit_desc_v1(
      input  logic [SUBMIT_BITS-1:0] desc,
      output logic ok
  );
    logic [15:0] v;
    logic [15:0] size_dw;
    begin
      v = desc[(CARBON_CAI_SUBMIT_DESC_V1_OFF_DESC_VERSION*8) +: 16];
      size_dw = desc[(CARBON_CAI_SUBMIT_DESC_V1_OFF_DESC_SIZE_DW*8) +: 16];
      ok = (v == 16'(CARBON_CAI_SUBMIT_DESC_V1_VERSION)) &&
           (size_dw == 16'(CARBON_CAI_SUBMIT_DESC_V1_SIZE_BYTES / 4));
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
