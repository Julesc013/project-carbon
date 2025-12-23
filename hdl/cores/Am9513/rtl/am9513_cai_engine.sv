// Project Carbon - Am9513 accelerator (v1.0)
// am9513_cai_engine: CAI ring fetch + completion writeback (single-outstanding v1).

module am9513_cai_engine #(
    parameter int unsigned NUM_CONTEXTS = 64,
    parameter int unsigned MAX_OPERANDS = 3,
    parameter int unsigned PENDING_DEPTH = 8
) (
    input logic clk,
    input logic rst_n,

    // DMA/fabric access for descriptor/operand/result rings.
    fabric_if.master mem_if,

    // CAI register-level link (host->dev submit; dev->host completion signals).
    cai_if.dev cai,

    // Global configuration (CSR)
    input logic        cfg_enable,
    input logic [7:0]  cfg_default_mode,
    input logic [63:0] cfg_comp_base,
    input logic [31:0] cfg_comp_ring_mask,
    input logic        cfg_comp_irq_en,

    // Context-file access (muxed by top)
    output logic [15:0] ctx_sel,
    output logic [3:0]  rf_index,
    input  logic [1:0]  rm_rdata,
    input  logic [63:0] rf_rdata,
    input  logic [127:0] vec_rdata,

    output logic        flags_or_we,
    output logic [4:0]  flags_or_mask,
    output logic        rf_we,
    output logic [63:0] rf_wdata,
    output logic        vec_we,
    output logic [127:0] vec_wdata,

    output logic        busy
);
  import carbon_arch_pkg::*;
  import am9513_pkg::*;
  import am9513_math_pkg::*;

  localparam int unsigned FAB_ADDR_W = $bits(mem_if.req_addr);
  localparam int unsigned FAB_DATA_W = $bits(mem_if.req_wdata);
  localparam int unsigned FAB_STRB_W = $bits(mem_if.req_wstrb);
  localparam int unsigned FAB_OP_W   = $bits(mem_if.req_op);
  localparam int unsigned FAB_SIZE_W = $bits(mem_if.req_size);
  localparam int unsigned FAB_ATTR_W = $bits(mem_if.req_attr);
  localparam int unsigned FAB_ID_W   = $bits(mem_if.req_id);
  localparam int unsigned FAB_CODE_W = $bits(mem_if.rsp_code);

  localparam logic [FAB_ATTR_W-1:0] DMA_ATTR =
      FAB_ATTR_W'(CARBON_FABRIC_ATTR_CACHEABLE_MASK | CARBON_FABRIC_ATTR_ORDERED_MASK);
  localparam int unsigned VEC_BYTES = 16;

  // --------------------------------------------------------------------------
  // Internal CAI rings
  // --------------------------------------------------------------------------
  logic [31:0] submit_head_q;
  logic [31:0] comp_head_q;
  logic [$clog2(PENDING_DEPTH+1)-1:0] pending_q;
  logic submit_db_d;

  // Current descriptor
  logic [63:0] desc_addr_q;
  logic [15:0] desc_version_q;
  logic [15:0] desc_size_dw_q;
  logic [31:0] desc_opcode_q;
  logic [31:0] desc_flags_q;
  logic [15:0] desc_ctx_id_q;
  logic [15:0] desc_operand_count_q;
  logic [31:0] desc_tag_q;
  logic [7:0]  desc_opcode_group_q;
  logic [7:0]  desc_fmt_primary_q;
  logic [7:0]  desc_fmt_aux_q;
  logic [7:0]  desc_fmt_flags_q;
  logic [63:0] desc_operands_ptr_q;
  logic [63:0] desc_result_ptr_q;
  logic [31:0] desc_result_len_q;
  logic [31:0] desc_result_stride_q;
  logic [63:0] desc_tensor_ptr_q;
  logic [15:0] desc_tensor_len_q;
  logic [7:0]  desc_tensor_rank_q;
  logic [7:0]  desc_tensor_flags_q;

  logic [15:0] eff_ctx_q;
  logic [7:0]  eff_mode_q;
  logic [7:0]  op_group_q;
  logic [7:0]  op_func_q;
  logic [7:0]  op_fmt_q;
  logic [7:0]  op_fmt_aux_q;
  logic [7:0]  op_fmt_flags_q;
  logic [7:0]  conv_src_fmt_q;

  logic        result_to_reg_q;
  logic [3:0]  result_reg_q;

  // Operand descriptors (bounded)
  logic [63:0] op_ptr_q   [MAX_OPERANDS];
  logic [31:0] op_flags_q [MAX_OPERANDS];
  logic [31:0] op_len_q   [MAX_OPERANDS];
  logic [31:0] op_stride_q [MAX_OPERANDS];
  logic [63:0] op_val_q   [MAX_OPERANDS];

  // Vector operand buffers (128-bit vector element)
  logic [127:0] op_vec_q [MAX_OPERANDS];
  logic [127:0] vec_result_q;
  logic [15:0]  vec_mask_q;
  logic [15:0]  vec_count_q;
  logic [15:0]  vec_index_q;
  logic [1:0]   vec_word_q;
  logic [$clog2(MAX_OPERANDS)-1:0] vec_op_idx_q;
  logic [2:0]   vec_operand_count_q;
  logic [31:0]  vec_step_bytes_q [MAX_OPERANDS];
  logic [31:0]  vec_result_step_q;
  logic         vec_exec_valid_q;
  logic [4:0]   vec_exc_flags_q;
  logic         vec_writeback_q;

  // Execution result
  am9513_exec_result_t exec_q;
  logic exec_valid_q;

  logic [127:0] vec_exec_result;
  logic [4:0]   vec_exec_flags;
  logic [15:0]  vec_exec_status;

  // Completion status cache
  logic [15:0] comp_status_q;
  logic [31:0] comp_bytes_q;

  // --------------------------------------------------------------------------
  // Fabric transaction micro-engine (single outstanding)
  // --------------------------------------------------------------------------
  typedef enum logic [3:0] {BUS_IDLE, BUS_REQ, BUS_RSP} bus_state_e;
  bus_state_e bus_state_q;
  logic [FAB_OP_W-1:0]   bus_op_q;
  logic [FAB_ADDR_W-1:0] bus_addr_q;
  logic [FAB_DATA_W-1:0] bus_wdata_q;
  logic [FAB_STRB_W-1:0] bus_wstrb_q;
  logic [FAB_SIZE_W-1:0] bus_size_q;
  logic [FAB_ATTR_W-1:0] bus_attr_q;
  logic [FAB_ID_W-1:0]   bus_id_q;

  logic [FAB_DATA_W-1:0] bus_rdata_q;
  logic [FAB_CODE_W-1:0] bus_rsp_code_q;

  typedef enum logic [7:0] {
    ST_IDLE,
    ST_DESC_RD,
    ST_DESC_CAP,
    ST_OPDESC_RD,
    ST_OPDESC_CAP,
    ST_OPVAL_REG,
    ST_OPVAL_RD,
    ST_OPVAL_CAP,
    ST_EXEC,
    ST_VEC_INIT,
    ST_VEC_REG,
    ST_VEC_OP_RD,
    ST_VEC_OP_CAP,
    ST_VEC_EXEC,
    ST_VEC_RES_WR,
    ST_VEC_RES_ADV,
    ST_RESULT_WR,
    ST_RESULT_WR2,
    ST_RESULT_ADV,
    ST_COMP_WR,
    ST_COMP_WR_NEXT,
    ST_COMP_WR_ADV,
    ST_FINISH
  } st_e;

  st_e st_q;
  st_e st_after_bus_q;

  logic [4:0] desc_word_q;
  logic [2:0] opdesc_word_q;
  logic [$clog2(MAX_OPERANDS)-1:0] opdesc_idx_q;
  logic [$clog2(MAX_OPERANDS)-1:0] opval_idx_q;
  logic opval_hi_q;

  logic [63:0] tmp_addr_q;
  logic [31:0] tmp_lo_q;

  // Result writeback tracking (handles multi-result ops like SINCOS).
  logic        result_sel_q;
  logic [63:0] result_base_q;
  logic [31:0] result_step_q;
  logic [31:0] result_elem_bytes_q;

  // Completion write word index
  logic [1:0] comp_word_q;
  logic [63:0] comp_addr_q;

  // CAI status outputs
  assign cai.comp_base = cfg_comp_base;

  // Busy reflects state machine activity (not bus alone).
  assign busy = (st_q != ST_IDLE);

  // Context-file control defaults (driven during CAI activity).
  always_comb begin
    ctx_sel = eff_ctx_q;
    rf_index = 4'h0;
    flags_or_we = 1'b0;
    flags_or_mask = 5'h0;
    rf_we = 1'b0;
    rf_wdata = '0;
    vec_we = 1'b0;
    vec_wdata = '0;

    if (st_q == ST_OPVAL_REG) begin
      rf_index = op_flags_q[opval_idx_q][AM9513_OPERAND_FLAG_REG_LSB +: AM9513_OPERAND_FLAG_REG_WIDTH];
    end
    if (st_q == ST_VEC_REG) begin
      rf_index = op_flags_q[vec_op_idx_q][AM9513_OPERAND_FLAG_REG_LSB +: AM9513_OPERAND_FLAG_REG_WIDTH];
    end

    if (exec_valid_q && ((st_q == ST_RESULT_WR) || (st_q == ST_COMP_WR))) begin
      flags_or_we = 1'b1;
      flags_or_mask = exec_q.exc_flags;
      if (result_to_reg_q && (eff_mode_q == AM9513_P2_AM9513) &&
          (exec_q.cai_status == 16'(CARBON_CAI_STATUS_OK))) begin
        rf_we = 1'b1;
        rf_index = result_reg_q;
        rf_wdata = exec_q.res0;
      end
    end

    if (vec_exec_valid_q && (st_q == ST_COMP_WR)) begin
      flags_or_we = 1'b1;
      flags_or_mask = vec_exc_flags_q;
      if (vec_writeback_q && (vec_exec_status == 16'(CARBON_CAI_STATUS_OK))) begin
        vec_we = 1'b1;
        rf_index = result_reg_q;
        vec_wdata = vec_result_q;
      end
    end
  end

  // --------------------------------------------------------------------------
  // Fabric interface wiring
  // --------------------------------------------------------------------------
  assign mem_if.req_valid = (bus_state_q == BUS_REQ);
  assign mem_if.req_op    = bus_op_q;
  assign mem_if.req_addr  = bus_addr_q;
  assign mem_if.req_wdata = bus_wdata_q;
  assign mem_if.req_wstrb = bus_wstrb_q;
  assign mem_if.req_size  = bus_size_q;
  assign mem_if.req_attr  = bus_attr_q;
  assign mem_if.req_id    = bus_id_q;

  assign mem_if.rsp_ready = 1'b1;

  wire bus_req_fire = mem_if.req_valid && mem_if.req_ready;
  wire bus_rsp_fire = mem_if.rsp_valid && mem_if.rsp_ready;

  // --------------------------------------------------------------------------
  // Address helpers
  // --------------------------------------------------------------------------
  function automatic logic addr64_ok(input logic [63:0] a);
    return (a[63:32] == 32'h0);
  endfunction

  function automatic logic [FAB_ADDR_W-1:0] addr64_to_fab(input logic [63:0] a);
    return FAB_ADDR_W'(a[FAB_ADDR_W-1:0]);
  endfunction

  function automatic logic [63:0] desc_word_addr(input logic [63:0] base, input logic [4:0] idx);
    logic [31:0] off;
    begin
      unique case (idx)
        4'd0: off = 32'(CARBON_CAI_SUBMIT_DESC_V1_OFF_DESC_VERSION);
        4'd1: off = 32'(CARBON_CAI_SUBMIT_DESC_V1_OFF_OPCODE);
        4'd2: off = 32'(CARBON_CAI_SUBMIT_DESC_V1_OFF_FLAGS);
        4'd3: off = 32'(CARBON_CAI_SUBMIT_DESC_V1_OFF_CONTEXT_ID);
        4'd4: off = 32'(CARBON_CAI_SUBMIT_DESC_V1_OFF_TAG);
        4'd5: off = 32'(CARBON_CAI_SUBMIT_DESC_V1_OFF_OPCODE_GROUP);
        4'd6: off = 32'(CARBON_CAI_SUBMIT_DESC_V1_OFF_OPERANDS_PTR);
        4'd7: off = 32'(CARBON_CAI_SUBMIT_DESC_V1_OFF_OPERANDS_PTR) + 32'd4;
        4'd8: off = 32'(CARBON_CAI_SUBMIT_DESC_V1_OFF_RESULT_PTR);
        4'd9: off = 32'(CARBON_CAI_SUBMIT_DESC_V1_OFF_RESULT_PTR) + 32'd4;
        4'd10: off = 32'(CARBON_CAI_SUBMIT_DESC_V1_OFF_RESULT_LEN);
        4'd11: off = 32'(CARBON_CAI_SUBMIT_DESC_V1_OFF_RESULT_STRIDE);
        4'd12: off = 32'(CARBON_CAI_SUBMIT_DESC_V1_OFF_TENSOR_DESC_PTR);
        4'd13: off = 32'(CARBON_CAI_SUBMIT_DESC_V1_OFF_TENSOR_DESC_PTR) + 32'd4;
        4'd14: off = 32'(CARBON_CAI_SUBMIT_DESC_V1_OFF_TENSOR_DESC_LEN);
        default: off = 32'(CARBON_CAI_SUBMIT_DESC_V1_OFF_RESERVED2);
      endcase
      desc_word_addr = base + 64'(off);
    end
  endfunction

  function automatic logic [63:0] opdesc_word_addr(
      input logic [63:0] base,
      input int unsigned op_index,
      input int unsigned word_index
  );
    logic [63:0] a;
    logic [31:0] off;
    begin
      a = base + 64'(op_index * CARBON_CAI_OPERAND_DESC_V1_SIZE_BYTES);
      unique case (word_index)
        0: off = 32'(CARBON_CAI_OPERAND_DESC_V1_OFF_PTR);
        1: off = 32'(CARBON_CAI_OPERAND_DESC_V1_OFF_PTR) + 32'd4;
        2: off = 32'(CARBON_CAI_OPERAND_DESC_V1_OFF_LEN);
        3: off = 32'(CARBON_CAI_OPERAND_DESC_V1_OFF_STRIDE);
        default: off = 32'(CARBON_CAI_OPERAND_DESC_V1_OFF_FLAGS);
      endcase
      opdesc_word_addr = a + 64'(off);
    end
  endfunction

  function automatic int unsigned operand_bytes(
      input logic [7:0] func,
      input logic [7:0] fmt,
      input logic [7:0] src_fmt,
      input int unsigned op_index
  );
    logic [7:0] ofmt;
    begin
      ofmt = fmt;
      if ((func == AM9513_FUNC_CONV) && (op_index == 0)) ofmt = src_fmt;
      operand_bytes = fmt_bytes(ofmt);
    end
  endfunction

  // --------------------------------------------------------------------------
  // Vector execution helper (one 128-bit vector element)
  // --------------------------------------------------------------------------
  am9514_vector u_vec (
      .func(op_func_q),
      .fmt(op_fmt_q),
      .fmt_aux(op_fmt_aux_q),
      .fmt_flags(op_fmt_flags_q),
      .op0(op_vec_q[0]),
      .op1(op_vec_q[1]),
      .op2(op_vec_q[2]),
      .mask_bits(vec_mask_q),
      .rm(rm_rdata),
      .result(vec_exec_result),
      .exc_flags(vec_exec_flags),
      .status(vec_exec_status)
  );

  // --------------------------------------------------------------------------
  // Main state machine
  // --------------------------------------------------------------------------
  always_ff @(posedge clk or negedge rst_n) begin
    int unsigned i;
    if (!rst_n) begin
      submit_head_q <= '0;
      comp_head_q <= '0;
      pending_q <= '0;
      submit_db_d <= 1'b0;

      desc_addr_q <= '0;
      desc_word_q <= '0;

      desc_version_q <= '0;
      desc_size_dw_q <= '0;
      desc_opcode_q <= '0;
      desc_flags_q <= '0;
      desc_ctx_id_q <= '0;
      desc_operand_count_q <= '0;
      desc_tag_q <= '0;
      desc_opcode_group_q <= 8'(CARBON_CAI_OPGROUP_SCALAR);
      desc_fmt_primary_q <= 8'h0;
      desc_fmt_aux_q <= 8'h0;
      desc_fmt_flags_q <= 8'h0;
      desc_operands_ptr_q <= '0;
      desc_result_ptr_q <= '0;
      desc_result_len_q <= '0;
      desc_result_stride_q <= '0;
      desc_tensor_ptr_q <= '0;
      desc_tensor_len_q <= '0;
      desc_tensor_rank_q <= '0;
      desc_tensor_flags_q <= '0;

      eff_ctx_q <= '0;
      eff_mode_q <= AM9513_P0_AM9511;
      op_group_q <= 8'(CARBON_CAI_OPGROUP_SCALAR);
      op_func_q <= '0;
      op_fmt_q <= '0;
      op_fmt_aux_q <= '0;
      op_fmt_flags_q <= '0;
      conv_src_fmt_q <= 8'(CARBON_FMT_BINARY32);
      result_to_reg_q <= 1'b0;
      result_reg_q <= '0;

      for (i = 0; i < MAX_OPERANDS; i++) begin
        op_ptr_q[i] <= '0;
        op_flags_q[i] <= '0;
        op_len_q[i] <= '0;
        op_stride_q[i] <= '0;
        op_val_q[i] <= '0;
        op_vec_q[i] <= '0;
        vec_step_bytes_q[i] <= '0;
      end

      exec_q <= '0;
      exec_valid_q <= 1'b0;
      vec_result_q <= '0;
      vec_mask_q <= 16'hFFFF;
      vec_count_q <= '0;
      vec_index_q <= '0;
      vec_word_q <= '0;
      vec_op_idx_q <= '0;
      vec_operand_count_q <= '0;
      vec_result_step_q <= '0;
      vec_exec_valid_q <= 1'b0;
      vec_exc_flags_q <= '0;
      vec_writeback_q <= 1'b0;
      comp_status_q <= 16'(CARBON_CAI_STATUS_OK);
      comp_bytes_q <= '0;

      bus_state_q <= BUS_IDLE;
      bus_op_q <= '0;
      bus_addr_q <= '0;
      bus_wdata_q <= '0;
      bus_wstrb_q <= '0;
      bus_size_q <= '0;
      bus_attr_q <= DMA_ATTR;
      bus_id_q <= '0;
      bus_rdata_q <= '0;
      bus_rsp_code_q <= '0;

      st_q <= ST_IDLE;
      st_after_bus_q <= ST_IDLE;

      opdesc_word_q <= '0;
      opdesc_idx_q <= '0;
      opval_idx_q <= '0;
      opval_hi_q <= 1'b0;
      tmp_addr_q <= '0;
      tmp_lo_q <= '0;

      result_sel_q <= 1'b0;
      result_base_q <= '0;
      result_step_q <= '0;
      result_elem_bytes_q <= '0;

      comp_word_q <= '0;
      comp_addr_q <= '0;

      cai.comp_doorbell <= 1'b0;
      cai.comp_irq <= 1'b0;
      cai.status <= '0;
    end else begin
      // Doorbell pulse detect (count pending descriptors; saturate).
      submit_db_d <= cai.submit_doorbell;
      if (cai.submit_doorbell && !submit_db_d) begin
        if (pending_q != PENDING_DEPTH[$clog2(PENDING_DEPTH+1)-1:0]) pending_q <= pending_q + 1'b1;
      end

      // Default pulses low.
      cai.comp_doorbell <= 1'b0;
      cai.comp_irq <= 1'b0;

      // Status (simple v1 encoding).
      cai.status[0] <= cfg_enable;
      cai.status[1] <= (st_q != ST_IDLE);
      cai.status[15:8] <= 8'(pending_q);
      cai.status[31:16] <= 16'h0000;

      // Bus engine
      if (bus_state_q == BUS_REQ) begin
        if (bus_req_fire) begin
          bus_state_q <= BUS_RSP;
        end
      end else if (bus_state_q == BUS_RSP) begin
        if (bus_rsp_fire) begin
          bus_rdata_q <= mem_if.rsp_rdata;
          bus_rsp_code_q <= mem_if.rsp_code;
          bus_state_q <= BUS_IDLE;
          st_q <= st_after_bus_q;
        end
      end

      // Main FSM actions (only when bus idle or no bus needed)
      if (bus_state_q == BUS_IDLE) begin
        unique case (st_q)
          ST_IDLE: begin
            if (cfg_enable && (pending_q != 0)) begin
              logic [31:0] ring_idx;
              ring_idx = submit_head_q & cai.submit_ring_mask;
              exec_valid_q <= 1'b0;
              vec_exec_valid_q <= 1'b0;
              vec_writeback_q <= 1'b0;
              vec_exc_flags_q <= '0;
              desc_addr_q <= cai.submit_desc_base + (64'(ring_idx) << 6);
              desc_word_q <= 5'd0;
              st_q <= ST_DESC_RD;
            end
          end

          ST_DESC_RD: begin
            if (!addr64_ok(desc_addr_q)) begin
              comp_status_q <= 16'(CARBON_CAI_STATUS_FAULT);
              comp_bytes_q <= '0;
              desc_tag_q <= '0;
              st_q <= ST_COMP_WR;
            end else begin
              bus_op_q <= FAB_OP_W'(CARBON_FABRIC_XACT_READ);
              bus_addr_q <= addr64_to_fab(desc_word_addr(desc_addr_q, desc_word_q));
              bus_wdata_q <= '0;
              bus_wstrb_q <= '0;
              bus_size_q <= '0;
              bus_attr_q <= DMA_ATTR;
              bus_id_q <= '0;
              st_after_bus_q <= ST_DESC_CAP;
              bus_state_q <= BUS_REQ;
            end
          end

          ST_DESC_CAP: begin
            if (bus_rsp_code_q != FAB_CODE_W'(CARBON_FABRIC_RESP_OK)) begin
              comp_status_q <= 16'(CARBON_CAI_STATUS_FAULT);
              comp_bytes_q <= '0;
              desc_tag_q <= '0;
              st_q <= ST_COMP_WR;
            end else begin
              unique case (desc_word_q)
                5'd0: begin
                  desc_version_q <= bus_rdata_q[15:0];
                  desc_size_dw_q <= bus_rdata_q[31:16];
                end
                5'd1: desc_opcode_q <= bus_rdata_q;
                5'd2: desc_flags_q <= bus_rdata_q;
                5'd3: begin
                  desc_ctx_id_q <= bus_rdata_q[15:0];
                  desc_operand_count_q <= bus_rdata_q[31:16];
                end
                5'd4: desc_tag_q <= bus_rdata_q;
                5'd5: begin
                  desc_opcode_group_q <= bus_rdata_q[7:0];
                  desc_fmt_primary_q <= bus_rdata_q[15:8];
                  desc_fmt_aux_q <= bus_rdata_q[23:16];
                  desc_fmt_flags_q <= bus_rdata_q[31:24];
                end
                5'd6: desc_operands_ptr_q[31:0] <= bus_rdata_q;
                5'd7: desc_operands_ptr_q[63:32] <= bus_rdata_q;
                5'd8: desc_result_ptr_q[31:0] <= bus_rdata_q;
                5'd9: desc_result_ptr_q[63:32] <= bus_rdata_q;
                5'd10: desc_result_len_q <= bus_rdata_q;
                5'd11: desc_result_stride_q <= bus_rdata_q;
                5'd12: desc_tensor_ptr_q[31:0] <= bus_rdata_q;
                5'd13: desc_tensor_ptr_q[63:32] <= bus_rdata_q;
                5'd14: begin
                  desc_tensor_len_q <= bus_rdata_q[15:0];
                  desc_tensor_rank_q <= bus_rdata_q[23:16];
                  desc_tensor_flags_q <= bus_rdata_q[31:24];
                end
                default: begin
                end
              endcase

              if (desc_word_q == 5'd15) begin
                // Validate and advance.
                if ((desc_version_q != 16'(CARBON_CAI_SUBMIT_DESC_V1_VERSION)) ||
                    (desc_size_dw_q != 16'(CARBON_CAI_SUBMIT_DESC_V1_SIZE_BYTES / 4))) begin
                  comp_status_q <= 16'(CARBON_CAI_STATUS_INVALID_OP);
                  comp_bytes_q <= '0;
                  st_q <= ST_COMP_WR;
                end else if (desc_operand_count_q > MAX_OPERANDS) begin
                  comp_status_q <= 16'(CARBON_CAI_STATUS_UNSUPPORTED);
                  comp_bytes_q <= '0;
                  st_q <= ST_COMP_WR;
                end else begin
                  // Effective context selection.
                  eff_ctx_q <= (desc_ctx_id_q == 16'hFFFF) ? cai.context_sel : desc_ctx_id_q;
                  // Mode selection (CSR default, optionally overridden per descriptor).
                  eff_mode_q <= cfg_default_mode;
                  if (desc_flags_q[AM9513_SUBMIT_FLAG_MODE_VALID_BIT]) begin
                    eff_mode_q <= desc_flags_q[AM9513_SUBMIT_FLAG_MODE_LSB +: AM9513_SUBMIT_FLAG_MODE_WIDTH];
                  end

                  op_group_q <= desc_opcode_group_q;
                  op_func_q <= desc_opcode_q[7:0];
                  op_fmt_q  <= desc_fmt_primary_q;
                  op_fmt_aux_q <= desc_fmt_aux_q;
                  op_fmt_flags_q <= desc_fmt_flags_q;
                  conv_src_fmt_q <= desc_flags_q[7:0];

                  result_to_reg_q <= desc_flags_q[AM9513_SUBMIT_FLAG_RESULT_REG_BIT];
                  result_reg_q <= desc_flags_q[AM9513_SUBMIT_FLAG_RESULT_REG_LSB +: AM9513_SUBMIT_FLAG_RESULT_REG_WIDTH];

                  opdesc_idx_q <= '0;
                  opdesc_word_q <= '0;
                  st_q <= ST_OPDESC_RD;
                end
              end else begin
                desc_word_q <= desc_word_q + 1'b1;
                st_q <= ST_DESC_RD;
              end
            end
          end

          ST_OPDESC_RD: begin
            if (desc_operand_count_q == 0) begin
              opval_idx_q <= '0;
              st_q <= ST_EXEC;
            end else if (!addr64_ok(desc_operands_ptr_q)) begin
              comp_status_q <= 16'(CARBON_CAI_STATUS_FAULT);
              comp_bytes_q <= '0;
              st_q <= ST_COMP_WR;
            end else begin
              bus_op_q <= FAB_OP_W'(CARBON_FABRIC_XACT_READ);
              bus_addr_q <= addr64_to_fab(opdesc_word_addr(desc_operands_ptr_q, opdesc_idx_q, opdesc_word_q));
              bus_wdata_q <= '0;
              bus_wstrb_q <= '0;
              bus_size_q <= '0;
              bus_attr_q <= DMA_ATTR;
              bus_id_q <= '0;
              st_after_bus_q <= ST_OPDESC_CAP;
              bus_state_q <= BUS_REQ;
            end
          end

          ST_OPDESC_CAP: begin
            if (bus_rsp_code_q != FAB_CODE_W'(CARBON_FABRIC_RESP_OK)) begin
              comp_status_q <= 16'(CARBON_CAI_STATUS_FAULT);
              comp_bytes_q <= '0;
              st_q <= ST_COMP_WR;
            end else begin
              unique case (opdesc_word_q)
                3'd0: op_ptr_q[opdesc_idx_q][31:0] <= bus_rdata_q;
                3'd1: op_ptr_q[opdesc_idx_q][63:32] <= bus_rdata_q;
                3'd2: op_len_q[opdesc_idx_q] <= bus_rdata_q;
                3'd3: op_stride_q[opdesc_idx_q] <= bus_rdata_q;
                default: op_flags_q[opdesc_idx_q] <= bus_rdata_q;
              endcase

              if (opdesc_word_q == 3'd4) begin
                opdesc_word_q <= '0;
                if (opdesc_idx_q == (desc_operand_count_q - 1'b1)) begin
                  opval_idx_q <= '0;
                  opval_hi_q <= 1'b0;
                  st_q <= ST_OPVAL_REG;
                end else begin
                  opdesc_idx_q <= opdesc_idx_q + 1'b1;
                  st_q <= ST_OPDESC_RD;
                end
              end else begin
                opdesc_word_q <= opdesc_word_q + 1'b1;
                st_q <= ST_OPDESC_RD;
              end
            end
          end

          ST_OPVAL_REG: begin
            // Decide per operand whether to read from regfile or memory.
            if (opval_idx_q == desc_operand_count_q) begin
              st_q <= ST_EXEC;
            end else if ((eff_mode_q != AM9513_P2_AM9513) &&
                         op_flags_q[opval_idx_q][AM9513_OPERAND_FLAG_IS_REG_BIT]) begin
              comp_status_q <= 16'(CARBON_CAI_STATUS_UNSUPPORTED);
              comp_bytes_q <= '0;
              st_q <= ST_COMP_WR;
            end else if (op_flags_q[opval_idx_q][AM9513_OPERAND_FLAG_IS_REG_BIT]) begin
              // reg operand: capture combinational rf_rdata
              op_val_q[opval_idx_q] <= rf_rdata;
              opval_idx_q <= opval_idx_q + 1'b1;
              st_q <= ST_OPVAL_REG;
            end else begin
              // memory operand
              tmp_addr_q <= op_ptr_q[opval_idx_q];
              opval_hi_q <= 1'b0;
              st_q <= ST_OPVAL_RD;
            end
          end

          ST_OPVAL_RD: begin
            int unsigned bytes;
            bytes = operand_bytes(op_func_q, op_fmt_q, conv_src_fmt_q, opval_idx_q);
            if (!addr64_ok(tmp_addr_q)) begin
              comp_status_q <= 16'(CARBON_CAI_STATUS_FAULT);
              comp_bytes_q <= '0;
              st_q <= ST_COMP_WR;
            end else begin
              bus_op_q <= FAB_OP_W'(CARBON_FABRIC_XACT_READ);
              bus_addr_q <= addr64_to_fab(tmp_addr_q + (opval_hi_q ? 64'd4 : 64'd0));
              bus_wdata_q <= '0;
              bus_wstrb_q <= '0;
              bus_size_q <= '0;
              bus_attr_q <= DMA_ATTR;
              bus_id_q <= '0;
              st_after_bus_q <= ST_OPVAL_CAP;
              bus_state_q <= BUS_REQ;
            end
          end

          ST_OPVAL_CAP: begin
            int unsigned bytes;
            bytes = operand_bytes(op_func_q, op_fmt_q, conv_src_fmt_q, opval_idx_q);
            if (bus_rsp_code_q != FAB_CODE_W'(CARBON_FABRIC_RESP_OK)) begin
              comp_status_q <= 16'(CARBON_CAI_STATUS_FAULT);
              comp_bytes_q <= '0;
              st_q <= ST_COMP_WR;
            end else begin
              if (bytes == 8) begin
                if (!opval_hi_q) begin
                  tmp_lo_q <= bus_rdata_q;
                  opval_hi_q <= 1'b1;
                  st_q <= ST_OPVAL_RD;
                end else begin
                  op_val_q[opval_idx_q] <= {bus_rdata_q, tmp_lo_q};
                  opval_idx_q <= opval_idx_q + 1'b1;
                  opval_hi_q <= 1'b0;
                  st_q <= ST_OPVAL_REG;
                end
              end else if (bytes == 4) begin
                op_val_q[opval_idx_q] <= {32'h0, bus_rdata_q};
                opval_idx_q <= opval_idx_q + 1'b1;
                st_q <= ST_OPVAL_REG;
              end else begin
                op_val_q[opval_idx_q] <= {48'h0, bus_rdata_q[15:0]};
                opval_idx_q <= opval_idx_q + 1'b1;
                st_q <= ST_OPVAL_REG;
              end
            end
          end

          ST_EXEC: begin
            // Context validity check.
            if (int'(eff_ctx_q) >= int'(NUM_CONTEXTS)) begin
              comp_status_q <= 16'(CARBON_CAI_STATUS_FAULT);
              comp_bytes_q <= '0;
              st_q <= ST_COMP_WR;
            end else begin
              if (op_group_q == 8'(CARBON_CAI_OPGROUP_SCALAR)) begin
                if (result_to_reg_q && (eff_mode_q != AM9513_P2_AM9513)) begin
                  comp_status_q <= 16'(CARBON_CAI_STATUS_UNSUPPORTED);
                  comp_bytes_q <= '0;
                  st_q <= ST_COMP_WR;
                end else begin
                  am9513_exec_result_t ex;
                  int unsigned elem_bytes;
                  ex = am9513_execute(op_func_q, op_fmt_q, desc_flags_q,
                                      op_val_q[0], op_val_q[1], op_val_q[2], rm_rdata);
                  exec_q <= ex;
                  exec_valid_q <= 1'b1;
                  comp_status_q <= ex.cai_status;
                  comp_bytes_q <= ex.bytes_written;

                  // If result goes to register, skip memory write.
                  if (result_to_reg_q && (eff_mode_q == AM9513_P2_AM9513) &&
                      (ex.cai_status == 16'(CARBON_CAI_STATUS_OK))) begin
                    comp_bytes_q <= 32'h0;
                    st_q <= ST_COMP_WR;
                  end else if (ex.cai_status != 16'(CARBON_CAI_STATUS_OK)) begin
                    comp_bytes_q <= 32'h0;
                    st_q <= ST_COMP_WR;
                  end else if ((desc_result_len_q != 0) && (desc_result_len_q < ex.bytes_written)) begin
                    comp_status_q <= 16'(CARBON_CAI_STATUS_FAULT);
                    comp_bytes_q <= 32'h0;
                    st_q <= ST_COMP_WR;
                  end else begin
                    // Result element sizing: scalar results use bytes_written, multi-result uses fmt size.
                    elem_bytes = fmt_bytes(op_fmt_q);
                    if (!ex.res1_valid) elem_bytes = ex.bytes_written;

                    result_sel_q <= 1'b0;
                    result_base_q <= desc_result_ptr_q;
                    result_elem_bytes_q <= 32'(elem_bytes);
                    result_step_q <= (desc_result_stride_q != 0) ? desc_result_stride_q : 32'(elem_bytes);
                    st_q <= ST_RESULT_WR;
                  end
                end
              end else if (op_group_q == 8'(CARBON_CAI_OPGROUP_VECTOR)) begin
                exec_valid_q <= 1'b0;
                vec_exec_valid_q <= 1'b0;
                vec_writeback_q <= 1'b0;
                st_q <= ST_VEC_INIT;
              end else begin
                comp_status_q <= 16'(CARBON_CAI_STATUS_INVALID_OP);
                comp_bytes_q <= '0;
                st_q <= ST_COMP_WR;
              end
            end
          end

          ST_VEC_INIT: begin
            int unsigned need_ops;
            int unsigned vec_count;
            int unsigned vec_bytes;
            int unsigned idx;
            logic unsupported;
            unsupported = 1'b0;
            vec_bytes = VEC_BYTES;
            vec_count = 0;

            // Require P3 or above for vector ops.
            if (eff_mode_q < AM9513_P3_AM9514) begin
              comp_status_q <= 16'(CARBON_CAI_STATUS_UNSUPPORTED);
              comp_bytes_q <= '0;
              st_q <= ST_COMP_WR;
            end else begin
              unique case (op_func_q)
                AM9514_VEC_FMA: need_ops = 3;
                AM9514_VEC_CONV: need_ops = 1;
                AM9514_VEC_SHUF_SWAP: need_ops = 1;
                AM9514_VEC_SHUF_BCAST: need_ops = 1;
                default: need_ops = 2;
              endcase

              if ((need_ops == 0) || (desc_operand_count_q != need_ops)) begin
                comp_status_q <= 16'(CARBON_CAI_STATUS_INVALID_OP);
                comp_bytes_q <= '0;
                st_q <= ST_COMP_WR;
              end else begin
                if (result_to_reg_q) vec_count = 1;
                else if (desc_result_len_q != 0) vec_count = desc_result_len_q / vec_bytes;
                else if (op_len_q[0] != 0) vec_count = op_len_q[0] / vec_bytes;
                else vec_count = 1;

                if ((vec_count == 0) ||
                    ((desc_result_len_q != 0) && (desc_result_len_q < (vec_count * vec_bytes)))) begin
                  comp_status_q <= 16'(CARBON_CAI_STATUS_FAULT);
                  comp_bytes_q <= '0;
                  st_q <= ST_COMP_WR;
                end else begin
                  vec_operand_count_q <= 3'(need_ops);
                  vec_count_q <= 16'(vec_count);
                  vec_index_q <= '0;
                  vec_op_idx_q <= '0;
                  vec_word_q <= '0;
                  vec_exec_valid_q <= 1'b0;
                  vec_writeback_q <= 1'b0;
                  vec_exc_flags_q <= '0;
                  vec_result_step_q <= (desc_result_stride_q != 0) ? desc_result_stride_q : 32'(vec_bytes);

                  if (desc_fmt_flags_q[AM9514_FMTFLAG_MASKED_BIT]) begin
                    vec_mask_q <= desc_flags_q[31:16];
                  end else begin
                    vec_mask_q <= 16'hFFFF;
                  end

                  // Validate operand lengths/strides for memory operands.
                  for (idx = 0; idx < MAX_OPERANDS; idx++) begin
                    if (idx < need_ops) begin
                      if (op_flags_q[idx][AM9513_OPERAND_FLAG_IS_REG_BIT]) begin
                        if (vec_count != 1) unsupported = 1'b1;
                        vec_step_bytes_q[idx] <= 32'h0;
                      end else begin
                        vec_step_bytes_q[idx] <= (op_stride_q[idx] != 0) ? op_stride_q[idx] : 32'(vec_bytes);
                        if ((op_len_q[idx] != 0) && (op_len_q[idx] < (vec_count * vec_bytes))) begin
                          unsupported = 1'b1;
                        end
                      end
                    end else begin
                      vec_step_bytes_q[idx] <= 32'h0;
                    end
                  end

                  if (unsupported) begin
                    comp_status_q <= 16'(CARBON_CAI_STATUS_UNSUPPORTED);
                    comp_bytes_q <= '0;
                    st_q <= ST_COMP_WR;
                  end else if (!result_to_reg_q && !addr64_ok(desc_result_ptr_q)) begin
                    comp_status_q <= 16'(CARBON_CAI_STATUS_FAULT);
                    comp_bytes_q <= '0;
                    st_q <= ST_COMP_WR;
                  end else begin
                    st_q <= ST_VEC_OP_RD;
                  end
                end
              end
            end
          end

          ST_VEC_OP_RD: begin
            if (vec_op_idx_q == vec_operand_count_q[$clog2(MAX_OPERANDS)-1:0]) begin
              st_q <= ST_VEC_EXEC;
            end else if (op_flags_q[vec_op_idx_q][AM9513_OPERAND_FLAG_IS_REG_BIT]) begin
              st_q <= ST_VEC_REG;
            end else begin
              logic [63:0] addr;
              addr = op_ptr_q[vec_op_idx_q] +
                     64'(vec_index_q) * 64'(vec_step_bytes_q[vec_op_idx_q]) +
                     64'(vec_word_q * 4);
              if (!addr64_ok(addr)) begin
                comp_status_q <= 16'(CARBON_CAI_STATUS_FAULT);
                comp_bytes_q <= '0;
                st_q <= ST_COMP_WR;
              end else begin
                bus_op_q <= FAB_OP_W'(CARBON_FABRIC_XACT_READ);
                bus_addr_q <= addr64_to_fab(addr);
                bus_wdata_q <= '0;
                bus_wstrb_q <= '0;
                bus_size_q <= '0;
                bus_attr_q <= DMA_ATTR;
                bus_id_q <= '0;
                st_after_bus_q <= ST_VEC_OP_CAP;
                bus_state_q <= BUS_REQ;
              end
            end
          end

          ST_VEC_REG: begin
            op_vec_q[vec_op_idx_q] <= vec_rdata;
            vec_op_idx_q <= vec_op_idx_q + 1'b1;
            st_q <= ST_VEC_OP_RD;
          end

          ST_VEC_OP_CAP: begin
            if (bus_rsp_code_q != FAB_CODE_W'(CARBON_FABRIC_RESP_OK)) begin
              comp_status_q <= 16'(CARBON_CAI_STATUS_FAULT);
              comp_bytes_q <= '0;
              st_q <= ST_COMP_WR;
            end else begin
              unique case (vec_word_q)
                2'd0: op_vec_q[vec_op_idx_q][31:0] <= bus_rdata_q;
                2'd1: op_vec_q[vec_op_idx_q][63:32] <= bus_rdata_q;
                2'd2: op_vec_q[vec_op_idx_q][95:64] <= bus_rdata_q;
                default: op_vec_q[vec_op_idx_q][127:96] <= bus_rdata_q;
              endcase

              if (vec_word_q == 2'd3) begin
                vec_word_q <= 2'd0;
                vec_op_idx_q <= vec_op_idx_q + 1'b1;
              end else begin
                vec_word_q <= vec_word_q + 1'b1;
              end
              st_q <= ST_VEC_OP_RD;
            end
          end

          ST_VEC_EXEC: begin
            vec_result_q <= vec_exec_result;
            vec_exc_flags_q <= vec_exec_flags;
            vec_exec_valid_q <= 1'b1;
            comp_status_q <= vec_exec_status;

            if (vec_exec_status != 16'(CARBON_CAI_STATUS_OK)) begin
              comp_bytes_q <= 32'h0;
              st_q <= ST_COMP_WR;
            end else if (result_to_reg_q) begin
              comp_bytes_q <= 32'h0;
              vec_writeback_q <= 1'b1;
              st_q <= ST_COMP_WR;
            end else begin
              comp_bytes_q <= 32'(vec_count_q) * 32'(VEC_BYTES);
              vec_word_q <= 2'd0;
              st_q <= ST_VEC_RES_WR;
            end
          end

          ST_VEC_RES_WR: begin
            logic [63:0] addr;
            logic [31:0] wdata;
            addr = desc_result_ptr_q +
                   64'(vec_index_q) * 64'(vec_result_step_q) +
                   64'(vec_word_q * 4);
            if (!addr64_ok(addr)) begin
              comp_status_q <= 16'(CARBON_CAI_STATUS_FAULT);
              comp_bytes_q <= 32'h0;
              st_q <= ST_COMP_WR;
            end else begin
              unique case (vec_word_q)
                2'd0: wdata = vec_result_q[31:0];
                2'd1: wdata = vec_result_q[63:32];
                2'd2: wdata = vec_result_q[95:64];
                default: wdata = vec_result_q[127:96];
              endcase
              bus_op_q <= FAB_OP_W'(CARBON_FABRIC_XACT_WRITE);
              bus_addr_q <= addr64_to_fab(addr);
              bus_wdata_q <= wdata;
              bus_wstrb_q <= FAB_STRB_W'({(FAB_STRB_W){1'b1}});
              bus_size_q <= '0;
              bus_attr_q <= DMA_ATTR;
              bus_id_q <= '0;
              st_after_bus_q <= ST_VEC_RES_ADV;
              bus_state_q <= BUS_REQ;
            end
          end

          ST_VEC_RES_ADV: begin
            if (bus_rsp_code_q != FAB_CODE_W'(CARBON_FABRIC_RESP_OK)) begin
              comp_status_q <= 16'(CARBON_CAI_STATUS_FAULT);
              comp_bytes_q <= 32'h0;
              st_q <= ST_COMP_WR;
            end else if (vec_word_q != 2'd3) begin
              vec_word_q <= vec_word_q + 1'b1;
              st_q <= ST_VEC_RES_WR;
            end else begin
              vec_word_q <= 2'd0;
              if (vec_index_q + 1'b1 < vec_count_q) begin
                vec_index_q <= vec_index_q + 1'b1;
                vec_op_idx_q <= '0;
                st_q <= ST_VEC_OP_RD;
              end else begin
                st_q <= ST_COMP_WR;
              end
            end
          end

          ST_RESULT_WR: begin
            int unsigned bytes;
            logic [63:0] v;
            logic do_bus;
            bytes = int'(result_elem_bytes_q);
            v = result_sel_q ? exec_q.res1 : exec_q.res0;
            do_bus = 1'b0;
            if (bytes == 0) begin
              st_q <= ST_COMP_WR;
            end else if (!addr64_ok(result_base_q)) begin
              comp_status_q <= 16'(CARBON_CAI_STATUS_FAULT);
              comp_bytes_q <= '0;
              st_q <= ST_COMP_WR;
            end else begin
              bus_op_q <= FAB_OP_W'(CARBON_FABRIC_XACT_WRITE);
              bus_addr_q <= addr64_to_fab(result_base_q);
              bus_attr_q <= DMA_ATTR;
              bus_id_q <= '0;
              bus_size_q <= '0;
              if (bytes == 8) begin
                bus_wdata_q <= v[31:0];
                bus_wstrb_q <= FAB_STRB_W'({(FAB_STRB_W){1'b1}});
                tmp_lo_q <= v[63:32];
                st_after_bus_q <= ST_RESULT_WR2;
                do_bus = 1'b1;
              end else if (bytes == 4) begin
                bus_wdata_q <= v[31:0];
                bus_wstrb_q <= FAB_STRB_W'({(FAB_STRB_W){1'b1}});
                st_after_bus_q <= ST_RESULT_ADV;
                do_bus = 1'b1;
              end else if (bytes == 2) begin
                bus_wdata_q <= {16'h0000, v[15:0]};
                bus_wstrb_q <= FAB_STRB_W'(4'b0011);
                st_after_bus_q <= ST_RESULT_ADV;
                do_bus = 1'b1;
              end else begin
                comp_status_q <= 16'(CARBON_CAI_STATUS_INVALID_OP);
                comp_bytes_q <= 32'h0;
                st_q <= ST_COMP_WR;
              end
              if (do_bus) bus_state_q <= BUS_REQ;
            end
          end

          ST_RESULT_WR2: begin
            if (bus_rsp_code_q != FAB_CODE_W'(CARBON_FABRIC_RESP_OK)) begin
              comp_status_q <= 16'(CARBON_CAI_STATUS_FAULT);
              comp_bytes_q <= '0;
              st_q <= ST_COMP_WR;
            end else begin
              bus_op_q <= FAB_OP_W'(CARBON_FABRIC_XACT_WRITE);
              bus_addr_q <= addr64_to_fab(result_base_q + 64'd4);
              bus_wdata_q <= tmp_lo_q;
              bus_wstrb_q <= FAB_STRB_W'({(FAB_STRB_W){1'b1}});
              bus_size_q <= '0;
              bus_attr_q <= DMA_ATTR;
              bus_id_q <= '0;
              st_after_bus_q <= ST_RESULT_ADV;
              bus_state_q <= BUS_REQ;
            end
          end

          ST_RESULT_ADV: begin
            if (bus_rsp_code_q != FAB_CODE_W'(CARBON_FABRIC_RESP_OK)) begin
              comp_status_q <= 16'(CARBON_CAI_STATUS_FAULT);
              comp_bytes_q <= 32'h0;
              st_q <= ST_COMP_WR;
            end else if (exec_q.res1_valid && !result_sel_q) begin
              result_sel_q <= 1'b1;
              result_base_q <= desc_result_ptr_q + 64'(result_step_q);
              st_q <= ST_RESULT_WR;
            end else begin
              st_q <= ST_COMP_WR;
            end
          end

          ST_COMP_WR: begin
            // Compute completion record base.
            logic [31:0] idx;
            idx = comp_head_q & cfg_comp_ring_mask;
            comp_addr_q <= cfg_comp_base + (64'(idx) << 4);
            comp_word_q <= 2'd0;
            st_q <= ST_COMP_WR_NEXT;
          end

          ST_COMP_WR_NEXT: begin
            logic [31:0] wdata;
            logic [63:0] addr;
            addr = comp_addr_q + 64'(comp_word_q * 4);
            if (!addr64_ok(addr)) begin
              // Can't write completion -> drop.
              st_q <= ST_FINISH;
            end else begin
              unique case (comp_word_q)
                2'd0: wdata = desc_tag_q;
                2'd1: wdata = {11'h0, (exec_valid_q ? exec_q.exc_flags : 5'h0), comp_status_q};
                2'd2: wdata = comp_bytes_q;
                default: wdata = 32'h0000_0000;
              endcase

              bus_op_q <= FAB_OP_W'(CARBON_FABRIC_XACT_WRITE);
              bus_addr_q <= addr64_to_fab(addr);
              bus_wdata_q <= wdata;
              bus_wstrb_q <= FAB_STRB_W'({(FAB_STRB_W){1'b1}});
              bus_size_q <= '0;
              bus_attr_q <= DMA_ATTR;
              bus_id_q <= '0;
              st_after_bus_q <= ST_COMP_WR_ADV;
              bus_state_q <= BUS_REQ;
            end
          end

          ST_COMP_WR_ADV: begin
            if (bus_rsp_code_q != FAB_CODE_W'(CARBON_FABRIC_RESP_OK)) begin
              st_q <= ST_FINISH;
            end else if (comp_word_q == 2'd3) begin
              st_q <= ST_FINISH;
            end else begin
              comp_word_q <= comp_word_q + 1'b1;
              st_q <= ST_COMP_WR_NEXT;
            end
          end

          ST_FINISH: begin
            // Advance rings and pulse completion.
            submit_head_q <= submit_head_q + 1'b1;
            if (pending_q != 0) pending_q <= pending_q - 1'b1;
            comp_head_q <= comp_head_q + 1'b1;
            cai.comp_doorbell <= 1'b1;
            cai.comp_irq <= cfg_comp_irq_en;
            exec_valid_q <= 1'b0;
            vec_exec_valid_q <= 1'b0;
            vec_writeback_q <= 1'b0;
            st_q <= ST_IDLE;
          end

          default: st_q <= ST_IDLE;
        endcase
      end

      // Completion write sequencing handled by ST_COMP_WR_ADV.
    end
  end

endmodule : am9513_cai_engine
