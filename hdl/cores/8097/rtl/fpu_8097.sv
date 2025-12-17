// Project Carbon - 8097 FPU (x87-like, v1.0)
// fpu_8097: CSR-driven FPU with x87-style stack semantics (FP64 internal).
//
// Notes (v1):
// - Arithmetic uses shared bounded-accuracy helpers (am9513_math_pkg) for determinism.
// - Stack tags/NaN payload propagation are simplified; behavior is deterministic.
// - CAI integration is deferred; CSR window is the control surface for v1 TBs.

module fpu_8097 (
    input logic clk,
    input logic rst_n,

    csr_if.slave csr,
    fabric_if.master mem_if
);
  import carbon_arch_pkg::*;
  import am9513_math_pkg::*;
  import fpu_8097_pkg::*;

  localparam int unsigned FAB_ADDR_W = $bits(mem_if.req_addr);
  localparam int unsigned FAB_DATA_W = $bits(mem_if.req_wdata);
  localparam int unsigned FAB_STRB_W = $bits(mem_if.req_wstrb);
  localparam int unsigned FAB_OP_W   = $bits(mem_if.req_op);
  localparam int unsigned FAB_SIZE_W = $bits(mem_if.req_size);
  localparam int unsigned FAB_ATTR_W = $bits(mem_if.req_attr);
  localparam int unsigned FAB_ID_W   = $bits(mem_if.req_id);
  localparam int unsigned FAB_CODE_W = $bits(mem_if.rsp_code);

  localparam int unsigned CSR_ADDR_W = $bits(csr.req_addr);
  localparam int unsigned CSR_DATA_W = $bits(csr.req_wdata);
  localparam int unsigned CSR_PRIV_W = $bits(csr.req_priv);

  localparam logic [FAB_ATTR_W-1:0] MEM_ATTR =
      FAB_ATTR_W'(CARBON_FABRIC_ATTR_CACHEABLE_MASK);

  // --------------------------------------------------------------------------
  // CSR interface response registers
  // --------------------------------------------------------------------------
  logic csr_rsp_valid_q;
  logic [CSR_DATA_W-1:0] csr_rsp_rdata_q;
  logic csr_rsp_fault_q;
  logic csr_rsp_side_q;

  assign csr.req_ready       = !csr_rsp_valid_q;
  assign csr.rsp_valid       = csr_rsp_valid_q;
  assign csr.rsp_rdata       = csr_rsp_rdata_q;
  assign csr.rsp_fault       = csr_rsp_fault_q;
  assign csr.rsp_side_effect = csr_rsp_side_q;

  wire csr_req_fire = csr.req_valid && csr.req_ready;
  wire csr_rsp_fire = csr.rsp_valid && csr.rsp_ready;

  // --------------------------------------------------------------------------
  // Core state
  // --------------------------------------------------------------------------
  logic [7:0]  tier_q;
  logic [7:0]  modeflags_q;
  logic [15:0] ctrl_word_q;
  logic [15:0] status_word_q;

  logic        busy_q;
  logic [7:0]  fault_code_q;

  logic [63:0] mem_addr_q;
  logic [31:0] push_lo_q;

  // x87-like stack: TOP pointer + depth counter.
  logic [2:0]  top_q;
  logic [3:0]  depth_q;  // 0..8
  logic [63:0] st_q [8];

  // P7 regfile mode (F0..F15)
  logic [3:0]  rf_index_q;
  logic [63:0] rf_q [16];

  wire tier_p0 = (tier_q == 8'(CARBON_X86_DERIVED_TIER_P0_I8086_8087));
  wire tier_p7 = (tier_q == 8'(CARBON_X86_DERIVED_TIER_P7_TURBO_UNLIMITED));
  wire tier_supported = tier_p0 || tier_p7;
  wire turbo_allowed = tier_p7 && !modeflags_q[CARBON_MODEFLAG_STRICT_BIT];

  function automatic logic [1:0] rm_from_ctrl(input logic [15:0] cw);
    logic [1:0] rc;
    begin
      rc = cw[11:10]; // x87 RC encoding
      unique case (rc)
        2'b01: rm_from_ctrl = 2'(CARBON_RND_RM); // -inf
        2'b10: rm_from_ctrl = 2'(CARBON_RND_RP); // +inf
        2'b11: rm_from_ctrl = 2'(CARBON_RND_RZ); // 0
        default: rm_from_ctrl = 2'(CARBON_RND_RN);
      endcase
    end
  endfunction

  function automatic logic [2:0] st_idx(input logic [2:0] top, input int unsigned i);
    begin
      st_idx = top + 3'(i[2:0]);
    end
  endfunction

  function automatic logic fp64_is_nan(input logic [63:0] v);
    begin
      fp64_is_nan = (v[62:52] == 11'h7FF) && (v[51:0] != 0);
    end
  endfunction

  function automatic logic [63:0] fp64_order_key(input logic [63:0] v);
    begin
      fp64_order_key = v[63] ? ~v : {1'b1, v[62:0]};
    end
  endfunction

  // --------------------------------------------------------------------------
  // Command staging (from CSR writes)
  // --------------------------------------------------------------------------
  logic        cmd_pending_q;
  logic [7:0]  cmd_op_q;

  logic        rfop_pending_q;
  logic [31:0] rfop_word_q;

  // --------------------------------------------------------------------------
  // Fabric bus micro-engine (single outstanding)
  // --------------------------------------------------------------------------
  typedef enum logic [3:0] {
    ST_RESET       = 4'd0,
    ST_IDLE        = 4'd1,
    ST_EXEC_IMM    = 4'd2,
    ST_FLD_FETCH_HI = 4'd3,
    ST_FLD_DONE    = 4'd4,
    ST_FSTP_WRITE_HI = 4'd5,
    ST_FSTP_DONE   = 4'd6,
    ST_RF_EXEC     = 4'd7,
    ST_BUS_REQ     = 4'd8,
    ST_BUS_RSP     = 4'd9
  } state_e;

  state_e state_q;
  state_e state_after_bus_q;

  logic [FAB_OP_W-1:0]   bus_op_q;
  logic [FAB_ADDR_W-1:0] bus_addr_q;
  logic [FAB_DATA_W-1:0] bus_wdata_q;
  logic [FAB_STRB_W-1:0] bus_wstrb_q;
  logic [FAB_SIZE_W-1:0] bus_size_q;
  logic [FAB_ATTR_W-1:0] bus_attr_q;
  logic [FAB_ID_W-1:0]   bus_id_q;

  typedef enum logic [1:0] {
    DEST_NONE = 2'd0,
    DEST_LO   = 2'd1,
    DEST_HI   = 2'd2
  } bus_dest_e;

  bus_dest_e bus_dest_q;
  logic [31:0] rd_lo_q;
  logic [31:0] rd_hi_q;

  wire bus_req_fire = mem_if.req_valid && mem_if.req_ready;
  wire bus_rsp_fire = mem_if.rsp_valid && mem_if.rsp_ready;

  assign mem_if.req_valid = (state_q == ST_BUS_REQ);
  assign mem_if.req_op    = bus_op_q;
  assign mem_if.req_addr  = bus_addr_q;
  assign mem_if.req_wdata = bus_wdata_q;
  assign mem_if.req_wstrb = bus_wstrb_q;
  assign mem_if.req_size  = bus_size_q;
  assign mem_if.req_attr  = bus_attr_q;
  assign mem_if.req_id    = bus_id_q;

  assign mem_if.rsp_ready = (state_q == ST_BUS_RSP);

  // --------------------------------------------------------------------------
  // Sequential logic
  // --------------------------------------------------------------------------
  integer i;
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      csr_rsp_valid_q <= 1'b0;
      csr_rsp_rdata_q <= '0;
      csr_rsp_fault_q <= 1'b0;
      csr_rsp_side_q  <= 1'b0;

      tier_q     <= 8'(CARBON_X86_DERIVED_TIER_P0_I8086_8087);
      modeflags_q <= 8'(CARBON_MODEFLAG_STRICT_MASK);
      ctrl_word_q <= 16'h037F; // x87 reset defaults (subset)
      status_word_q <= 16'h0000;

      busy_q       <= 1'b0;
      fault_code_q <= FPU8097_FAULT_NONE;

      mem_addr_q <= 64'd0;
      push_lo_q  <= 32'd0;

      top_q   <= 3'd0;
      depth_q <= 4'd0;
      for (i = 0; i < 8; i++) st_q[i] <= 64'd0;

      rf_index_q <= 4'd0;
      for (i = 0; i < 16; i++) rf_q[i] <= 64'd0;

      cmd_pending_q <= 1'b0;
      cmd_op_q      <= 8'd0;
      rfop_pending_q <= 1'b0;
      rfop_word_q    <= 32'd0;

      state_q <= ST_RESET;
      state_after_bus_q <= ST_IDLE;
      bus_op_q   <= '0;
      bus_addr_q <= '0;
      bus_wdata_q <= '0;
      bus_wstrb_q <= '0;
      bus_size_q <= '0;
      bus_attr_q <= MEM_ATTR;
      bus_id_q <= '0;
      bus_dest_q <= DEST_NONE;
      rd_lo_q <= 32'd0;
      rd_hi_q <= 32'd0;
    end else begin
      // Keep TOP bits reflected in status_word (subset).
      status_word_q[FPU8097_SW_TOP_LSB+2 -: 3] <= top_q;

      if (csr_rsp_fire) csr_rsp_valid_q <= 1'b0;

      // --------------------------------------------------------------------
      // CSR request handling (one outstanding response)
      // --------------------------------------------------------------------
      if (csr_req_fire) begin
        csr_rsp_valid_q <= 1'b1;
        csr_rsp_fault_q <= 1'b0;
        csr_rsp_side_q  <= csr.req_write;
        csr_rsp_rdata_q <= '0;

        unique case (csr.req_addr)
          CARBON_CSR_8097_ID: begin
            if (!csr.req_write) csr_rsp_rdata_q <= 32'h3830_3937; // "8097"
            else csr_rsp_fault_q <= 1'b1;
          end

          CARBON_CSR_8097_TIER: begin
            if (!csr.req_write) begin
              csr_rsp_rdata_q[7:0] <= tier_q;
            end else begin
              if (csr.req_priv < CSR_PRIV_W'(1)) begin
                csr_rsp_fault_q <= 1'b1;
              end else if (!((csr.req_wdata[7:0] == 8'(CARBON_X86_DERIVED_TIER_P0_I8086_8087)) ||
                             (csr.req_wdata[7:0] == 8'(CARBON_X86_DERIVED_TIER_P7_TURBO_UNLIMITED)))) begin
                csr_rsp_fault_q <= 1'b1;
                fault_code_q <= FPU8097_FAULT_BAD_TIER;
              end else begin
                tier_q <= csr.req_wdata[7:0];
              end
            end
          end

          CARBON_CSR_8097_MODEFLAGS: begin
            if (!csr.req_write) begin
              csr_rsp_rdata_q[7:0] <= modeflags_q;
            end else begin
              if (csr.req_priv < CSR_PRIV_W'(1)) begin
                csr_rsp_fault_q <= 1'b1;
              end else begin
                modeflags_q <= csr.req_wdata[7:0] & 8'(CARBON_MODEFLAG_STRICT_MASK | CARBON_MODEFLAG_INTMASK_MASK);
              end
            end
          end

          CARBON_CSR_8097_STATUS: begin
            if (!csr.req_write) begin
              csr_rsp_rdata_q[0] <= busy_q;
              csr_rsp_rdata_q[1] <= (fault_code_q != FPU8097_FAULT_NONE);
              csr_rsp_rdata_q[5:2] <= depth_q;
              csr_rsp_rdata_q[8:6] <= top_q;
              csr_rsp_rdata_q[16 +: 8] <= fault_code_q;
              csr_rsp_rdata_q[24] <= turbo_allowed;
            end else begin
              csr_rsp_fault_q <= 1'b1;
            end
          end

          CARBON_CSR_8097_CTRL_WORD: begin
            if (!csr.req_write) begin
              csr_rsp_rdata_q[15:0] <= ctrl_word_q;
            end else begin
              if (csr.req_priv < CSR_PRIV_W'(1)) csr_rsp_fault_q <= 1'b1;
              else ctrl_word_q <= csr.req_wdata[15:0];
            end
          end

          CARBON_CSR_8097_STATUS_WORD: begin
            if (!csr.req_write) csr_rsp_rdata_q[15:0] <= status_word_q;
            else csr_rsp_fault_q <= 1'b1;
          end

          CARBON_CSR_8097_MEM_ADDR_LO: begin
            if (!csr.req_write) csr_rsp_rdata_q <= mem_addr_q[31:0];
            else mem_addr_q[31:0] <= csr.req_wdata;
          end
          CARBON_CSR_8097_MEM_ADDR_HI: begin
            if (!csr.req_write) csr_rsp_rdata_q <= mem_addr_q[63:32];
            else mem_addr_q[63:32] <= csr.req_wdata;
          end

          CARBON_CSR_8097_PUSH_LO: begin
            if (csr.req_write) begin
              push_lo_q <= csr.req_wdata;
            end else begin
              csr_rsp_fault_q <= 1'b1;
            end
          end

          CARBON_CSR_8097_PUSH_HI: begin
            if (csr.req_write) begin
              if (busy_q) begin
                csr_rsp_fault_q <= 1'b1;
                fault_code_q <= FPU8097_FAULT_BUSY;
              end else if (depth_q == 4'd8) begin
                csr_rsp_fault_q <= 1'b1;
                fault_code_q <= FPU8097_FAULT_STACK_OVERFLOW;
                status_word_q[FPU8097_SW_SF] <= 1'b1;
              end else begin
                top_q <= top_q - 3'd1;
                st_q[top_q - 3'd1] <= {csr.req_wdata, push_lo_q};
                depth_q <= depth_q + 4'd1;
              end
            end else begin
              csr_rsp_fault_q <= 1'b1;
            end
          end

          CARBON_CSR_8097_POP_LO: begin
            if (!csr.req_write) begin
              if (depth_q == 0) begin
                csr_rsp_rdata_q <= 32'h0000_0000;
                csr_rsp_fault_q <= 1'b1;
                fault_code_q <= FPU8097_FAULT_STACK_UNDERFLOW;
                status_word_q[FPU8097_SW_SF] <= 1'b1;
              end else begin
                csr_rsp_rdata_q <= st_q[top_q][31:0];
              end
            end else begin
              csr_rsp_fault_q <= 1'b1;
            end
          end

          CARBON_CSR_8097_POP_HI: begin
            if (!csr.req_write) begin
              csr_rsp_side_q <= 1'b1;
              if (depth_q == 0) begin
                csr_rsp_rdata_q <= 32'h0000_0000;
                csr_rsp_fault_q <= 1'b1;
                fault_code_q <= FPU8097_FAULT_STACK_UNDERFLOW;
                status_word_q[FPU8097_SW_SF] <= 1'b1;
              end else begin
                csr_rsp_rdata_q <= st_q[top_q][63:32];
                top_q <= top_q + 3'd1;
                depth_q <= depth_q - 4'd1;
              end
            end else begin
              csr_rsp_fault_q <= 1'b1;
            end
          end

          CARBON_CSR_8097_CMD: begin
            if (csr.req_write) begin
              if (!tier_supported) begin
                csr_rsp_fault_q <= 1'b1;
                fault_code_q <= FPU8097_FAULT_BAD_TIER;
              end else if (busy_q || cmd_pending_q || rfop_pending_q) begin
                csr_rsp_fault_q <= 1'b1;
                fault_code_q <= FPU8097_FAULT_BUSY;
              end else begin
                cmd_pending_q <= 1'b1;
                cmd_op_q <= csr.req_wdata[7:0];
              end
            end else begin
              csr_rsp_fault_q <= 1'b1;
            end
          end

          CARBON_CSR_8097_RF_INDEX: begin
            if (!csr.req_write) begin
              csr_rsp_rdata_q[3:0] <= rf_index_q;
            end else begin
              if (csr.req_priv < CSR_PRIV_W'(1)) begin
                csr_rsp_fault_q <= 1'b1;
              end else if (!turbo_allowed) begin
                csr_rsp_fault_q <= 1'b1;
                fault_code_q <= FPU8097_FAULT_TURBO_DENIED;
              end else begin
                rf_index_q <= csr.req_wdata[3:0];
              end
            end
          end

          CARBON_CSR_8097_RF_DATA_LO: begin
            if (!turbo_allowed) begin
              csr_rsp_fault_q <= 1'b1;
              fault_code_q <= FPU8097_FAULT_TURBO_DENIED;
            end else if (!csr.req_write) begin
              csr_rsp_rdata_q <= rf_q[rf_index_q][31:0];
            end else begin
              if (csr.req_priv < CSR_PRIV_W'(1)) csr_rsp_fault_q <= 1'b1;
              else rf_q[rf_index_q][31:0] <= csr.req_wdata;
            end
          end

          CARBON_CSR_8097_RF_DATA_HI: begin
            if (!turbo_allowed) begin
              csr_rsp_fault_q <= 1'b1;
              fault_code_q <= FPU8097_FAULT_TURBO_DENIED;
            end else if (!csr.req_write) begin
              csr_rsp_rdata_q <= rf_q[rf_index_q][63:32];
            end else begin
              if (csr.req_priv < CSR_PRIV_W'(1)) csr_rsp_fault_q <= 1'b1;
              else rf_q[rf_index_q][63:32] <= csr.req_wdata;
            end
          end

          CARBON_CSR_8097_RF_OP: begin
            if (csr.req_write) begin
              if (csr.req_priv < CSR_PRIV_W'(1)) begin
                csr_rsp_fault_q <= 1'b1;
              end else if (!turbo_allowed) begin
                csr_rsp_fault_q <= 1'b1;
                fault_code_q <= FPU8097_FAULT_TURBO_DENIED;
              end else if (busy_q || cmd_pending_q || rfop_pending_q) begin
                csr_rsp_fault_q <= 1'b1;
                fault_code_q <= FPU8097_FAULT_BUSY;
              end else begin
                rfop_pending_q <= 1'b1;
                rfop_word_q <= csr.req_wdata;
              end
            end else begin
              csr_rsp_fault_q <= 1'b1;
            end
          end

          default: begin
            csr_rsp_fault_q <= 1'b1;
          end
        endcase
      end

      // --------------------------------------------------------------------
      // Execution state machine
      // --------------------------------------------------------------------
      unique case (state_q)
        ST_RESET: begin
          state_q <= ST_IDLE;
        end

        ST_IDLE: begin
          if (cmd_pending_q) begin
            cmd_pending_q <= 1'b0;
            busy_q <= 1'b1;
            state_q <= ST_EXEC_IMM;
          end else if (rfop_pending_q) begin
            rfop_pending_q <= 1'b0;
            busy_q <= 1'b1;
            state_q <= ST_RF_EXEC;
          end
        end

        ST_EXEC_IMM: begin
          logic [1:0] rm;
          logic [63:0] a;
          logic [63:0] b;
          am9513_fp64_t r;
          logic [7:0] op;
          op = cmd_op_q;
          rm = rm_from_ctrl(ctrl_word_q);

          if (op == FPU8097_CMD_NOP) begin
            busy_q <= 1'b0;
            state_q <= ST_IDLE;
          end else if ((op == FPU8097_CMD_FADD) || (op == FPU8097_CMD_FSUB) ||
                       (op == FPU8097_CMD_FMUL) || (op == FPU8097_CMD_FDIV) ||
                       (op == FPU8097_CMD_FCOM) || (op == FPU8097_CMD_FCOMP)) begin
            if (depth_q < 2) begin
              fault_code_q <= FPU8097_FAULT_STACK_UNDERFLOW;
              status_word_q[FPU8097_SW_SF] <= 1'b1;
              busy_q <= 1'b0;
              state_q <= ST_IDLE;
            end else begin
              a = st_q[st_idx(top_q, 0)];
              b = st_q[st_idx(top_q, 1)];
              if ((op == FPU8097_CMD_FCOM) || (op == FPU8097_CMD_FCOMP)) begin
                logic [63:0] ka;
                logic [63:0] kb;
                logic unordered;
                logic eqz;
                unordered = fp64_is_nan(a) || fp64_is_nan(b);
                eqz = (a[62:0] == 0) && (b[62:0] == 0);
                status_word_q[FPU8097_SW_C0] <= 1'b0;
                status_word_q[FPU8097_SW_C2] <= 1'b0;
                status_word_q[FPU8097_SW_C3] <= 1'b0;
                if (unordered) begin
                  status_word_q[FPU8097_SW_C0] <= 1'b1;
                  status_word_q[FPU8097_SW_C2] <= 1'b1;
                  status_word_q[FPU8097_SW_C3] <= 1'b1;
                  status_word_q[FPU8097_SW_IE] <= 1'b1;
                end else if (eqz || (a == b)) begin
                  status_word_q[FPU8097_SW_C3] <= 1'b1;
                end else begin
                  ka = fp64_order_key(a);
                  kb = fp64_order_key(b);
                  if (ka < kb) status_word_q[FPU8097_SW_C0] <= 1'b1;
                end

                if (op == FPU8097_CMD_FCOMP) begin
                  top_q <= top_q + 3'd1;
                  depth_q <= depth_q - 4'd1;
                end

                busy_q <= 1'b0;
                state_q <= ST_IDLE;
              end else begin
                unique case (op)
                  FPU8097_CMD_FADD: r = fp64_add(a, b, rm);
                  FPU8097_CMD_FSUB: r = fp64_sub(a, b, rm);
                  FPU8097_CMD_FMUL: r = fp64_mul(a, b, rm);
                  default: r = fp64_div(a, b, rm);
                endcase

                st_q[st_idx(top_q, 0)] <= r.v;
                status_word_q[FPU8097_SW_IE] <= status_word_q[FPU8097_SW_IE] | (| (r.flags & AM9513_F_NV));
                status_word_q[FPU8097_SW_ZE] <= status_word_q[FPU8097_SW_ZE] | (| (r.flags & AM9513_F_DZ));
                status_word_q[FPU8097_SW_OE] <= status_word_q[FPU8097_SW_OE] | (| (r.flags & AM9513_F_OF));
                status_word_q[FPU8097_SW_UE] <= status_word_q[FPU8097_SW_UE] | (| (r.flags & AM9513_F_UF));
                status_word_q[FPU8097_SW_PE] <= status_word_q[FPU8097_SW_PE] | (| (r.flags & AM9513_F_NX));
                busy_q <= 1'b0;
                state_q <= ST_IDLE;
              end
            end
          end else if (op == FPU8097_CMD_FSQRT) begin
            if (depth_q < 1) begin
              fault_code_q <= FPU8097_FAULT_STACK_UNDERFLOW;
              status_word_q[FPU8097_SW_SF] <= 1'b1;
              busy_q <= 1'b0;
              state_q <= ST_IDLE;
            end else begin
              a = st_q[st_idx(top_q, 0)];
              r = fp64_sqrt(a, rm);
              st_q[st_idx(top_q, 0)] <= r.v;
              status_word_q[FPU8097_SW_IE] <= status_word_q[FPU8097_SW_IE] | (| (r.flags & AM9513_F_NV));
              status_word_q[FPU8097_SW_ZE] <= status_word_q[FPU8097_SW_ZE] | (| (r.flags & AM9513_F_DZ));
              status_word_q[FPU8097_SW_OE] <= status_word_q[FPU8097_SW_OE] | (| (r.flags & AM9513_F_OF));
              status_word_q[FPU8097_SW_UE] <= status_word_q[FPU8097_SW_UE] | (| (r.flags & AM9513_F_UF));
              status_word_q[FPU8097_SW_PE] <= status_word_q[FPU8097_SW_PE] | (| (r.flags & AM9513_F_NX));
              busy_q <= 1'b0;
              state_q <= ST_IDLE;
            end
          end else if (op == FPU8097_CMD_FLD_MEM64) begin
            if (depth_q == 4'd8) begin
              fault_code_q <= FPU8097_FAULT_STACK_OVERFLOW;
              status_word_q[FPU8097_SW_SF] <= 1'b1;
              busy_q <= 1'b0;
              state_q <= ST_IDLE;
            end else begin
              bus_op_q <= FAB_OP_W'(CARBON_FABRIC_XACT_READ);
              bus_addr_q <= FAB_ADDR_W'(mem_addr_q[FAB_ADDR_W-1:0]);
              bus_wdata_q <= '0;
              bus_wstrb_q <= '0;
              bus_size_q <= '0;
              bus_attr_q <= MEM_ATTR;
              bus_id_q <= '0;
              bus_dest_q <= DEST_LO;
              state_after_bus_q <= ST_FLD_FETCH_HI;
              state_q <= ST_BUS_REQ;
            end
          end else if (op == FPU8097_CMD_FSTP_MEM64) begin
            if (depth_q == 0) begin
              fault_code_q <= FPU8097_FAULT_STACK_UNDERFLOW;
              status_word_q[FPU8097_SW_SF] <= 1'b1;
              busy_q <= 1'b0;
              state_q <= ST_IDLE;
            end else begin
              bus_op_q <= FAB_OP_W'(CARBON_FABRIC_XACT_WRITE);
              bus_addr_q <= FAB_ADDR_W'(mem_addr_q[FAB_ADDR_W-1:0]);
              bus_wdata_q <= FAB_DATA_W'({{(FAB_DATA_W-32){1'b0}}, st_q[st_idx(top_q, 0)][31:0]});
              bus_wstrb_q <= FAB_STRB_W'({{(FAB_STRB_W-4){1'b0}}, 4'hF});
              bus_size_q <= '0;
              bus_attr_q <= MEM_ATTR;
              bus_id_q <= '0;
              bus_dest_q <= DEST_NONE;
              state_after_bus_q <= ST_FSTP_WRITE_HI;
              state_q <= ST_BUS_REQ;
            end
          end else begin
            fault_code_q <= FPU8097_FAULT_ILLEGAL_CMD;
            busy_q <= 1'b0;
            state_q <= ST_IDLE;
          end

          status_word_q[FPU8097_SW_ES] <=
              status_word_q[FPU8097_SW_IE] |
              status_word_q[FPU8097_SW_ZE] |
              status_word_q[FPU8097_SW_OE] |
              status_word_q[FPU8097_SW_UE] |
              status_word_q[FPU8097_SW_PE] |
              status_word_q[FPU8097_SW_SF];
        end

        ST_FLD_FETCH_HI: begin
          bus_op_q <= FAB_OP_W'(CARBON_FABRIC_XACT_READ);
          bus_addr_q <= FAB_ADDR_W'((mem_addr_q[FAB_ADDR_W-1:0]) + FAB_ADDR_W'(32'd4));
          bus_wdata_q <= '0;
          bus_wstrb_q <= '0;
          bus_size_q <= '0;
          bus_attr_q <= MEM_ATTR;
          bus_id_q <= '0;
          bus_dest_q <= DEST_HI;
          state_after_bus_q <= ST_FLD_DONE;
          state_q <= ST_BUS_REQ;
        end

        ST_FLD_DONE: begin
          top_q <= top_q - 3'd1;
          st_q[top_q - 3'd1] <= {rd_hi_q, rd_lo_q};
          depth_q <= depth_q + 4'd1;
          busy_q <= 1'b0;
          state_q <= ST_IDLE;
        end

        ST_FSTP_WRITE_HI: begin
          bus_op_q <= FAB_OP_W'(CARBON_FABRIC_XACT_WRITE);
          bus_addr_q <= FAB_ADDR_W'((mem_addr_q[FAB_ADDR_W-1:0]) + FAB_ADDR_W'(32'd4));
          bus_wdata_q <= FAB_DATA_W'({{(FAB_DATA_W-32){1'b0}}, st_q[st_idx(top_q, 0)][63:32]});
          bus_wstrb_q <= FAB_STRB_W'({{(FAB_STRB_W-4){1'b0}}, 4'hF});
          bus_size_q <= '0;
          bus_attr_q <= MEM_ATTR;
          bus_id_q <= '0;
          bus_dest_q <= DEST_NONE;
          state_after_bus_q <= ST_FSTP_DONE;
          state_q <= ST_BUS_REQ;
        end

        ST_FSTP_DONE: begin
          top_q <= top_q + 3'd1;
          depth_q <= depth_q - 4'd1;
          busy_q <= 1'b0;
          state_q <= ST_IDLE;
        end

        ST_RF_EXEC: begin
          logic [1:0] rm;
          logic [3:0] op;
          logic [3:0] dst;
          logic [3:0] a_i;
          logic [3:0] b_i;
          am9513_fp64_t r;

          rm = rm_from_ctrl(ctrl_word_q);
          op  = rfop_word_q[3:0];
          dst = rfop_word_q[7:4];
          a_i = rfop_word_q[11:8];
          b_i = rfop_word_q[15:12];

          unique case (op)
            FPU8097_RFOP_MOV: begin
              rf_q[dst] <= rf_q[a_i];
            end
            FPU8097_RFOP_ADD: begin
              r = fp64_add(rf_q[a_i], rf_q[b_i], rm);
              rf_q[dst] <= r.v;
              status_word_q[FPU8097_SW_IE] <= status_word_q[FPU8097_SW_IE] | (| (r.flags & AM9513_F_NV));
              status_word_q[FPU8097_SW_ZE] <= status_word_q[FPU8097_SW_ZE] | (| (r.flags & AM9513_F_DZ));
              status_word_q[FPU8097_SW_OE] <= status_word_q[FPU8097_SW_OE] | (| (r.flags & AM9513_F_OF));
              status_word_q[FPU8097_SW_UE] <= status_word_q[FPU8097_SW_UE] | (| (r.flags & AM9513_F_UF));
              status_word_q[FPU8097_SW_PE] <= status_word_q[FPU8097_SW_PE] | (| (r.flags & AM9513_F_NX));
            end
            FPU8097_RFOP_MUL: begin
              r = fp64_mul(rf_q[a_i], rf_q[b_i], rm);
              rf_q[dst] <= r.v;
              status_word_q[FPU8097_SW_IE] <= status_word_q[FPU8097_SW_IE] | (| (r.flags & AM9513_F_NV));
              status_word_q[FPU8097_SW_ZE] <= status_word_q[FPU8097_SW_ZE] | (| (r.flags & AM9513_F_DZ));
              status_word_q[FPU8097_SW_OE] <= status_word_q[FPU8097_SW_OE] | (| (r.flags & AM9513_F_OF));
              status_word_q[FPU8097_SW_UE] <= status_word_q[FPU8097_SW_UE] | (| (r.flags & AM9513_F_UF));
              status_word_q[FPU8097_SW_PE] <= status_word_q[FPU8097_SW_PE] | (| (r.flags & AM9513_F_NX));
            end
            FPU8097_RFOP_DIV: begin
              r = fp64_div(rf_q[a_i], rf_q[b_i], rm);
              rf_q[dst] <= r.v;
              status_word_q[FPU8097_SW_IE] <= status_word_q[FPU8097_SW_IE] | (| (r.flags & AM9513_F_NV));
              status_word_q[FPU8097_SW_ZE] <= status_word_q[FPU8097_SW_ZE] | (| (r.flags & AM9513_F_DZ));
              status_word_q[FPU8097_SW_OE] <= status_word_q[FPU8097_SW_OE] | (| (r.flags & AM9513_F_OF));
              status_word_q[FPU8097_SW_UE] <= status_word_q[FPU8097_SW_UE] | (| (r.flags & AM9513_F_UF));
              status_word_q[FPU8097_SW_PE] <= status_word_q[FPU8097_SW_PE] | (| (r.flags & AM9513_F_NX));
            end
            FPU8097_RFOP_SQRT: begin
              r = fp64_sqrt(rf_q[a_i], rm);
              rf_q[dst] <= r.v;
              status_word_q[FPU8097_SW_IE] <= status_word_q[FPU8097_SW_IE] | (| (r.flags & AM9513_F_NV));
              status_word_q[FPU8097_SW_ZE] <= status_word_q[FPU8097_SW_ZE] | (| (r.flags & AM9513_F_DZ));
              status_word_q[FPU8097_SW_OE] <= status_word_q[FPU8097_SW_OE] | (| (r.flags & AM9513_F_OF));
              status_word_q[FPU8097_SW_UE] <= status_word_q[FPU8097_SW_UE] | (| (r.flags & AM9513_F_UF));
              status_word_q[FPU8097_SW_PE] <= status_word_q[FPU8097_SW_PE] | (| (r.flags & AM9513_F_NX));
            end
            default: begin
              fault_code_q <= FPU8097_FAULT_ILLEGAL_CMD;
            end
          endcase

          status_word_q[FPU8097_SW_ES] <=
              status_word_q[FPU8097_SW_IE] |
              status_word_q[FPU8097_SW_ZE] |
              status_word_q[FPU8097_SW_OE] |
              status_word_q[FPU8097_SW_UE] |
              status_word_q[FPU8097_SW_PE] |
              status_word_q[FPU8097_SW_SF];

          busy_q <= 1'b0;
          state_q <= ST_IDLE;
        end

        ST_BUS_REQ: begin
          if (bus_req_fire) begin
            state_q <= ST_BUS_RSP;
          end
        end

        ST_BUS_RSP: begin
          if (bus_rsp_fire) begin
            if (mem_if.rsp_code != FAB_CODE_W'(CARBON_FABRIC_RESP_OK)) begin
              fault_code_q <= FPU8097_FAULT_MEM;
              busy_q <= 1'b0;
              state_q <= ST_IDLE;
            end else begin
              unique case (bus_dest_q)
                DEST_LO: rd_lo_q <= mem_if.rsp_rdata[31:0];
                DEST_HI: rd_hi_q <= mem_if.rsp_rdata[31:0];
                default: begin end
              endcase
              state_q <= state_after_bus_q;
            end
          end
        end

        default: begin
          state_q <= ST_IDLE;
          busy_q <= 1'b0;
        end
      endcase
    end
  end

endmodule : fpu_8097

