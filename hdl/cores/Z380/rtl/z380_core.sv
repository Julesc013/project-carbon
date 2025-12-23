// Project Carbon - Z380 core (Z380-class)
// z380_core: In-order Z380-class core with strict legacy personalities.

module z380_core #(
    parameter int unsigned MODESTACK_DEPTH = carbon_arch_pkg::CARBON_MODESTACK_RECOMMENDED_DEPTH
) (
    input logic clk,
    input logic rst_n,

    fabric_if.master mem_if,
    fabric_if.master io_if,

    irq_if.sink irq,
    csr_if.slave csr,
    dbg_if.core dbg
);
  import carbon_arch_pkg::*;
  import z85_regfile_pkg::*;
  import z85_decode_pkg::*;
  import z85_flags_pkg::*;

  localparam int unsigned FAB_ADDR_W = $bits(mem_if.req_addr);
  localparam int unsigned FAB_DATA_W = $bits(mem_if.req_wdata);
  localparam int unsigned FAB_STRB_W = $bits(mem_if.req_wstrb);
  localparam int unsigned FAB_OP_W   = $bits(mem_if.req_op);
  localparam int unsigned FAB_SIZE_W = $bits(mem_if.req_size);
  localparam int unsigned FAB_ATTR_W = $bits(mem_if.req_attr);
  localparam int unsigned FAB_ID_W   = $bits(mem_if.req_id);
  localparam int unsigned FAB_CODE_W = $bits(mem_if.rsp_code);

  localparam int unsigned IRQ_VEC_W  = $bits(irq.irq_vector);

`ifndef SYNTHESIS
  initial begin
    if (IRQ_VEC_W < 8) $fatal(1, "z380_core: irq_if vector width must be >= 8");
    if (MODESTACK_DEPTH < CARBON_MODESTACK_MIN_DEPTH) begin
      $fatal(1, "z380_core: MODESTACK_DEPTH must be >= CARBON_MODESTACK_MIN_DEPTH");
    end
  end
`endif

  localparam logic [FAB_ATTR_W-1:0] MEM_ATTR =
      FAB_ATTR_W'(CARBON_FABRIC_ATTR_CACHEABLE_MASK);
  localparam logic [FAB_ATTR_W-1:0] IO_ATTR =
      FAB_ATTR_W'(CARBON_FABRIC_ATTR_ORDERED_MASK | CARBON_FABRIC_ATTR_IO_SPACE_MASK);
  localparam int unsigned MD_SP_W =
      (MODESTACK_DEPTH < 2) ? 1 : $clog2(MODESTACK_DEPTH + 1);

  // --------------------------------------------------------------------------
  // Core-local trap causes (implementation-defined)
  // --------------------------------------------------------------------------
  localparam logic [31:0] Z380_CAUSE_ILLEGAL_INSN = 32'h0000_0001;
  localparam logic [31:0] Z380_CAUSE_BUS_FAULT    = 32'h0000_0002;
  localparam logic [31:0] Z380_CAUSE_IM0_UNSUP    = 32'h0000_0003;
  localparam logic [31:0] Z380_CAUSE_MODESTACK_OVERFLOW  = 32'h0000_0010;
  localparam logic [31:0] Z380_CAUSE_MODESTACK_UNDERFLOW = 32'h0000_0011;
  localparam logic [31:0] Z380_CAUSE_MODEUP_INVALID      = 32'h0000_0012;

  // --------------------------------------------------------------------------
  // CSR implementation (minimal + CAPS/CPUID window)
  // --------------------------------------------------------------------------

  logic csr_rsp_valid_q;
  logic [31:0] csr_rsp_rdata_q;
  logic csr_rsp_fault_q;
  logic csr_rsp_side_q;

  logic [31:0] csr_cause_q;
  logic [31:0] csr_epc_q;
  logic [31:0] csr_trace_ctl_q;
  logic [63:0] cycle_q;
  logic [7:0]  csr_modeflags_q;
  logic [7:0]  csr_tier_q;
  logic [31:0] csr_cpuid_leaf_q;
  logic [31:0] csr_cpuid_subleaf_q;

  // Mode stack (tier/modeflags/return PC)
  logic [MD_SP_W-1:0] md_sp_q;
  logic [7:0]  md_tier_q  [MODESTACK_DEPTH];
  logic [7:0]  md_flags_q [MODESTACK_DEPTH];
  logic [15:0] md_pc_q    [MODESTACK_DEPTH];

  // MODEUP/RETMD decode staging
  logic [7:0] mode_op0_q;
  logic [7:0] mode_op1_q;
  logic [7:0] mode_target_q;

  // CSR-originated debug pulses (optional)
  logic csr_halt_pulse_q;
  logic csr_run_pulse_q;
  logic csr_step_pulse_q;

  // Core-originated trap writeback (single-cycle pulse)
  logic        core_trap_pulse_q;
  logic [31:0] core_trap_cause_q;
  logic [31:0] core_trap_epc_q;

  assign csr.req_ready       = !csr_rsp_valid_q;
  assign csr.rsp_valid       = csr_rsp_valid_q;
  assign csr.rsp_rdata       = csr_rsp_rdata_q;
  assign csr.rsp_fault       = csr_rsp_fault_q;
  assign csr.rsp_side_effect = csr_rsp_side_q;

  wire csr_req_fire = csr.req_valid && csr.req_ready;
  wire csr_rsp_fire = csr.rsp_valid && csr.rsp_ready;
  wire csr_modeflags_wr = csr_req_fire && csr.req_write &&
      (csr.req_addr == CARBON_CSR_MODEFLAGS);
  wire [7:0] csr_modeflags_wdata =
      csr.req_wdata[7:0] & (CARBON_MODEFLAG_STRICT_MASK | CARBON_MODEFLAG_INTMASK_MASK);

  localparam logic [31:0] Z380_FEAT_WORD0 =
      CARBON_FEAT_MODE_SWITCH_MASK |
      CARBON_FEAT_CSR_NAMESPACE_MASK |
      CARBON_FEAT_FABRIC_MASK |
      CARBON_FEAT_CAPS_MASK |
      CARBON_FEAT_POLLING_COMPLETE_MASK |
      CARBON_Z380_32BIT_EXTENDED_MASK;

  localparam logic [7:0] Z380_VENDOR_ID  = 8'h00;
  localparam logic [7:0] Z380_FAMILY_ID  = 8'h38;
  localparam logic [7:0] Z380_MODEL_ID   = 8'h01;
  localparam logic [7:0] Z380_STEPPING   = 8'h00;
  localparam logic [31:0] Z380_VENDOR0   = "CARB";
  localparam logic [31:0] Z380_VENDOR1   = "ON Z";
  localparam logic [31:0] Z380_VENDOR2   = "380 ";

  function automatic logic [31:0] cpuid_word(
      input logic [31:0] leaf,
      input logic [31:0] subleaf,
      input int unsigned word_sel
  );
    logic [31:0] w0, w1, w2, w3;
    begin
      w0 = 32'h0;
      w1 = 32'h0;
      w2 = 32'h0;
      w3 = 32'h0;
      unique case (leaf)
        CARBON_CPUID_LEAF_VENDOR: begin
          w0[15:0]  = 16'(CARBON_CPUID_LEAF_FEATURES0);
          w0[31:16] = 16'h0001;
          w1 = Z380_VENDOR0;
          w2 = Z380_VENDOR1;
          w3 = Z380_VENDOR2;
        end
        CARBON_CPUID_LEAF_ID: begin
          w0 = {Z380_STEPPING, Z380_MODEL_ID, Z380_FAMILY_ID, Z380_VENDOR_ID};
          w1 = 32'h0;
        end
        CARBON_CPUID_LEAF_TIERS: begin
          w0 = {8'h00,
                8'(CARBON_Z80_DERIVED_TIER_P6_Z380),
                8'(CARBON_Z80_DERIVED_TIER_P6_Z380),
                8'(CARBON_TIER_LADDER_Z80)};
          w1 = {8'h00,
                8'(CARBON_AMD_FPU_TIER_P0_AM9511),
                8'(CARBON_AMD_FPU_TIER_P0_AM9511),
                8'(CARBON_TIER_LADDER_AMD_FPU)};
        end
        CARBON_CPUID_LEAF_FEATURES0: begin
          w0 = Z380_FEAT_WORD0;
        end
        default: begin
          // return zeros
        end
      endcase
      unique case (word_sel)
        0: cpuid_word = w0;
        1: cpuid_word = w1;
        2: cpuid_word = w2;
        default: cpuid_word = w3;
      endcase
    end
  endfunction

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      csr_rsp_valid_q <= 1'b0;
      csr_rsp_rdata_q <= '0;
      csr_rsp_fault_q <= 1'b0;
      csr_rsp_side_q  <= 1'b0;
      csr_cause_q     <= '0;
      csr_epc_q       <= '0;
      csr_trace_ctl_q <= '0;
      cycle_q         <= 64'd0;
      csr_cpuid_leaf_q <= 32'h0;
      csr_cpuid_subleaf_q <= 32'h0;
      csr_halt_pulse_q <= 1'b0;
      csr_run_pulse_q  <= 1'b0;
      csr_step_pulse_q <= 1'b0;
    end else begin
      cycle_q <= cycle_q + 64'd1;
      csr_halt_pulse_q <= 1'b0;
      csr_run_pulse_q  <= 1'b0;
      csr_step_pulse_q <= 1'b0;

      if (csr_rsp_fire) csr_rsp_valid_q <= 1'b0;

      if (core_trap_pulse_q) begin
        csr_cause_q <= core_trap_cause_q;
        csr_epc_q   <= core_trap_epc_q;
      end

      if (csr_req_fire) begin
        csr_rsp_valid_q <= 1'b1;
        csr_rsp_fault_q <= 1'b0;
        csr_rsp_side_q  <= csr.req_write;
        csr_rsp_rdata_q <= '0;

        unique case (csr.req_addr)
          CARBON_CSR_ID: begin
            if (!csr.req_write) csr_rsp_rdata_q <= 32'h5A33_3801; // "Z380"+v1
            else csr_rsp_fault_q <= 1'b1;
          end
          CARBON_CSR_TIER: begin
            if (!csr.req_write) csr_rsp_rdata_q[7:0] <= csr_tier_q;
            else csr_rsp_fault_q <= 1'b1;
          end
          CARBON_CSR_MODEFLAGS: begin
            if (!csr.req_write) csr_rsp_rdata_q[7:0] <= csr_modeflags_q;
            else csr_rsp_side_q <= 1'b1;
          end
          CARBON_CSR_TIME: begin
            if (!csr.req_write) csr_rsp_rdata_q <= cycle_q[31:0];
            else csr_rsp_fault_q <= 1'b1;
          end
          CARBON_CSR_TIME_HI: begin
            if (!csr.req_write) csr_rsp_rdata_q <= cycle_q[63:32];
            else csr_rsp_fault_q <= 1'b1;
          end
          CARBON_CSR_CAUSE: begin
            if (!csr.req_write) csr_rsp_rdata_q <= csr_cause_q;
            else csr_rsp_fault_q <= 1'b1;
          end
          CARBON_CSR_EPC: begin
            if (!csr.req_write) csr_rsp_rdata_q <= csr_epc_q;
            else begin
              csr_epc_q <= csr.req_wdata;
              csr_rsp_side_q <= 1'b1;
            end
          end
          CARBON_CSR_IE: begin
            if (!csr.req_write) begin
              csr_rsp_rdata_q[0] <= s_q.IFF1;
              csr_rsp_rdata_q[1] <= s_q.IFF2;
            end else csr_rsp_fault_q <= 1'b1;
          end
          CARBON_CSR_IP: begin
            if (!csr.req_write) begin
              if ($bits(irq.irq_pending) <= 32) begin
                csr_rsp_rdata_q <= {{(32-$bits(irq.irq_pending)){1'b0}}, irq.irq_pending};
              end else begin
                csr_rsp_rdata_q <= irq.irq_pending[31:0];
              end
            end else csr_rsp_fault_q <= 1'b1;
          end
          CARBON_CSR_TRACE_CTL: begin
            if (!csr.req_write) csr_rsp_rdata_q <= csr_trace_ctl_q;
            else begin
              csr_trace_ctl_q <= csr.req_wdata;
              csr_rsp_side_q <= 1'b1;
            end
          end
          CARBON_CSR_CPUID_LEAF: begin
            if (csr.req_write) begin
              csr_cpuid_leaf_q <= csr.req_wdata;
              csr_rsp_side_q <= 1'b1;
            end else begin
              csr_rsp_rdata_q <= csr_cpuid_leaf_q;
            end
          end
          CARBON_CSR_CPUID_SUBLEAF: begin
            if (csr.req_write) begin
              csr_cpuid_subleaf_q <= csr.req_wdata;
              csr_rsp_side_q <= 1'b1;
            end else begin
              csr_rsp_rdata_q <= csr_cpuid_subleaf_q;
            end
          end
          CARBON_CSR_CPUID_DATA0_LO: begin
            if (!csr.req_write) csr_rsp_rdata_q <= cpuid_word(csr_cpuid_leaf_q, csr_cpuid_subleaf_q, 0);
            else csr_rsp_fault_q <= 1'b1;
          end
          CARBON_CSR_CPUID_DATA0_HI: begin
            if (!csr.req_write) csr_rsp_rdata_q <= 32'h0;
            else csr_rsp_fault_q <= 1'b1;
          end
          CARBON_CSR_CPUID_DATA1_LO: begin
            if (!csr.req_write) csr_rsp_rdata_q <= cpuid_word(csr_cpuid_leaf_q, csr_cpuid_subleaf_q, 1);
            else csr_rsp_fault_q <= 1'b1;
          end
          CARBON_CSR_CPUID_DATA1_HI: begin
            if (!csr.req_write) csr_rsp_rdata_q <= 32'h0;
            else csr_rsp_fault_q <= 1'b1;
          end
          CARBON_CSR_CPUID_DATA2_LO: begin
            if (!csr.req_write) csr_rsp_rdata_q <= cpuid_word(csr_cpuid_leaf_q, csr_cpuid_subleaf_q, 2);
            else csr_rsp_fault_q <= 1'b1;
          end
          CARBON_CSR_CPUID_DATA2_HI: begin
            if (!csr.req_write) csr_rsp_rdata_q <= 32'h0;
            else csr_rsp_fault_q <= 1'b1;
          end
          CARBON_CSR_CPUID_DATA3_LO: begin
            if (!csr.req_write) csr_rsp_rdata_q <= cpuid_word(csr_cpuid_leaf_q, csr_cpuid_subleaf_q, 3);
            else csr_rsp_fault_q <= 1'b1;
          end
          CARBON_CSR_CPUID_DATA3_HI: begin
            if (!csr.req_write) csr_rsp_rdata_q <= 32'h0;
            else csr_rsp_fault_q <= 1'b1;
          end
          CARBON_CSR_DBG_CTRL: begin
            if (csr.req_write) begin
              if (csr.req_wdata[0]) csr_halt_pulse_q <= 1'b1;
              if (csr.req_wdata[1]) csr_run_pulse_q  <= 1'b1;
              if (csr.req_wdata[2]) csr_step_pulse_q <= 1'b1;
              csr_rsp_side_q <= 1'b1;
            end else begin
              csr_rsp_rdata_q[0] <= 1'b0;
            end
          end
          CARBON_CSR_DBG_STEP: begin
            if (csr.req_write) begin
              csr_step_pulse_q <= 1'b1;
              csr_rsp_side_q <= 1'b1;
            end else csr_rsp_fault_q <= 1'b1;
          end
          CARBON_CSR_DBG_STATUS: begin
            if (!csr.req_write) begin
              csr_rsp_rdata_q[0] <= dbg_halted_q || trapped_q;
              csr_rsp_rdata_q[1] <= dbg_step_ack_q;
            end else begin
              csr_rsp_fault_q <= 1'b1;
            end
          end
          default: begin
            csr_rsp_fault_q <= 1'b1;
          end
        endcase
      end
    end
  end

  // --------------------------------------------------------------------------
  // Core implementation follows.
  // --------------------------------------------------------------------------

  // --------------------------------------------------------------------------
  // Interrupt interface mapping
  // --------------------------------------------------------------------------
  wire irq_is_nmi = (IRQ_VEC_W > 8) ? irq.irq_vector[IRQ_VEC_W-1] : 1'b0;
  wire [7:0] irq_byte = irq.irq_vector[7:0];

  logic irq_ack_q;
  logic [IRQ_VEC_W-1:0] irq_ack_vec_q;
  assign irq.irq_ack = irq_ack_q;
  assign irq.irq_ack_vector = irq_ack_vec_q;

  // --------------------------------------------------------------------------
  // Fabric bus "subroutine" (single outstanding op)
  // --------------------------------------------------------------------------
  typedef enum logic [3:0] {
    DEST_NONE     = 4'd0,
    DEST_OPCODE   = 4'd1,
    DEST_DISP     = 4'd2,
    DEST_IMM8     = 4'd3,
    DEST_IMM16_LO = 4'd4,
    DEST_IMM16_HI = 4'd5,
    DEST_TMP8     = 4'd6,
    DEST_TMP16_LO = 4'd7,
    DEST_TMP16_HI = 4'd8
  } dest_e;

  typedef enum logic [5:0] {
    ST_RESET,
    ST_TRAP,
    ST_BOUNDARY,
    ST_DECODE,
    ST_DDCB_FETCH,
    ST_EXEC,
    ST_IMM8_DONE,
    ST_IMM16_HI,
    ST_IMM16_DONE,
    ST_MEM_RD_DONE,
    ST_MEM16_HI,
    ST_MEM16_DONE,
    ST_MEM16_WR_HI,
    ST_STACK_POP_LO,
    ST_STACK_POP_HI,
    ST_STACK_POP_DONE,
    ST_EX_SP_HI,
    ST_EX_SP_WR_LO,
    ST_EX_SP_WR_HI,
    ST_BLOCK_DONE,
    ST_INT_PUSH_HI,
    ST_INT_PUSH_LO,
    ST_INT_VECTOR,
    ST_INT_IM2_HI,
    ST_INT_IM2_SETPC,
    ST_BUS_REQ,
    ST_BUS_RSP
  } state_e;

  state_e state_q;
  state_e state_after_bus_q;
  dest_e  bus_dest_q;

  logic bus_is_io_q;
  logic [FAB_OP_W-1:0] bus_op_q;
  logic [FAB_ADDR_W-1:0] bus_addr_q;
  logic [FAB_DATA_W-1:0] bus_wdata_q;
  logic [FAB_STRB_W-1:0] bus_wstrb_q;
  logic [FAB_SIZE_W-1:0] bus_size_q;
  logic [FAB_ATTR_W-1:0] bus_attr_q;

  wire sel_io = bus_is_io_q;
  wire req_ready_sel = sel_io ? io_if.req_ready : mem_if.req_ready;
  wire rsp_valid_sel = sel_io ? io_if.rsp_valid : mem_if.rsp_valid;
  wire [FAB_DATA_W-1:0] rsp_rdata_sel = sel_io ? io_if.rsp_rdata : mem_if.rsp_rdata;
  wire [FAB_CODE_W-1:0] rsp_code_sel  = sel_io ? io_if.rsp_code  : mem_if.rsp_code;

  // Drive fabric master ports.
  assign mem_if.req_valid = (state_q == ST_BUS_REQ) && !sel_io;
  assign mem_if.req_op    = bus_op_q;
  assign mem_if.req_addr  = bus_addr_q;
  assign mem_if.req_wdata = bus_wdata_q;
  assign mem_if.req_wstrb = bus_wstrb_q;
  assign mem_if.req_size  = bus_size_q;
  assign mem_if.req_attr  = bus_attr_q;
  assign mem_if.req_id    = '0;
  assign mem_if.rsp_ready = (state_q == ST_BUS_RSP) && !sel_io;

  assign io_if.req_valid = (state_q == ST_BUS_REQ) && sel_io;
  assign io_if.req_op    = bus_op_q;
  assign io_if.req_addr  = bus_addr_q;
  assign io_if.req_wdata = bus_wdata_q;
  assign io_if.req_wstrb = bus_wstrb_q;
  assign io_if.req_size  = bus_size_q;
  assign io_if.req_attr  = bus_attr_q;
  assign io_if.req_id    = '0;
  assign io_if.rsp_ready = (state_q == ST_BUS_RSP) && sel_io;

  task automatic start_bus_read(
      input logic is_io,
      input logic [15:0] addr,
      input dest_e dest,
      input state_e next_state
  );
    begin
      bus_is_io_q <= is_io;
      bus_op_q <= FAB_OP_W'(CARBON_FABRIC_XACT_READ);
      bus_addr_q <= FAB_ADDR_W'({{(FAB_ADDR_W-16){1'b0}}, addr});
      bus_wdata_q <= '0;
      bus_wstrb_q <= '0;
      bus_size_q <= '0;
      bus_attr_q <= is_io ? IO_ATTR : MEM_ATTR;
      bus_dest_q <= dest;
      state_after_bus_q <= next_state;
      state_q <= ST_BUS_REQ;
    end
  endtask

  task automatic start_bus_write(
      input logic is_io,
      input logic [15:0] addr,
      input logic [7:0] data,
      input state_e next_state
  );
    begin
      bus_is_io_q <= is_io;
      bus_op_q <= FAB_OP_W'(CARBON_FABRIC_XACT_WRITE);
      bus_addr_q <= FAB_ADDR_W'({{(FAB_ADDR_W-16){1'b0}}, addr});
      bus_wdata_q <= FAB_DATA_W'({{(FAB_DATA_W-8){1'b0}}, data});
      bus_wstrb_q <= FAB_STRB_W'({{(FAB_STRB_W-1){1'b0}}, 1'b1});
      bus_size_q <= '0;
      bus_attr_q <= is_io ? IO_ATTR : MEM_ATTR;
      bus_dest_q <= DEST_NONE;
      state_after_bus_q <= next_state;
      state_q <= ST_BUS_REQ;
    end
  endtask

  // --------------------------------------------------------------------------
  // Core architectural state and decode context
  // --------------------------------------------------------------------------
  z85_state_t s_q;
  z85_grp_e grp_q;
  z85_idx_sel_e idx_q;
  logic signed [7:0] disp_q;
  logic [7:0] opcode_q;
  logic [7:0] imm8_q;
  logic [15:0] imm16_q;
  logic [7:0] tmp8_q;
  logic [15:0] tmp16_q;
  logic [15:0] insn_pc_q;

  // Interrupt context
  logic int_is_nmi_q;
  logic [7:0] int_vec_q;

  // Control
  logic trapped_q;
  logic ei_delay_q;

  // Execution contexts (minimal)
  typedef enum logic [4:0] {
    IMM8_NONE = 5'd0,
    IMM8_LD_R,
    IMM8_ALU_A,
    IMM8_JR,
    IMM8_JR_COND,
    IMM8_DJNZ,
    IMM8_OUT_N_A,
    IMM8_IN_A_N,
    IMM8_MODE_OP0,
    IMM8_MODE_OP1,
    IMM8_MODE_TIER,
    IMM8_IN0,
    IMM8_OUT0,
    IMM8_TST_N
  } imm8_ctx_e;
  imm8_ctx_e imm8_ctx_q;
  logic [2:0] imm8_r_q;
  logic [2:0] imm8_aluop_q;
  logic [2:0] imm8_cond_q;
  logic       imm8_is_io_q;
  logic [15:0] mem_addr_q;

  typedef enum logic [4:0] {
    IMM16_NONE = 5'd0,
    IMM16_LD_DD,
    IMM16_LD_MEM_DD,
    IMM16_LD_DD_MEM,
    IMM16_LD_MEM_A,
    IMM16_LD_A_MEM,
    IMM16_JP,
    IMM16_JP_COND,
    IMM16_CALL,
    IMM16_CALL_COND,
    IMM16_MODE_ENTRY
  } imm16_ctx_e;
  imm16_ctx_e imm16_ctx_q;
  logic [1:0] imm16_dd_q;
  logic [2:0] imm16_cond_q;
  logic       imm16_use_idx_q;

  typedef enum logic [4:0] {
    MEMRD_NONE = 5'd0,
    MEMRD_LD_R,
    MEMRD_ALU,
    MEMRD_INCDEC,
    MEMRD_IN,
    MEMRD_TST,
    MEMRD_BLOCK_LD,
    MEMRD_BLOCK_CP,
    MEMRD_BLOCK_IN,
    MEMRD_BLOCK_OUT,
    MEMRD_RLD,
    MEMRD_RRD,
    MEMRD_CB
  } mem_rd_ctx_e;
  mem_rd_ctx_e mem_rd_ctx_q;
  logic [2:0] mem_rd_r_q;
  logic [2:0] mem_rd_aluop_q;
  logic       mem_rd_inc_q;
  logic       mem_rd_is_io_q;

  typedef enum logic [2:0] {
    MEM16_NONE = 3'd0,
    MEM16_LD_DD_MEM
  } mem16_ctx_e;
  mem16_ctx_e mem16_ctx_q;
  logic [1:0] mem16_dd_q;
  logic       mem16_use_idx_q;

  logic [15:0] stack_push_val_q;
  state_e      stack_push_next_q;
  typedef enum logic [1:0] {
    STACK_POP_NONE = 2'd0,
    STACK_POP_PC,
    STACK_POP_PP
  } stack_pop_ctx_e;
  stack_pop_ctx_e stack_pop_ctx_q;
  logic [1:0] stack_pop_pp_q;
  logic       stack_pop_use_idx_q;
  logic       stack_pop_restore_iff_q;

  logic [15:0] ex_sp_val_q;
  state_e      mem16_wr_next_q;
  typedef enum logic [1:0] {
    BLOCK_NONE = 2'd0,
    BLOCK_LD,
    BLOCK_CP,
    BLOCK_IN,
    BLOCK_OUT
  } block_kind_e;
  block_kind_e block_kind_q;
  logic        block_dir_q;
  logic        block_repeat_q;
  logic [15:0] block_addr_q;
  logic [15:0] block_port_q;

  // Debug control (halt/step)
  logic dbg_halted_q;
  logic dbg_step_pending_q;
  logic dbg_step_inflight_q;
  logic dbg_step_ack_q;

  wire dbg_halt_req = dbg.halt_req | csr_halt_pulse_q;
  wire dbg_run_req  = dbg.run_req  | csr_run_pulse_q;
  wire dbg_step_req = dbg.step_req | csr_step_pulse_q;

  assign dbg.halt_ack = dbg_halted_q || trapped_q;
  assign dbg.step_ack = dbg_step_ack_q;
  assign dbg.bp_ready = 1'b0;
  assign dbg.trace_valid = 1'b0;
  assign dbg.trace_data  = '0;

  // --------------------------------------------------------------------------
  // Core FSM
  // --------------------------------------------------------------------------
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      int i;
      state_q <= ST_RESET;
      state_after_bus_q <= ST_BOUNDARY;
      bus_dest_q <= DEST_NONE;
      bus_is_io_q <= 1'b0;
      bus_op_q <= '0;
      bus_addr_q <= '0;
      bus_wdata_q <= '0;
      bus_wstrb_q <= '0;
      bus_size_q <= '0;
      bus_attr_q <= '0;

      s_q <= '0;
      s_q.SP <= 16'hFFFE;
      s_q.PC <= 16'h0000;
      s_q.IM <= 2'd0;
      s_q.halt_latch <= 1'b0;

      grp_q <= Z85_GRP_BASE;
      idx_q <= Z85_IDX_NONE;
      disp_q <= '0;
      opcode_q <= 8'h00;
      imm8_q <= '0;
      imm16_q <= '0;
      tmp8_q <= '0;
      tmp16_q <= '0;
      insn_pc_q <= '0;

      int_is_nmi_q <= 1'b0;
      int_vec_q <= 8'h00;

      trapped_q <= 1'b0;
      ei_delay_q <= 1'b0;

      imm8_ctx_q <= IMM8_NONE;
      imm8_r_q <= '0;
      imm8_aluop_q <= '0;
      imm8_cond_q <= '0;
      imm8_is_io_q <= 1'b0;
      mem_addr_q <= '0;
      imm16_ctx_q <= IMM16_NONE;
      imm16_dd_q <= '0;
      imm16_cond_q <= '0;
      imm16_use_idx_q <= 1'b0;
      mem_rd_ctx_q <= MEMRD_NONE;
      mem_rd_r_q <= '0;
      mem_rd_aluop_q <= '0;
      mem_rd_inc_q <= 1'b0;
      mem_rd_is_io_q <= 1'b0;
      mem16_ctx_q <= MEM16_NONE;
      mem16_dd_q <= '0;
      mem16_use_idx_q <= 1'b0;
      stack_push_val_q <= '0;
      stack_push_next_q <= ST_BOUNDARY;
      stack_pop_ctx_q <= STACK_POP_NONE;
      stack_pop_pp_q <= '0;
      stack_pop_use_idx_q <= 1'b0;
      stack_pop_restore_iff_q <= 1'b0;
      ex_sp_val_q <= '0;
      mem16_wr_next_q <= ST_BOUNDARY;
      block_kind_q <= BLOCK_NONE;
      block_dir_q <= 1'b0;
      block_repeat_q <= 1'b0;
      block_addr_q <= '0;
      block_port_q <= '0;

      csr_modeflags_q <= CARBON_MODEFLAG_STRICT_MASK;
      csr_tier_q <= 8'(CARBON_Z80_DERIVED_TIER_P0_I8080);
      md_sp_q <= '0;
      mode_op0_q <= '0;
      mode_op1_q <= '0;
      mode_target_q <= '0;
      for (i = 0; i < int'(MODESTACK_DEPTH); i++) begin
        md_tier_q[i] <= '0;
        md_flags_q[i] <= '0;
        md_pc_q[i] <= '0;
      end

      dbg_halted_q <= 1'b0;
      dbg_step_pending_q <= 1'b0;
      dbg_step_inflight_q <= 1'b0;
      dbg_step_ack_q <= 1'b0;

      irq_ack_q <= 1'b0;
      irq_ack_vec_q <= '0;

      core_trap_pulse_q <= 1'b0;
      core_trap_cause_q <= '0;
      core_trap_epc_q   <= '0;
    end else begin
      dbg_step_ack_q <= 1'b0;
      irq_ack_q <= 1'b0;
      core_trap_pulse_q <= 1'b0;
      if (csr_modeflags_wr) csr_modeflags_q <= csr_modeflags_wdata;

      unique case (state_q)
        ST_RESET: begin
          trapped_q <= 1'b0;
          ei_delay_q <= 1'b0;
          s_q <= '0;
          s_q.SP <= 16'hFFFE;
          s_q.PC <= 16'h0000;
          s_q.IM <= 2'd0;
          s_q.halt_latch <= 1'b0;
          grp_q <= Z85_GRP_BASE;
          idx_q <= Z85_IDX_NONE;
          disp_q <= '0;
          state_q <= ST_BOUNDARY;
        end

        ST_TRAP: begin
          state_q <= ST_TRAP;
        end

        ST_BOUNDARY: begin
          if (dbg_step_inflight_q) begin
            dbg_step_inflight_q <= 1'b0;
            dbg_step_ack_q <= 1'b1;
          end

          if (dbg_run_req) begin
            dbg_halted_q <= 1'b0;
            dbg_step_pending_q <= 1'b0;
          end
          if (dbg_halt_req) dbg_halted_q <= 1'b1;
          if (dbg_step_req && dbg_halted_q) dbg_step_pending_q <= 1'b1;

          if (trapped_q) begin
            state_q <= ST_TRAP;
          end else if (dbg_halted_q && !dbg_step_pending_q) begin
            state_q <= ST_BOUNDARY;
          end else begin
            if (dbg_halted_q && dbg_step_pending_q) begin
              dbg_step_pending_q <= 1'b0;
              dbg_step_inflight_q <= 1'b1;
            end

            // EI delay inhibits maskable interrupts for one boundary.
            if (ei_delay_q) ei_delay_q <= 1'b0;

            // Interrupt sampling at boundary.
            if (irq.irq_valid && irq_is_nmi) begin
              irq_ack_q <= 1'b1;
              irq_ack_vec_q <= irq.irq_vector;
              int_is_nmi_q <= 1'b1;
              int_vec_q <= irq_byte;
              s_q.halt_latch <= 1'b0;
              s_q.IFF2 <= s_q.IFF1;
              s_q.IFF1 <= 1'b0;
              stack_push_val_q <= s_q.PC;
              stack_push_next_q <= ST_INT_VECTOR;
              state_q <= ST_INT_PUSH_HI;
            end else if (irq.irq_valid && !irq_is_nmi && s_q.IFF1 && !ei_delay_q) begin
              irq_ack_q <= 1'b1;
              irq_ack_vec_q <= irq.irq_vector;
              int_is_nmi_q <= 1'b0;
              int_vec_q <= irq_byte;
              s_q.halt_latch <= 1'b0;
              s_q.IFF1 <= 1'b0;
              s_q.IFF2 <= 1'b0;
              stack_push_val_q <= s_q.PC;
              stack_push_next_q <= ST_INT_VECTOR;
              state_q <= ST_INT_PUSH_HI;
            end else if (s_q.halt_latch) begin
              state_q <= ST_BOUNDARY;
            end else begin
              // Start next instruction.
              insn_pc_q <= s_q.PC;
              grp_q <= Z85_GRP_BASE;
              idx_q <= Z85_IDX_NONE;
              disp_q <= '0;

              bus_is_io_q <= 1'b0;
              bus_op_q <= FAB_OP_W'(CARBON_FABRIC_XACT_READ);
              bus_addr_q <= FAB_ADDR_W'({{(FAB_ADDR_W-16){1'b0}}, s_q.PC});
              bus_wdata_q <= '0;
              bus_wstrb_q <= '0;
              bus_size_q <= '0;
              bus_attr_q <= MEM_ATTR;
              bus_dest_q <= DEST_OPCODE;
              state_after_bus_q <= ST_DECODE;
              state_q <= ST_BUS_REQ;
            end
          end
        end

        ST_BUS_REQ: begin
          if (req_ready_sel) state_q <= ST_BUS_RSP;
        end

        ST_BUS_RSP: begin
          if (rsp_valid_sel) begin
            if (rsp_code_sel != FAB_CODE_W'(CARBON_FABRIC_RESP_OK)) begin
              trapped_q <= 1'b1;
              core_trap_pulse_q <= 1'b1;
              core_trap_cause_q <= Z380_CAUSE_BUS_FAULT;
              core_trap_epc_q   <= {16'h0000, insn_pc_q};
              state_q <= ST_TRAP;
            end else begin
              unique case (bus_dest_q)
                DEST_OPCODE: begin
                  opcode_q <= rsp_rdata_sel[7:0];
                  s_q.PC   <= s_q.PC + 16'd1;
                  r_inc_on_opcode_fetch(s_q);
                end
                DEST_DISP: begin
                  disp_q <= $signed(rsp_rdata_sel[7:0]);
                  s_q.PC <= s_q.PC + 16'd1;
                end
                DEST_IMM8: begin
                  imm8_q <= rsp_rdata_sel[7:0];
                  s_q.PC <= s_q.PC + 16'd1;
                end
                DEST_IMM16_LO: begin
                  imm16_q[7:0] <= rsp_rdata_sel[7:0];
                  s_q.PC <= s_q.PC + 16'd1;
                end
                DEST_IMM16_HI: begin
                  imm16_q[15:8] <= rsp_rdata_sel[7:0];
                  s_q.PC <= s_q.PC + 16'd1;
                end
                DEST_TMP8: begin
                  tmp8_q <= rsp_rdata_sel[7:0];
                end
                DEST_TMP16_LO: begin
                  tmp16_q[7:0] <= rsp_rdata_sel[7:0];
                end
                DEST_TMP16_HI: begin
                  tmp16_q[15:8] <= rsp_rdata_sel[7:0];
                end
                default: begin end
              endcase
              state_q <= state_after_bus_q;
            end
          end
        end

        ST_DECODE: begin
          if (opcode_q == 8'hDD) begin
            idx_q <= Z85_IDX_IX;
            bus_is_io_q <= 1'b0;
            bus_op_q <= FAB_OP_W'(CARBON_FABRIC_XACT_READ);
            bus_addr_q <= FAB_ADDR_W'({{(FAB_ADDR_W-16){1'b0}}, s_q.PC});
            bus_attr_q <= MEM_ATTR;
            bus_wdata_q <= '0;
            bus_wstrb_q <= '0;
            bus_size_q <= '0;
            bus_dest_q <= DEST_OPCODE;
            state_after_bus_q <= ST_DECODE;
            state_q <= ST_BUS_REQ;
          end else if (opcode_q == 8'hFD) begin
            idx_q <= Z85_IDX_IY;
            bus_is_io_q <= 1'b0;
            bus_op_q <= FAB_OP_W'(CARBON_FABRIC_XACT_READ);
            bus_addr_q <= FAB_ADDR_W'({{(FAB_ADDR_W-16){1'b0}}, s_q.PC});
            bus_attr_q <= MEM_ATTR;
            bus_wdata_q <= '0;
            bus_wstrb_q <= '0;
            bus_size_q <= '0;
            bus_dest_q <= DEST_OPCODE;
            state_after_bus_q <= ST_DECODE;
            state_q <= ST_BUS_REQ;
          end else if (opcode_q == 8'hED) begin
            grp_q <= Z85_GRP_ED;
            idx_q <= Z85_IDX_NONE;
            bus_is_io_q <= 1'b0;
            bus_op_q <= FAB_OP_W'(CARBON_FABRIC_XACT_READ);
            bus_addr_q <= FAB_ADDR_W'({{(FAB_ADDR_W-16){1'b0}}, s_q.PC});
            bus_attr_q <= MEM_ATTR;
            bus_wdata_q <= '0;
            bus_wstrb_q <= '0;
            bus_size_q <= '0;
            bus_dest_q <= DEST_OPCODE;
            state_after_bus_q <= ST_EXEC;
            state_q <= ST_BUS_REQ;
          end else if (opcode_q == 8'hCB) begin
            if (idx_q == Z85_IDX_NONE) begin
              grp_q <= Z85_GRP_CB;
              bus_is_io_q <= 1'b0;
              bus_op_q <= FAB_OP_W'(CARBON_FABRIC_XACT_READ);
              bus_addr_q <= FAB_ADDR_W'({{(FAB_ADDR_W-16){1'b0}}, s_q.PC});
              bus_attr_q <= MEM_ATTR;
              bus_wdata_q <= '0;
              bus_wstrb_q <= '0;
              bus_size_q <= '0;
              bus_dest_q <= DEST_OPCODE;
              state_after_bus_q <= ST_EXEC;
              state_q <= ST_BUS_REQ;
            end else begin
              grp_q <= Z85_GRP_DDCB;
              bus_is_io_q <= 1'b0;
              bus_op_q <= FAB_OP_W'(CARBON_FABRIC_XACT_READ);
              bus_addr_q <= FAB_ADDR_W'({{(FAB_ADDR_W-16){1'b0}}, s_q.PC});
              bus_attr_q <= MEM_ATTR;
              bus_wdata_q <= '0;
              bus_wstrb_q <= '0;
              bus_size_q <= '0;
              bus_dest_q <= DEST_DISP;
              state_after_bus_q <= ST_DDCB_FETCH;
              state_q <= ST_BUS_REQ;
            end
          end else begin
            grp_q <= Z85_GRP_BASE;
            if ((idx_q != Z85_IDX_NONE) && base_uses_hl_indirect(opcode_q)) begin
              bus_is_io_q <= 1'b0;
              bus_op_q <= FAB_OP_W'(CARBON_FABRIC_XACT_READ);
              bus_addr_q <= FAB_ADDR_W'({{(FAB_ADDR_W-16){1'b0}}, s_q.PC});
              bus_attr_q <= MEM_ATTR;
              bus_wdata_q <= '0;
              bus_wstrb_q <= '0;
              bus_size_q <= '0;
              bus_dest_q <= DEST_DISP;
              state_after_bus_q <= ST_EXEC;
              state_q <= ST_BUS_REQ;
            end else begin
              disp_q <= '0;
              state_q <= ST_EXEC;
            end
          end
        end

        ST_DDCB_FETCH: begin
          // fetch CB opcode byte after displacement
          bus_is_io_q <= 1'b0;
          bus_op_q <= FAB_OP_W'(CARBON_FABRIC_XACT_READ);
          bus_addr_q <= FAB_ADDR_W'({{(FAB_ADDR_W-16){1'b0}}, s_q.PC});
          bus_attr_q <= MEM_ATTR;
          bus_wdata_q <= '0;
          bus_wstrb_q <= '0;
          bus_size_q <= '0;
          bus_dest_q <= DEST_OPCODE;
          state_after_bus_q <= ST_EXEC;
          state_q <= ST_BUS_REQ;
        end

        ST_EXEC: begin
          logic handled;
          logic tier_illegal;
          logic tier_is_p0;
          logic tier_is_p1;
          logic tier_is_p2;
          logic tier_is_p3;
          logic tier_is_p4;
          logic tier_is_p5;
          logic tier_is_p6;
          logic tier_is_z80_plus;
          logic tier_is_z180_plus;
          logic z180_op;
          z85_alu8_t o8;
          z85_alu16_t o16;
          handled = 1'b0;
          tier_illegal = 1'b0;
          tier_is_p0 = (csr_tier_q == 8'(CARBON_Z80_DERIVED_TIER_P0_I8080));
          tier_is_p1 = (csr_tier_q == 8'(CARBON_Z80_DERIVED_TIER_P1_I8085));
          tier_is_p2 = (csr_tier_q == 8'(CARBON_Z80_DERIVED_TIER_P2_Z80));
          tier_is_p3 = (csr_tier_q == 8'(CARBON_Z80_DERIVED_TIER_P3_Z180));
          tier_is_p4 = (csr_tier_q == 8'(CARBON_Z80_DERIVED_TIER_P4_EZ80));
          tier_is_p5 = (csr_tier_q == 8'(CARBON_Z80_DERIVED_TIER_P5_Z280));
          tier_is_p6 = (csr_tier_q == 8'(CARBON_Z80_DERIVED_TIER_P6_Z380));
          tier_is_z80_plus = (tier_is_p2 || tier_is_p3 || tier_is_p4 || tier_is_p5 || tier_is_p6);
          tier_is_z180_plus = (tier_is_p3 || tier_is_p4 || tier_is_p5 || tier_is_p6);

          z180_op = 1'b0;
          if (grp_q == Z85_GRP_ED) begin
            if ((opcode_q & 8'hC7) == 8'h00) z180_op = 1'b1; // IN0 r,(n)
            else if ((opcode_q & 8'hC7) == 8'h01) z180_op = 1'b1; // OUT0 (n),r
            else if ((opcode_q & 8'hC7) == 8'h04) z180_op = 1'b1; // TST r/(HL)
            else if (opcode_q == 8'h83 || opcode_q == 8'h8B ||
                     opcode_q == 8'h93 || opcode_q == 8'h9B) begin
              z180_op = 1'b1;
            end
          end

          if (csr_tier_q > 8'(CARBON_Z80_DERIVED_TIER_P6_Z380)) begin
            tier_illegal = 1'b1;
          end else begin
            if (!tier_is_z80_plus) begin
              if (idx_q != Z85_IDX_NONE) begin
                tier_illegal = 1'b1;
              end else if (grp_q != Z85_GRP_BASE) begin
                if (!((grp_q == Z85_GRP_ED) && (opcode_q == CARBON_Z90_OPPAGE_P0_PREFIX1))) begin
                  tier_illegal = 1'b1;
                end
              end else begin
                if (opcode_q == 8'h08 || opcode_q == 8'h10 || opcode_q == 8'h18 ||
                    opcode_q == 8'h28 || opcode_q == 8'h38 || opcode_q == 8'hD9) begin
                  tier_illegal = 1'b1;
                end else if (tier_is_p0 && (opcode_q == 8'h20 || opcode_q == 8'h30)) begin
                  tier_illegal = 1'b1;
                end
              end
            end
            if (!tier_is_z180_plus && z180_op) begin
              tier_illegal = 1'b1;
            end
          end

          if (tier_illegal) begin
            trapped_q <= 1'b1;
            core_trap_pulse_q <= 1'b1;
            core_trap_cause_q <= Z380_CAUSE_ILLEGAL_INSN;
            core_trap_epc_q <= {16'h0000, insn_pc_q};
            state_q <= ST_TRAP;
          end else begin
          // BASE group
          if (grp_q == Z85_GRP_BASE) begin
            logic [1:0] x;
            logic [2:0] y, z;
            logic [1:0] p;
            logic q;
            logic [15:0] ea;
            logic [7:0] v;
            x = op_x(opcode_q);
            y = op_y(opcode_q);
            z = op_z(opcode_q);
            p = op_p(opcode_q);
            q = op_q(opcode_q);
            ea = hl_eff_addr(s_q, idx_q, disp_q);

            handled = 1'b1;
            if (tier_is_p1 && (opcode_q == 8'h20 || opcode_q == 8'h30)) begin
              // 8085 RIM/SIM stubs: deterministic no-side-effect behavior.
              if (opcode_q == 8'h20) s_q.A <= 8'h00;
              state_q <= ST_BOUNDARY;
            end else begin
              unique case (x)
              2'd0: begin
                unique case (z)
                  3'd0: begin
                    unique case (y)
                      3'd0: state_q <= ST_BOUNDARY; // NOP
                      3'd1: begin
                        {s_q.A, s_q.F, s_q.A2, s_q.F2} <= {s_q.A2, s_q.F2, s_q.A, s_q.F};
                        state_q <= ST_BOUNDARY;
                      end
                      3'd2: begin
                        imm8_ctx_q <= IMM8_DJNZ;
                        start_bus_read(1'b0, s_q.PC, DEST_IMM8, ST_IMM8_DONE);
                      end
                      3'd3: begin
                        imm8_ctx_q <= IMM8_JR;
                        start_bus_read(1'b0, s_q.PC, DEST_IMM8, ST_IMM8_DONE);
                      end
                      default: begin
                        imm8_ctx_q <= IMM8_JR_COND;
                        imm8_cond_q <= y - 3'd4;
                        start_bus_read(1'b0, s_q.PC, DEST_IMM8, ST_IMM8_DONE);
                      end
                    endcase
                  end
                  3'd1: begin
                    if (!q) begin
                      imm16_ctx_q <= IMM16_LD_DD;
                      imm16_dd_q <= p;
                      imm16_use_idx_q <= (idx_q != Z85_IDX_NONE);
                      start_bus_read(1'b0, s_q.PC, DEST_IMM16_LO, ST_IMM16_HI);
                    end else begin
                      o16 = alu_add16_hl(get_ss(s_q, 2'd2, idx_q), get_ss(s_q, p, idx_q), s_q.F);
                      set_ss(s_q, 2'd2, idx_q, o16.res);
                      s_q.F <= o16.f;
                      state_q <= ST_BOUNDARY;
                    end
                  end
                  3'd2: begin
                    unique case (p)
                      2'd0: begin
                        if (!q) start_bus_write(1'b0, {s_q.B, s_q.C}, s_q.A, ST_BOUNDARY);
                        else begin
                          mem_rd_ctx_q <= MEMRD_LD_R;
                          mem_rd_r_q <= 3'd7;
                          mem_rd_is_io_q <= 1'b0;
                          mem_addr_q <= {s_q.B, s_q.C};
                          start_bus_read(1'b0, {s_q.B, s_q.C}, DEST_TMP8, ST_MEM_RD_DONE);
                        end
                      end
                      2'd1: begin
                        if (!q) start_bus_write(1'b0, {s_q.D, s_q.E}, s_q.A, ST_BOUNDARY);
                        else begin
                          mem_rd_ctx_q <= MEMRD_LD_R;
                          mem_rd_r_q <= 3'd7;
                          mem_rd_is_io_q <= 1'b0;
                          mem_addr_q <= {s_q.D, s_q.E};
                          start_bus_read(1'b0, {s_q.D, s_q.E}, DEST_TMP8, ST_MEM_RD_DONE);
                        end
                      end
                      2'd2: begin
                        imm16_ctx_q <= q ? IMM16_LD_DD_MEM : IMM16_LD_MEM_DD;
                        imm16_dd_q <= 2'd2;
                        imm16_use_idx_q <= (idx_q != Z85_IDX_NONE);
                        start_bus_read(1'b0, s_q.PC, DEST_IMM16_LO, ST_IMM16_HI);
                      end
                      default: begin
                        imm16_ctx_q <= q ? IMM16_LD_A_MEM : IMM16_LD_MEM_A;
                        start_bus_read(1'b0, s_q.PC, DEST_IMM16_LO, ST_IMM16_HI);
                      end
                    endcase
                  end
                  3'd3: begin
                    if (!q) set_ss(s_q, p, idx_q, get_ss(s_q, p, idx_q) + 16'd1);
                    else set_ss(s_q, p, idx_q, get_ss(s_q, p, idx_q) - 16'd1);
                    state_q <= ST_BOUNDARY;
                  end
                  3'd4: begin
                    if (y == 3'd6) begin
                      mem_rd_ctx_q <= MEMRD_INCDEC;
                      mem_rd_inc_q <= 1'b1;
                      mem_addr_q <= ea;
                      start_bus_read(1'b0, ea, DEST_TMP8, ST_MEM_RD_DONE);
                    end else begin
                      o8 = alu_inc8(get_r8(s_q, y, idx_q), s_q.F);
                      set_r8(s_q, y, idx_q, o8.res);
                      s_q.F <= o8.f;
                      state_q <= ST_BOUNDARY;
                    end
                  end
                  3'd5: begin
                    if (y == 3'd6) begin
                      mem_rd_ctx_q <= MEMRD_INCDEC;
                      mem_rd_inc_q <= 1'b0;
                      mem_addr_q <= ea;
                      start_bus_read(1'b0, ea, DEST_TMP8, ST_MEM_RD_DONE);
                    end else begin
                      o8 = alu_dec8(get_r8(s_q, y, idx_q), s_q.F);
                      set_r8(s_q, y, idx_q, o8.res);
                      s_q.F <= o8.f;
                      state_q <= ST_BOUNDARY;
                    end
                  end
                  3'd6: begin
                    imm8_ctx_q <= IMM8_LD_R;
                    imm8_r_q <= y;
                    mem_addr_q <= ea;
                    start_bus_read(1'b0, s_q.PC, DEST_IMM8, ST_IMM8_DONE);
                  end
                  default: begin
                    unique case (y)
                      3'd0: begin
                        logic c;
                        c = s_q.A[7];
                        s_q.A <= {s_q.A[6:0], s_q.A[7]};
                        s_q.F <= flags_rlca_rrca_rla_rra(s_q.F, {s_q.A[6:0], s_q.A[7]}, c);
                        state_q <= ST_BOUNDARY;
                      end
                      3'd1: begin
                        logic c;
                        c = s_q.A[0];
                        s_q.A <= {s_q.A[0], s_q.A[7:1]};
                        s_q.F <= flags_rlca_rrca_rla_rra(s_q.F, {s_q.A[0], s_q.A[7:1]}, c);
                        state_q <= ST_BOUNDARY;
                      end
                      3'd2: begin
                        logic c;
                        c = s_q.A[7];
                        s_q.A <= {s_q.A[6:0], (s_q.F & Z85_F_C) != 0};
                        s_q.F <= flags_rlca_rrca_rla_rra(s_q.F, {s_q.A[6:0], (s_q.F & Z85_F_C) != 0}, c);
                        state_q <= ST_BOUNDARY;
                      end
                      3'd3: begin
                        logic c;
                        c = s_q.A[0];
                        s_q.A <= {(s_q.F & Z85_F_C) != 0, s_q.A[7:1]};
                        s_q.F <= flags_rlca_rrca_rla_rra(s_q.F, {(s_q.F & Z85_F_C) != 0, s_q.A[7:1]}, c);
                        state_q <= ST_BOUNDARY;
                      end
                      3'd4: begin
                        o8 = alu_daa(s_q.A, s_q.F);
                        s_q.A <= o8.res;
                        s_q.F <= o8.f;
                        state_q <= ST_BOUNDARY;
                      end
                      3'd5: begin
                        s_q.A <= ~s_q.A;
                        s_q.F <= flags_cpl(s_q.F, ~s_q.A);
                        state_q <= ST_BOUNDARY;
                      end
                      3'd6: begin
                        s_q.F <= flags_scf(s_q.F, s_q.A);
                        state_q <= ST_BOUNDARY;
                      end
                      default: begin
                        s_q.F <= flags_ccf(s_q.F, s_q.A);
                        state_q <= ST_BOUNDARY;
                      end
                    endcase
                  end
                endcase
              end
              2'd1: begin
                if (y == 3'd6 && z == 3'd6) begin
                  s_q.halt_latch <= 1'b1;
                  state_q <= ST_BOUNDARY;
                end else if (y == 3'd6) begin
                  start_bus_write(1'b0, ea, get_r8(s_q, z, idx_q), ST_BOUNDARY);
                end else if (z == 3'd6) begin
                  mem_rd_ctx_q <= MEMRD_LD_R;
                  mem_rd_r_q <= y;
                  mem_rd_is_io_q <= 1'b0;
                  mem_addr_q <= ea;
                  start_bus_read(1'b0, ea, DEST_TMP8, ST_MEM_RD_DONE);
                end else begin
                  set_r8(s_q, y, idx_q, get_r8(s_q, z, idx_q));
                  state_q <= ST_BOUNDARY;
                end
              end
              2'd2: begin
                if (z == 3'd6) begin
                  mem_rd_ctx_q <= MEMRD_ALU;
                  mem_rd_aluop_q <= y;
                  mem_rd_is_io_q <= 1'b0;
                  mem_addr_q <= ea;
                  start_bus_read(1'b0, ea, DEST_TMP8, ST_MEM_RD_DONE);
                end else begin
                  v = get_r8(s_q, z, idx_q);
                  unique case (y)
                    3'd0: o8 = alu_add8(s_q.A, v);
                    3'd1: o8 = alu_adc8(s_q.A, v, (s_q.F & Z85_F_C) != 0);
                    3'd2: o8 = alu_sub8(s_q.A, v);
                    3'd3: o8 = alu_sbc8(s_q.A, v, (s_q.F & Z85_F_C) != 0);
                    3'd4: o8 = alu_and8(s_q.A, v);
                    3'd5: o8 = alu_xor8(s_q.A, v);
                    3'd6: o8 = alu_or8(s_q.A, v);
                    default: o8 = alu_cp8(s_q.A, v, s_q.F);
                  endcase
                  if (y == 3'd7) s_q.F <= o8.f;
                  else begin
                    s_q.A <= o8.res;
                    s_q.F <= o8.f;
                  end
                  state_q <= ST_BOUNDARY;
                end
              end
              default: begin
                unique case (z)
                  3'd0: begin
                    if (cond_true(y, s_q.F)) begin
                      stack_pop_ctx_q <= STACK_POP_PC;
                      stack_pop_restore_iff_q <= 1'b0;
                      state_q <= ST_STACK_POP_LO;
                    end else begin
                      state_q <= ST_BOUNDARY;
                    end
                  end
                  3'd1: begin
                    if (!q) begin
                      stack_pop_ctx_q <= STACK_POP_PP;
                      stack_pop_pp_q <= p;
                      stack_pop_use_idx_q <= (idx_q != Z85_IDX_NONE);
                      stack_pop_restore_iff_q <= 1'b0;
                      state_q <= ST_STACK_POP_LO;
                    end else begin
                      unique case (p)
                        2'd0: begin
                          stack_pop_ctx_q <= STACK_POP_PC;
                          stack_pop_restore_iff_q <= 1'b0;
                          state_q <= ST_STACK_POP_LO;
                        end
                        2'd1: begin
                          {s_q.B, s_q.C, s_q.D, s_q.E, s_q.H, s_q.L, s_q.B2, s_q.C2, s_q.D2, s_q.E2, s_q.H2, s_q.L2} <=
                              {s_q.B2, s_q.C2, s_q.D2, s_q.E2, s_q.H2, s_q.L2, s_q.B, s_q.C, s_q.D, s_q.E, s_q.H, s_q.L};
                          state_q <= ST_BOUNDARY;
                        end
                        2'd2: begin
                          s_q.PC <= get_ss(s_q, 2'd2, idx_q);
                          state_q <= ST_BOUNDARY;
                        end
                        default: begin
                          s_q.SP <= get_ss(s_q, 2'd2, idx_q);
                          state_q <= ST_BOUNDARY;
                        end
                      endcase
                    end
                  end
                  3'd2: begin
                    imm16_ctx_q <= IMM16_JP_COND;
                    imm16_cond_q <= y;
                    start_bus_read(1'b0, s_q.PC, DEST_IMM16_LO, ST_IMM16_HI);
                  end
                  3'd3: begin
                    unique case (y)
                      3'd0: begin
                        imm16_ctx_q <= IMM16_JP;
                        start_bus_read(1'b0, s_q.PC, DEST_IMM16_LO, ST_IMM16_HI);
                      end
                      3'd2: begin
                        imm8_ctx_q <= IMM8_OUT_N_A;
                        start_bus_read(1'b0, s_q.PC, DEST_IMM8, ST_IMM8_DONE);
                      end
                      3'd3: begin
                        imm8_ctx_q <= IMM8_IN_A_N;
                        start_bus_read(1'b0, s_q.PC, DEST_IMM8, ST_IMM8_DONE);
                      end
                      3'd4: begin
                        ex_sp_val_q <= get_ss(s_q, 2'd2, idx_q);
                        mem_addr_q <= s_q.SP;
                        start_bus_read(1'b0, s_q.SP, DEST_TMP16_LO, ST_EX_SP_HI);
                      end
                      3'd5: begin
                        logic [15:0] tmp;
                        tmp = get_ss(s_q, 2'd2, idx_q);
                        set_ss(s_q, 2'd2, idx_q, {s_q.D, s_q.E});
                        s_q.D <= tmp[15:8];
                        s_q.E <= tmp[7:0];
                        state_q <= ST_BOUNDARY;
                      end
                      3'd6: begin
                        s_q.IFF1 <= 1'b0;
                        s_q.IFF2 <= 1'b0;
                        ei_delay_q <= 1'b0;
                        state_q <= ST_BOUNDARY;
                      end
                      default: begin
                        s_q.IFF1 <= 1'b1;
                        s_q.IFF2 <= 1'b1;
                        ei_delay_q <= 1'b1;
                        state_q <= ST_BOUNDARY;
                      end
                    endcase
                  end
                  3'd4: begin
                    imm16_ctx_q <= IMM16_CALL_COND;
                    imm16_cond_q <= y;
                    start_bus_read(1'b0, s_q.PC, DEST_IMM16_LO, ST_IMM16_HI);
                  end
                  3'd5: begin
                    if (!q) begin
                      stack_push_val_q <= (p == 2'd3) ? {s_q.A, s_q.F} : get_pp(s_q, p, idx_q);
                      stack_push_next_q <= ST_BOUNDARY;
                      state_q <= ST_INT_PUSH_HI;
                    end else if (p == 2'd0) begin
                      imm16_ctx_q <= IMM16_CALL;
                      start_bus_read(1'b0, s_q.PC, DEST_IMM16_LO, ST_IMM16_HI);
                    end else begin
                      state_q <= ST_BOUNDARY;
                    end
                  end
                  3'd6: begin
                    imm8_ctx_q <= IMM8_ALU_A;
                    imm8_aluop_q <= y;
                    start_bus_read(1'b0, s_q.PC, DEST_IMM8, ST_IMM8_DONE);
                  end
                  default: begin
                    stack_push_val_q <= s_q.PC;
                    stack_push_next_q <= ST_BOUNDARY;
                    s_q.PC <= {5'b0, y, 3'b000};
                    state_q <= ST_INT_PUSH_HI;
                  end
                endcase
              end
            endcase
            end
          end

          // CB / DDCB group
          if (!handled && (grp_q == Z85_GRP_CB || grp_q == Z85_GRP_DDCB)) begin
            logic [1:0] x;
            logic [2:0] y, z;
            logic [15:0] ea;
            x = op_x(opcode_q);
            y = op_y(opcode_q);
            z = op_z(opcode_q);
            ea = (grp_q == Z85_GRP_DDCB) ? hl_eff_addr(s_q, idx_q, disp_q) : get_HL(s_q);
            handled = 1'b1;
            if (grp_q == Z85_GRP_DDCB || z == 3'd6) begin
              mem_rd_ctx_q <= MEMRD_CB;
              mem_addr_q <= ea;
              start_bus_read(1'b0, ea, DEST_TMP8, ST_MEM_RD_DONE);
            end else begin
              logic [7:0] rv;
              rv = get_r8(s_q, z, Z85_IDX_NONE);
              if (x == 2'd0) begin
                z85_alu8_t o;
                o = alu_rotshift(y, rv, s_q.F);
                set_r8(s_q, z, Z85_IDX_NONE, o.res);
                s_q.F <= o.f;
              end else if (x == 2'd1) begin
                s_q.F <= flags_bitop(y, rv, s_q.F, rv);
              end else if (x == 2'd2) begin
                rv[y] = 1'b0;
                set_r8(s_q, z, Z85_IDX_NONE, rv);
              end else begin
                rv[y] = 1'b1;
                set_r8(s_q, z, Z85_IDX_NONE, rv);
              end
              state_q <= ST_BOUNDARY;
            end
          end

          // ED group
          if (!handled && grp_q == Z85_GRP_ED) begin
            logic [15:0] port;
            port = {s_q.B, s_q.C};
            handled = 1'b1;
            if (opcode_q == CARBON_Z90_OPPAGE_P0_PREFIX1) begin
              imm8_ctx_q <= IMM8_MODE_OP0;
              start_bus_read(1'b0, s_q.PC, DEST_IMM8, ST_IMM8_DONE);
            end else if (tier_is_z180_plus && ((opcode_q & 8'hC7) == 8'h00)) begin
              imm8_ctx_q <= IMM8_IN0;
              imm8_r_q <= opcode_q[5:3];
              start_bus_read(1'b0, s_q.PC, DEST_IMM8, ST_IMM8_DONE);
            end else if (tier_is_z180_plus && ((opcode_q & 8'hC7) == 8'h01)) begin
              imm8_ctx_q <= IMM8_OUT0;
              imm8_r_q <= opcode_q[5:3];
              start_bus_read(1'b0, s_q.PC, DEST_IMM8, ST_IMM8_DONE);
            end else if (tier_is_z180_plus && ((opcode_q & 8'hCF) == 8'h4C)) begin
              logic [1:0] dd;
              logic [15:0] ss_val;
              logic [7:0] hi;
              logic [7:0] lo;
              logic [15:0] prod;
              dd = opcode_q[5:4];
              ss_val = get_ss(s_q, dd, Z85_IDX_NONE);
              hi = ss_val[15:8];
              lo = ss_val[7:0];
              prod = hi * lo;
              set_ss(s_q, dd, Z85_IDX_NONE, prod);
              state_q <= ST_BOUNDARY;
            end else if (tier_is_z180_plus && ((opcode_q & 8'hC7) == 8'h04)) begin
              if (opcode_q[5:3] == 3'd6) begin
                mem_rd_ctx_q <= MEMRD_TST;
                mem_addr_q <= get_HL(s_q);
                start_bus_read(1'b0, mem_addr_q, DEST_TMP8, ST_MEM_RD_DONE);
              end else begin
                o8 = alu_and8(s_q.A, get_r8(s_q, opcode_q[5:3], Z85_IDX_NONE));
                s_q.F <= o8.f;
                state_q <= ST_BOUNDARY;
              end
            end else if (tier_is_z180_plus && opcode_q == 8'h64) begin
              imm8_ctx_q <= IMM8_TST_N;
              start_bus_read(1'b0, s_q.PC, DEST_IMM8, ST_IMM8_DONE);
            end else if (tier_is_z180_plus && opcode_q == 8'h74) begin
              mem_rd_ctx_q <= MEMRD_TST;
              mem_addr_q <= port;
              start_bus_read(1'b1, port, DEST_TMP8, ST_MEM_RD_DONE);
            end else if (tier_is_z180_plus && opcode_q == 8'h76) begin
              s_q.halt_latch <= 1'b1;
              state_q <= ST_BOUNDARY;
            end else if (tier_is_z180_plus &&
                         (opcode_q == 8'h83 || opcode_q == 8'h8B ||
                          opcode_q == 8'h93 || opcode_q == 8'h9B)) begin
              block_kind_q <= BLOCK_OUT;
              block_dir_q <= (opcode_q == 8'h8B || opcode_q == 8'h9B);
              block_repeat_q <= (opcode_q == 8'h93 || opcode_q == 8'h9B);
              block_addr_q <= get_HL(s_q);
              block_port_q <= port;
              mem_rd_ctx_q <= MEMRD_BLOCK_OUT;
              mem_addr_q <= block_addr_q;
              start_bus_read(1'b0, block_addr_q, DEST_TMP8, ST_MEM_RD_DONE);
            end else if ((opcode_q & 8'hC7) == 8'h40) begin
              mem_rd_ctx_q <= MEMRD_IN;
              mem_rd_r_q <= opcode_q[5:3];
              mem_rd_is_io_q <= 1'b1;
              mem_addr_q <= port;
              start_bus_read(1'b1, port, DEST_TMP8, ST_MEM_RD_DONE);
            end else if ((opcode_q & 8'hC7) == 8'h41) begin
              logic [7:0] out_v;
              out_v = (opcode_q[5:3] == 3'd6) ? 8'h00 : get_r8(s_q, opcode_q[5:3], Z85_IDX_NONE);
              start_bus_write(1'b1, port, out_v, ST_BOUNDARY);
            end else if ((opcode_q & 8'hCF) == 8'h43) begin
              imm16_ctx_q <= IMM16_LD_MEM_DD;
              imm16_dd_q <= opcode_q[5:4];
              imm16_use_idx_q <= 1'b0;
              start_bus_read(1'b0, s_q.PC, DEST_IMM16_LO, ST_IMM16_HI);
            end else if ((opcode_q & 8'hCF) == 8'h4B) begin
              imm16_ctx_q <= IMM16_LD_DD_MEM;
              imm16_dd_q <= opcode_q[5:4];
              imm16_use_idx_q <= 1'b0;
              start_bus_read(1'b0, s_q.PC, DEST_IMM16_LO, ST_IMM16_HI);
            end else if ((opcode_q & 8'hCF) == 8'h42) begin
              o16 = alu_sbc16_hl(get_HL(s_q), get_ss(s_q, opcode_q[5:4], Z85_IDX_NONE), (s_q.F & Z85_F_C) != 0);
              set_HL(s_q, o16.res);
              s_q.F <= o16.f;
              state_q <= ST_BOUNDARY;
            end else if ((opcode_q & 8'hCF) == 8'h4A) begin
              o16 = alu_adc16_hl(get_HL(s_q), get_ss(s_q, opcode_q[5:4], Z85_IDX_NONE), (s_q.F & Z85_F_C) != 0);
              set_HL(s_q, o16.res);
              s_q.F <= o16.f;
              state_q <= ST_BOUNDARY;
            end else if ((opcode_q & 8'hC7) == 8'h44) begin
              o8 = alu_neg(s_q.A, s_q.F);
              s_q.A <= o8.res;
              s_q.F <= o8.f;
              state_q <= ST_BOUNDARY;
            end else if ((opcode_q & 8'hC7) == 8'h45) begin
              stack_pop_ctx_q <= STACK_POP_PC;
              stack_pop_restore_iff_q <= 1'b1;
              state_q <= ST_STACK_POP_LO;
            end else if ((opcode_q & 8'hC7) == 8'h4D) begin
              stack_pop_ctx_q <= STACK_POP_PC;
              stack_pop_restore_iff_q <= 1'b1;
              state_q <= ST_STACK_POP_LO;
            end else begin
              unique case (opcode_q)
                8'h47: begin
                  s_q.I <= s_q.A;
                  state_q <= ST_BOUNDARY;
                end
                8'h4F: begin
                  s_q.R <= s_q.A;
                  state_q <= ST_BOUNDARY;
                end
                8'h57: begin
                  logic [7:0] f;
                  s_q.A <= s_q.I;
                  f = (s_q.F & Z85_F_C) | flags_sz_xy(s_q.I);
                  if (s_q.IFF2) f |= Z85_F_PV;
                  s_q.F <= f;
                  state_q <= ST_BOUNDARY;
                end
                8'h5F: begin
                  logic [7:0] f;
                  s_q.A <= s_q.R;
                  f = (s_q.F & Z85_F_C) | flags_sz_xy(s_q.R);
                  if (s_q.IFF2) f |= Z85_F_PV;
                  s_q.F <= f;
                  state_q <= ST_BOUNDARY;
                end
                8'h46, 8'h4E, 8'h66, 8'h6E: begin
                  s_q.IM <= 2'd0;
                  state_q <= ST_BOUNDARY;
                end
                8'h56, 8'h76: begin
                  s_q.IM <= 2'd1;
                  state_q <= ST_BOUNDARY;
                end
                8'h5E, 8'h7E: begin
                  s_q.IM <= 2'd2;
                  state_q <= ST_BOUNDARY;
                end
                8'h67: begin
                  mem_rd_ctx_q <= MEMRD_RRD;
                  mem_addr_q <= get_HL(s_q);
                  start_bus_read(1'b0, mem_addr_q, DEST_TMP8, ST_MEM_RD_DONE);
                end
                8'h6F: begin
                  mem_rd_ctx_q <= MEMRD_RLD;
                  mem_addr_q <= get_HL(s_q);
                  start_bus_read(1'b0, mem_addr_q, DEST_TMP8, ST_MEM_RD_DONE);
                end
                8'hA0, 8'hB0, 8'hA8, 8'hB8: begin
                  block_kind_q <= BLOCK_LD;
                  block_dir_q <= opcode_q[3];
                  block_repeat_q <= opcode_q[4];
                  block_addr_q <= {s_q.D, s_q.E};
                  mem_rd_ctx_q <= MEMRD_BLOCK_LD;
                  mem_addr_q <= get_HL(s_q);
                  start_bus_read(1'b0, mem_addr_q, DEST_TMP8, ST_MEM_RD_DONE);
                end
                8'hA1, 8'hB1, 8'hA9, 8'hB9: begin
                  block_kind_q <= BLOCK_CP;
                  block_dir_q <= opcode_q[3];
                  block_repeat_q <= opcode_q[4];
                  mem_rd_ctx_q <= MEMRD_BLOCK_CP;
                  mem_addr_q <= get_HL(s_q);
                  start_bus_read(1'b0, mem_addr_q, DEST_TMP8, ST_MEM_RD_DONE);
                end
                8'hA2, 8'hB2, 8'hAA, 8'hBA: begin
                  block_kind_q <= BLOCK_IN;
                  block_dir_q <= opcode_q[3];
                  block_repeat_q <= opcode_q[4];
                  block_addr_q <= get_HL(s_q);
                  block_port_q <= {s_q.B, s_q.C};
                  mem_rd_ctx_q <= MEMRD_BLOCK_IN;
                  mem_addr_q <= block_port_q;
                  start_bus_read(1'b1, block_port_q, DEST_TMP8, ST_MEM_RD_DONE);
                end
                8'hA3, 8'hB3, 8'hAB, 8'hBB: begin
                  block_kind_q <= BLOCK_OUT;
                  block_dir_q <= opcode_q[3];
                  block_repeat_q <= opcode_q[4];
                  block_addr_q <= get_HL(s_q);
                  block_port_q <= {s_q.B, s_q.C};
                  mem_rd_ctx_q <= MEMRD_BLOCK_OUT;
                  mem_addr_q <= block_addr_q;
                  start_bus_read(1'b0, block_addr_q, DEST_TMP8, ST_MEM_RD_DONE);
                end
                default: begin
                  state_q <= ST_BOUNDARY;
                end
              endcase
            end
          end

          if (!handled) begin
            trapped_q <= 1'b1;
            core_trap_pulse_q <= 1'b1;
            core_trap_cause_q <= Z380_CAUSE_ILLEGAL_INSN;
            core_trap_epc_q <= {16'h0000, insn_pc_q};
            state_q <= ST_TRAP;
          end
          end
        end

        ST_IMM8_DONE: begin
          logic signed [7:0] rel;
          rel = $signed(imm8_q);
          unique case (imm8_ctx_q)
            IMM8_LD_R: begin
              if (imm8_r_q == 3'd6) begin
                start_bus_write(1'b0, mem_addr_q, imm8_q, ST_BOUNDARY);
              end else begin
                set_r8(s_q, imm8_r_q, idx_q, imm8_q);
                state_q <= ST_BOUNDARY;
              end
            end
            IMM8_ALU_A: begin
              z85_alu8_t o;
              unique case (imm8_aluop_q)
                Z85_ALU_ADD: o = alu_add8(s_q.A, imm8_q);
                Z85_ALU_ADC: o = alu_adc8(s_q.A, imm8_q, (s_q.F & Z85_F_C) != 0);
                Z85_ALU_SUB: o = alu_sub8(s_q.A, imm8_q);
                Z85_ALU_SBC: o = alu_sbc8(s_q.A, imm8_q, (s_q.F & Z85_F_C) != 0);
                Z85_ALU_AND: o = alu_and8(s_q.A, imm8_q);
                Z85_ALU_XOR: o = alu_xor8(s_q.A, imm8_q);
                Z85_ALU_OR:  o = alu_or8(s_q.A, imm8_q);
                default:     o = alu_cp8(s_q.A, imm8_q, s_q.F);
              endcase
              if (imm8_aluop_q == Z85_ALU_CP) begin
                s_q.F <= o.f;
              end else begin
                s_q.A <= o.res;
                s_q.F <= o.f;
              end
              state_q <= ST_BOUNDARY;
            end
            IMM8_JR: begin
              s_q.PC <= s_q.PC + 16'(rel);
              state_q <= ST_BOUNDARY;
            end
            IMM8_JR_COND: begin
              if (cond_true(imm8_cond_q, s_q.F)) s_q.PC <= s_q.PC + 16'(rel);
              state_q <= ST_BOUNDARY;
            end
            IMM8_DJNZ: begin
              logic [7:0] b_next;
              b_next = s_q.B - 8'd1;
              s_q.B <= b_next;
              if (b_next != 8'h00) s_q.PC <= s_q.PC + 16'(rel);
              state_q <= ST_BOUNDARY;
            end
            IMM8_OUT_N_A: begin
              start_bus_write(1'b1, {s_q.A, imm8_q}, s_q.A, ST_BOUNDARY);
            end
            IMM8_IN_A_N: begin
              mem_rd_ctx_q <= MEMRD_IN;
              mem_rd_r_q <= 3'd7;
              mem_rd_is_io_q <= 1'b1;
              mem_addr_q <= {s_q.A, imm8_q};
              start_bus_read(1'b1, {s_q.A, imm8_q}, DEST_TMP8, ST_MEM_RD_DONE);
            end
            IMM8_IN0: begin
              mem_rd_ctx_q <= MEMRD_IN;
              mem_rd_r_q <= imm8_r_q;
              mem_rd_is_io_q <= 1'b1;
              mem_addr_q <= {8'h00, imm8_q};
              start_bus_read(1'b1, {8'h00, imm8_q}, DEST_TMP8, ST_MEM_RD_DONE);
            end
            IMM8_OUT0: begin
              logic [7:0] out_v;
              out_v = (imm8_r_q == 3'd6) ? 8'h00 : get_r8(s_q, imm8_r_q, Z85_IDX_NONE);
              start_bus_write(1'b1, {8'h00, imm8_q}, out_v, ST_BOUNDARY);
            end
            IMM8_TST_N: begin
              z85_alu8_t o;
              o = alu_and8(s_q.A, imm8_q);
              s_q.F <= o.f;
              state_q <= ST_BOUNDARY;
            end
            IMM8_MODE_OP0: begin
              mode_op0_q <= imm8_q;
              imm8_ctx_q <= IMM8_MODE_OP1;
              start_bus_read(1'b0, s_q.PC, DEST_IMM8, ST_IMM8_DONE);
            end
            IMM8_MODE_OP1: begin
              logic [3:0] major;
              logic [3:0] sub;
              logic [3:0] rs;
              mode_op1_q <= imm8_q;
              major = mode_op0_q[7:4];
              sub = imm8_q[7:4];
              rs = imm8_q[3:0];
              if (major != 4'(CARBON_Z90_P0_MAJOR_SYS)) begin
                trapped_q <= 1'b1;
                core_trap_pulse_q <= 1'b1;
                core_trap_cause_q <= Z380_CAUSE_ILLEGAL_INSN;
                core_trap_epc_q <= {16'h0000, insn_pc_q};
                state_q <= ST_TRAP;
              end else if (sub == 4'(CARBON_Z90_P0_SUB_MODEUP)) begin
                if (rs != 4'd0) begin
                  trapped_q <= 1'b1;
                  core_trap_pulse_q <= 1'b1;
                  core_trap_cause_q <= Z380_CAUSE_MODEUP_INVALID;
                  core_trap_epc_q <= {16'h0000, insn_pc_q};
                  state_q <= ST_TRAP;
                end else begin
                  imm8_ctx_q <= IMM8_MODE_TIER;
                  start_bus_read(1'b0, s_q.PC, DEST_IMM8, ST_IMM8_DONE);
                end
              end else if (sub == 4'(CARBON_Z90_P0_SUB_RETMD)) begin
                if (md_sp_q == 0) begin
                  trapped_q <= 1'b1;
                  core_trap_pulse_q <= 1'b1;
                  core_trap_cause_q <= Z380_CAUSE_MODESTACK_UNDERFLOW;
                  core_trap_epc_q <= {16'h0000, insn_pc_q};
                  state_q <= ST_TRAP;
                end else begin
                  md_sp_q <= md_sp_q - 1'b1;
                  csr_tier_q <= md_tier_q[md_sp_q - 1'b1];
                  csr_modeflags_q <= md_flags_q[md_sp_q - 1'b1];
                  s_q.PC <= md_pc_q[md_sp_q - 1'b1];
                  state_q <= ST_BOUNDARY;
                end
              end else begin
                trapped_q <= 1'b1;
                core_trap_pulse_q <= 1'b1;
                core_trap_cause_q <= Z380_CAUSE_ILLEGAL_INSN;
                core_trap_epc_q <= {16'h0000, insn_pc_q};
                state_q <= ST_TRAP;
              end
            end
            IMM8_MODE_TIER: begin
              mode_target_q <= imm8_q;
              imm16_ctx_q <= IMM16_MODE_ENTRY;
              start_bus_read(1'b0, s_q.PC, DEST_IMM16_LO, ST_IMM16_HI);
            end
            default: state_q <= ST_BOUNDARY;
          endcase
        end

        ST_IMM16_HI: begin
          bus_is_io_q <= 1'b0;
          bus_op_q <= FAB_OP_W'(CARBON_FABRIC_XACT_READ);
          bus_addr_q <= FAB_ADDR_W'({{(FAB_ADDR_W-16){1'b0}}, s_q.PC});
          bus_attr_q <= MEM_ATTR;
          bus_wdata_q <= '0;
          bus_wstrb_q <= '0;
          bus_size_q <= '0;
          bus_dest_q <= DEST_IMM16_HI;
          state_after_bus_q <= ST_IMM16_DONE;
          state_q <= ST_BUS_REQ;
        end

        ST_IMM16_DONE: begin
          unique case (imm16_ctx_q)
            IMM16_LD_DD: begin
              set_ss(s_q, imm16_dd_q, imm16_use_idx_q ? idx_q : Z85_IDX_NONE, imm16_q);
              state_q <= ST_BOUNDARY;
            end
            IMM16_LD_MEM_DD: begin
              tmp16_q <= get_ss(s_q, imm16_dd_q, imm16_use_idx_q ? idx_q : Z85_IDX_NONE);
              mem_addr_q <= imm16_q;
              mem16_wr_next_q <= ST_BOUNDARY;
              start_bus_write(1'b0, imm16_q, tmp16_q[7:0], ST_MEM16_WR_HI);
            end
            IMM16_LD_DD_MEM: begin
              mem16_ctx_q <= MEM16_LD_DD_MEM;
              mem16_dd_q <= imm16_dd_q;
              mem16_use_idx_q <= imm16_use_idx_q;
              mem_addr_q <= imm16_q;
              start_bus_read(1'b0, imm16_q, DEST_TMP16_LO, ST_MEM16_HI);
            end
            IMM16_LD_MEM_A: begin
              mem_addr_q <= imm16_q;
              start_bus_write(1'b0, imm16_q, s_q.A, ST_BOUNDARY);
            end
            IMM16_LD_A_MEM: begin
              mem_rd_ctx_q <= MEMRD_LD_R;
              mem_rd_r_q <= 3'd7;
              mem_rd_is_io_q <= 1'b0;
              mem_addr_q <= imm16_q;
              start_bus_read(1'b0, imm16_q, DEST_TMP8, ST_MEM_RD_DONE);
            end
            IMM16_JP: begin
              s_q.PC <= imm16_q;
              state_q <= ST_BOUNDARY;
            end
            IMM16_JP_COND: begin
              if (cond_true(imm16_cond_q, s_q.F)) s_q.PC <= imm16_q;
              state_q <= ST_BOUNDARY;
            end
            IMM16_CALL: begin
              stack_push_val_q <= s_q.PC;
              stack_push_next_q <= ST_BOUNDARY;
              s_q.PC <= imm16_q;
              state_q <= ST_INT_PUSH_HI;
            end
            IMM16_CALL_COND: begin
              if (cond_true(imm16_cond_q, s_q.F)) begin
                stack_push_val_q <= s_q.PC;
                stack_push_next_q <= ST_BOUNDARY;
                s_q.PC <= imm16_q;
                state_q <= ST_INT_PUSH_HI;
              end else begin
                state_q <= ST_BOUNDARY;
              end
            end
            IMM16_MODE_ENTRY: begin
              if (mode_target_q <= csr_tier_q ||
                  mode_target_q > 8'(CARBON_Z80_DERIVED_TIER_P6_Z380)) begin
                trapped_q <= 1'b1;
                core_trap_pulse_q <= 1'b1;
                core_trap_cause_q <= Z380_CAUSE_MODEUP_INVALID;
                core_trap_epc_q <= {16'h0000, insn_pc_q};
                state_q <= ST_TRAP;
              end else if (md_sp_q == MD_SP_W'(MODESTACK_DEPTH)) begin
                trapped_q <= 1'b1;
                core_trap_pulse_q <= 1'b1;
                core_trap_cause_q <= Z380_CAUSE_MODESTACK_OVERFLOW;
                core_trap_epc_q <= {16'h0000, insn_pc_q};
                state_q <= ST_TRAP;
              end else begin
                md_tier_q[md_sp_q] <= csr_tier_q;
                md_flags_q[md_sp_q] <= csr_modeflags_q;
                md_pc_q[md_sp_q] <= s_q.PC;
                md_sp_q <= md_sp_q + 1'b1;
                csr_tier_q <= mode_target_q;
                s_q.PC <= imm16_q;
                state_q <= ST_BOUNDARY;
              end
            end
            default: state_q <= ST_BOUNDARY;
          endcase
        end

        ST_MEM16_HI: begin
          start_bus_read(1'b0, mem_addr_q + 16'd1, DEST_TMP16_HI, ST_MEM16_DONE);
        end

        ST_MEM16_DONE: begin
          unique case (mem16_ctx_q)
            MEM16_LD_DD_MEM: begin
              set_ss(s_q, mem16_dd_q, mem16_use_idx_q ? idx_q : Z85_IDX_NONE, tmp16_q);
              state_q <= ST_BOUNDARY;
            end
            default: state_q <= ST_BOUNDARY;
          endcase
        end

        ST_MEM16_WR_HI: begin
          start_bus_write(1'b0, mem_addr_q + 16'd1, tmp16_q[15:8], mem16_wr_next_q);
        end

        ST_MEM_RD_DONE: begin
          logic [1:0] x;
          logic [2:0] y, z;
          logic [7:0] v;
          logic [7:0] res;
          z85_alu8_t o;
          x = op_x(opcode_q);
          y = op_y(opcode_q);
          z = op_z(opcode_q);
          v = tmp8_q;

          unique case (mem_rd_ctx_q)
            MEMRD_LD_R: begin
              if (mem_rd_r_q != 3'd6) begin
                set_r8(s_q, mem_rd_r_q, idx_q, v);
              end
              state_q <= ST_BOUNDARY;
            end
            MEMRD_ALU: begin
              unique case (mem_rd_aluop_q)
                Z85_ALU_ADD: o = alu_add8(s_q.A, v);
                Z85_ALU_ADC: o = alu_adc8(s_q.A, v, (s_q.F & Z85_F_C) != 0);
                Z85_ALU_SUB: o = alu_sub8(s_q.A, v);
                Z85_ALU_SBC: o = alu_sbc8(s_q.A, v, (s_q.F & Z85_F_C) != 0);
                Z85_ALU_AND: o = alu_and8(s_q.A, v);
                Z85_ALU_XOR: o = alu_xor8(s_q.A, v);
                Z85_ALU_OR:  o = alu_or8(s_q.A, v);
                default:     o = alu_cp8(s_q.A, v, s_q.F);
              endcase
              if (mem_rd_aluop_q == Z85_ALU_CP) begin
                s_q.F <= o.f;
              end else begin
                s_q.A <= o.res;
                s_q.F <= o.f;
              end
              state_q <= ST_BOUNDARY;
            end
            MEMRD_INCDEC: begin
              if (mem_rd_inc_q) o = alu_inc8(v, s_q.F);
              else o = alu_dec8(v, s_q.F);
              s_q.F <= o.f;
              start_bus_write(1'b0, mem_addr_q, o.res, ST_BOUNDARY);
            end
            MEMRD_IN: begin
              o = alu_in8_flags(v, s_q.F);
              if (mem_rd_r_q != 3'd6) set_r8(s_q, mem_rd_r_q, Z85_IDX_NONE, v);
              s_q.F <= o.f;
              state_q <= ST_BOUNDARY;
            end
            MEMRD_TST: begin
              o = alu_and8(s_q.A, v);
              s_q.F <= o.f;
              state_q <= ST_BOUNDARY;
            end
            MEMRD_BLOCK_LD: begin
              logic [15:0] hl;
              logic [15:0] de;
              logic [15:0] bc;
              logic [15:0] hl_next;
              logic [15:0] de_next;
              logic [15:0] bc_next;
              hl = get_HL(s_q);
              de = {s_q.D, s_q.E};
              bc = {s_q.B, s_q.C};
              bc_next = bc - 16'd1;
              if (block_dir_q) begin
                hl_next = hl - 16'd1;
                de_next = de - 16'd1;
              end else begin
                hl_next = hl + 16'd1;
                de_next = de + 16'd1;
              end
              set_HL(s_q, hl_next);
              s_q.D <= de_next[15:8];
              s_q.E <= de_next[7:0];
              s_q.B <= bc_next[15:8];
              s_q.C <= bc_next[7:0];
              s_q.F <= flags_ld_block(s_q.F, s_q.A, v, bc_next);
              start_bus_write(1'b0, block_addr_q, v, ST_BLOCK_DONE);
            end
            MEMRD_BLOCK_CP: begin
              logic [15:0] hl;
              logic [15:0] bc;
              logic [15:0] hl_next;
              logic [15:0] bc_next;
              hl = get_HL(s_q);
              bc = {s_q.B, s_q.C};
              bc_next = bc - 16'd1;
              if (block_dir_q) hl_next = hl - 16'd1;
              else hl_next = hl + 16'd1;
              set_HL(s_q, hl_next);
              s_q.B <= bc_next[15:8];
              s_q.C <= bc_next[7:0];
              s_q.F <= flags_cp_block(s_q.F, s_q.A, v, bc_next);
              state_q <= ST_BLOCK_DONE;
            end
            MEMRD_BLOCK_IN: begin
              logic [15:0] hl;
              logic [15:0] hl_next;
              logic [7:0] b_next;
              hl = get_HL(s_q);
              b_next = s_q.B - 8'd1;
              if (block_dir_q) hl_next = hl - 16'd1;
              else hl_next = hl + 16'd1;
              set_HL(s_q, hl_next);
              s_q.B <= b_next;
              s_q.F <= flags_block_io(v, b_next, s_q.C, hl_next[7:0], 1'b1, !block_dir_q);
              start_bus_write(1'b0, block_addr_q, v, ST_BLOCK_DONE);
            end
            MEMRD_BLOCK_OUT: begin
              logic [15:0] hl;
              logic [15:0] hl_next;
              logic [7:0] b_next;
              hl = get_HL(s_q);
              b_next = s_q.B - 8'd1;
              if (block_dir_q) hl_next = hl - 16'd1;
              else hl_next = hl + 16'd1;
              set_HL(s_q, hl_next);
              s_q.B <= b_next;
              s_q.F <= flags_block_io(v, b_next, s_q.C, hl_next[7:0], 1'b0, !block_dir_q);
              start_bus_write(1'b1, block_port_q, v, ST_BLOCK_DONE);
            end
            MEMRD_RLD: begin
              logic [7:0] new_mem;
              logic [7:0] new_a;
              new_mem = {v[3:0], s_q.A[3:0]};
              new_a = {s_q.A[7:4], v[7:4]};
              s_q.A <= new_a;
              s_q.F <= (s_q.F & Z85_F_C) | flags_szp_xy(new_a);
              start_bus_write(1'b0, mem_addr_q, new_mem, ST_BOUNDARY);
            end
            MEMRD_RRD: begin
              logic [7:0] new_mem;
              logic [7:0] new_a;
              new_mem = {s_q.A[3:0], v[7:4]};
              new_a = {s_q.A[7:4], v[3:0]};
              s_q.A <= new_a;
              s_q.F <= (s_q.F & Z85_F_C) | flags_szp_xy(new_a);
              start_bus_write(1'b0, mem_addr_q, new_mem, ST_BOUNDARY);
            end
            MEMRD_CB: begin
              if (x == 2'd0) begin
                o = alu_rotshift(y, v, s_q.F);
                res = o.res;
                s_q.F <= o.f;
                if (grp_q == Z85_GRP_DDCB && z != 3'd6) set_r8(s_q, z, Z85_IDX_NONE, res);
                start_bus_write(1'b0, mem_addr_q, res, ST_BOUNDARY);
              end else if (x == 2'd1) begin
                s_q.F <= flags_bitop(y, v, s_q.F, (grp_q == Z85_GRP_DDCB) ? mem_addr_q[15:8] : v);
                state_q <= ST_BOUNDARY;
              end else begin
                res = v;
                res[y] = (x == 2'd3);
                if (grp_q == Z85_GRP_DDCB && z != 3'd6) set_r8(s_q, z, Z85_IDX_NONE, res);
                start_bus_write(1'b0, mem_addr_q, res, ST_BOUNDARY);
              end
            end
            default: state_q <= ST_BOUNDARY;
          endcase
        end

        ST_STACK_POP_LO: begin
          start_bus_read(1'b0, s_q.SP, DEST_TMP16_LO, ST_STACK_POP_HI);
          s_q.SP <= s_q.SP + 16'd1;
        end

        ST_STACK_POP_HI: begin
          start_bus_read(1'b0, s_q.SP, DEST_TMP16_HI, ST_STACK_POP_DONE);
          s_q.SP <= s_q.SP + 16'd1;
        end

        ST_STACK_POP_DONE: begin
          if (stack_pop_ctx_q == STACK_POP_PC) begin
            s_q.PC <= tmp16_q;
            if (stack_pop_restore_iff_q) s_q.IFF1 <= s_q.IFF2;
          end else if (stack_pop_ctx_q == STACK_POP_PP) begin
            if (stack_pop_pp_q == 2'd3) begin
              s_q.A <= tmp16_q[15:8];
              s_q.F <= tmp16_q[7:0];
            end else begin
              set_pp(s_q, stack_pop_pp_q, stack_pop_use_idx_q ? idx_q : Z85_IDX_NONE, tmp16_q);
            end
          end
          stack_pop_ctx_q <= STACK_POP_NONE;
          stack_pop_restore_iff_q <= 1'b0;
          state_q <= ST_BOUNDARY;
        end

        ST_EX_SP_HI: begin
          start_bus_read(1'b0, mem_addr_q + 16'd1, DEST_TMP16_HI, ST_EX_SP_WR_LO);
        end

        ST_EX_SP_WR_LO: begin
          set_ss(s_q, 2'd2, idx_q, tmp16_q);
          start_bus_write(1'b0, mem_addr_q, ex_sp_val_q[7:0], ST_EX_SP_WR_HI);
        end

        ST_EX_SP_WR_HI: begin
          start_bus_write(1'b0, mem_addr_q + 16'd1, ex_sp_val_q[15:8], ST_BOUNDARY);
        end

        ST_BLOCK_DONE: begin
          case (block_kind_q)
            BLOCK_LD: begin
              if (block_repeat_q && {s_q.B, s_q.C} != 16'h0000) s_q.PC <= insn_pc_q;
            end
            BLOCK_CP: begin
              if (block_repeat_q && {s_q.B, s_q.C} != 16'h0000 && (s_q.F & Z85_F_Z) == 0) s_q.PC <= insn_pc_q;
            end
            BLOCK_IN, BLOCK_OUT: begin
              if (block_repeat_q && s_q.B != 8'h00) s_q.PC <= insn_pc_q;
            end
            default: begin end
          endcase
          state_q <= ST_BOUNDARY;
        end

        // Interrupt microsequence
        ST_INT_PUSH_HI: begin
          s_q.SP <= s_q.SP - 16'd1;
          bus_is_io_q <= 1'b0;
          bus_op_q <= FAB_OP_W'(CARBON_FABRIC_XACT_WRITE);
          bus_addr_q <= FAB_ADDR_W'({{(FAB_ADDR_W-16){1'b0}}, (s_q.SP - 16'd1)});
          bus_wdata_q <= FAB_DATA_W'({{(FAB_DATA_W-8){1'b0}}, stack_push_val_q[15:8]});
          bus_wstrb_q <= FAB_STRB_W'({{(FAB_STRB_W-1){1'b0}}, 1'b1});
          bus_size_q <= '0;
          bus_attr_q <= MEM_ATTR;
          bus_dest_q <= DEST_NONE;
          state_after_bus_q <= ST_INT_PUSH_LO;
          state_q <= ST_BUS_REQ;
        end

        ST_INT_PUSH_LO: begin
          s_q.SP <= s_q.SP - 16'd1;
          bus_is_io_q <= 1'b0;
          bus_op_q <= FAB_OP_W'(CARBON_FABRIC_XACT_WRITE);
          bus_addr_q <= FAB_ADDR_W'({{(FAB_ADDR_W-16){1'b0}}, (s_q.SP - 16'd1)});
          bus_wdata_q <= FAB_DATA_W'({{(FAB_DATA_W-8){1'b0}}, stack_push_val_q[7:0]});
          bus_wstrb_q <= FAB_STRB_W'({{(FAB_STRB_W-1){1'b0}}, 1'b1});
          bus_size_q <= '0;
          bus_attr_q <= MEM_ATTR;
          bus_dest_q <= DEST_NONE;
          state_after_bus_q <= stack_push_next_q;
          state_q <= ST_BUS_REQ;
        end

        ST_INT_VECTOR: begin
          if (int_is_nmi_q) begin
            s_q.PC <= 16'h0066;
            state_q <= ST_BOUNDARY;
          end else begin
            unique case (s_q.IM)
              2'd1: begin
                s_q.PC <= 16'h0038;
                state_q <= ST_BOUNDARY;
              end
              2'd2: begin
                bus_is_io_q <= 1'b0;
                bus_op_q <= FAB_OP_W'(CARBON_FABRIC_XACT_READ);
                bus_addr_q <= FAB_ADDR_W'({{(FAB_ADDR_W-16){1'b0}}, {s_q.I, int_vec_q}});
                bus_attr_q <= MEM_ATTR;
                bus_wdata_q <= '0;
                bus_wstrb_q <= '0;
                bus_size_q <= '0;
                bus_dest_q <= DEST_TMP16_LO;
                state_after_bus_q <= ST_INT_IM2_HI;
                state_q <= ST_BUS_REQ;
              end
              default: begin
                // IM0: execute provided opcode as an injected M1 fetch.
                opcode_q <= int_vec_q;
                grp_q <= Z85_GRP_BASE;
                idx_q <= Z85_IDX_NONE;
                disp_q <= '0;
                insn_pc_q <= s_q.PC;
                r_inc_on_opcode_fetch(s_q);
                state_q <= ST_DECODE;
              end
            endcase
          end
        end

        ST_INT_IM2_HI: begin
          bus_is_io_q <= 1'b0;
          bus_op_q <= FAB_OP_W'(CARBON_FABRIC_XACT_READ);
          bus_addr_q <= FAB_ADDR_W'({{(FAB_ADDR_W-16){1'b0}}, ({s_q.I, int_vec_q} + 16'd1)});
          bus_attr_q <= MEM_ATTR;
          bus_wdata_q <= '0;
          bus_wstrb_q <= '0;
          bus_size_q <= '0;
          bus_dest_q <= DEST_TMP16_HI;
          state_after_bus_q <= ST_INT_IM2_SETPC;
          state_q <= ST_BUS_REQ;
        end

        ST_INT_IM2_SETPC: begin
          s_q.PC <= tmp16_q;
          state_q <= ST_BOUNDARY;
        end

        default: begin
          trapped_q <= 1'b1;
          core_trap_pulse_q <= 1'b1;
          core_trap_cause_q <= Z380_CAUSE_ILLEGAL_INSN;
          core_trap_epc_q <= {16'h0000, insn_pc_q};
          state_q <= ST_TRAP;
        end
      endcase
    end
  end

endmodule : z380_core
