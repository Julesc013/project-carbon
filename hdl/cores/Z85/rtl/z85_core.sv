// Project Carbon - Z85 core (strict Z80 engine)
// z85_core: Minimal strict Z80-compatible core scaffolding.

module z85_core (
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
    if (IRQ_VEC_W < 8) $fatal(1, "z85_core: irq_if vector width must be >= 8");
  end
`endif

  localparam logic [FAB_ATTR_W-1:0] MEM_ATTR =
      FAB_ATTR_W'(CARBON_FABRIC_ATTR_CACHEABLE_MASK);
  localparam logic [FAB_ATTR_W-1:0] IO_ATTR =
      FAB_ATTR_W'(CARBON_FABRIC_ATTR_ORDERED_MASK | CARBON_FABRIC_ATTR_IO_SPACE_MASK);

  // --------------------------------------------------------------------------
  // Core-local trap causes (implementation-defined)
  // --------------------------------------------------------------------------
  localparam logic [31:0] Z85_CAUSE_ILLEGAL_INSN = 32'h0000_0001;
  localparam logic [31:0] Z85_CAUSE_BUS_FAULT    = 32'h0000_0002;
  localparam logic [31:0] Z85_CAUSE_IM0_UNSUP    = 32'h0000_0003;

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

  localparam logic [31:0] Z85_FEAT_WORD0 =
      CARBON_FEAT_MODE_SWITCH_MASK |
      CARBON_FEAT_CSR_NAMESPACE_MASK |
      CARBON_FEAT_FABRIC_MASK |
      CARBON_FEAT_CAPS_MASK |
      CARBON_FEAT_POLLING_COMPLETE_MASK |
      CARBON_Z85_UNDOC_Z80_MASK;

  localparam logic [7:0] Z85_VENDOR_ID  = 8'h00;
  localparam logic [7:0] Z85_FAMILY_ID  = 8'h85;
  localparam logic [7:0] Z85_MODEL_ID   = 8'h01;
  localparam logic [7:0] Z85_STEPPING   = 8'h00;
  localparam logic [31:0] Z85_VENDOR0   = "CARB";
  localparam logic [31:0] Z85_VENDOR1   = "ON Z";
  localparam logic [31:0] Z85_VENDOR2   = "85  ";

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
          w1 = Z85_VENDOR0;
          w2 = Z85_VENDOR1;
          w3 = Z85_VENDOR2;
        end
        CARBON_CPUID_LEAF_ID: begin
          w0 = {Z85_STEPPING, Z85_MODEL_ID, Z85_FAMILY_ID, Z85_VENDOR_ID};
          w1 = 32'h0;
        end
        CARBON_CPUID_LEAF_TIERS: begin
          w0 = {8'h00,
                8'(CARBON_Z80_DERIVED_TIER_P2_Z80),
                8'(CARBON_Z80_DERIVED_TIER_P2_Z80),
                8'(CARBON_TIER_LADDER_Z80)};
          w1 = {8'h00,
                8'(CARBON_AMD_FPU_TIER_P0_AM9511),
                8'(CARBON_AMD_FPU_TIER_P0_AM9511),
                8'(CARBON_TIER_LADDER_AMD_FPU)};
        end
        CARBON_CPUID_LEAF_FEATURES0: begin
          w0 = Z85_FEAT_WORD0;
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
      csr_modeflags_q <= CARBON_MODEFLAG_STRICT_MASK;
      csr_tier_q      <= 8'(CARBON_Z80_DERIVED_TIER_P0_I8080);
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
            if (!csr.req_write) csr_rsp_rdata_q <= 32'h5A38_3501; // "Z85"+v1
            else csr_rsp_fault_q <= 1'b1;
          end
          CARBON_CSR_TIER: begin
            if (!csr.req_write) csr_rsp_rdata_q[7:0] <= csr_tier_q;
            else csr_rsp_fault_q <= 1'b1;
          end
          CARBON_CSR_MODEFLAGS: begin
            if (!csr.req_write) csr_rsp_rdata_q[7:0] <= csr_modeflags_q;
            else begin
              csr_modeflags_q <= csr.req_wdata[7:0] & (CARBON_MODEFLAG_STRICT_MASK | CARBON_MODEFLAG_INTMASK_MASK);
              csr_rsp_side_q <= 1'b1;
            end
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

  typedef enum logic [4:0] {
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
  typedef enum logic [3:0] {
    IMM8_NONE = 4'd0,
    IMM8_LD_R,
    IMM8_LD_MEM,
    IMM8_ALU_A
  } imm8_ctx_e;
  imm8_ctx_e imm8_ctx_q;
  logic [2:0] imm8_r_q;
  logic [2:0] imm8_aluop_q;
  logic [15:0] mem_addr_q;

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
      mem_addr_q <= '0;

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
              state_q <= ST_INT_PUSH_HI;
            end else if (irq.irq_valid && !irq_is_nmi && s_q.IFF1 && !ei_delay_q) begin
              irq_ack_q <= 1'b1;
              irq_ack_vec_q <= irq.irq_vector;
              int_is_nmi_q <= 1'b0;
              int_vec_q <= irq_byte;
              s_q.halt_latch <= 1'b0;
              s_q.IFF1 <= 1'b0;
              s_q.IFF2 <= 1'b0;
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
              core_trap_cause_q <= Z85_CAUSE_BUS_FAULT;
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
          handled = 1'b0;

          // BASE subset
          if (grp_q == Z85_GRP_BASE) begin
            logic [1:0] x;
            logic [2:0] y, z;
            x = op_x(opcode_q);
            y = op_y(opcode_q);
            z = op_z(opcode_q);

            if (opcode_q == 8'h00) begin
              handled = 1'b1;
              state_q <= ST_BOUNDARY;
            end else if (opcode_q == 8'h76) begin
              handled = 1'b1;
              s_q.halt_latch <= 1'b1;
              state_q <= ST_BOUNDARY;
            end else if (opcode_q == 8'hF3) begin
              handled = 1'b1;
              s_q.IFF1 <= 1'b0;
              s_q.IFF2 <= 1'b0;
              ei_delay_q <= 1'b0;
              state_q <= ST_BOUNDARY;
            end else if (opcode_q == 8'hFB) begin
              handled = 1'b1;
              s_q.IFF1 <= 1'b1;
              s_q.IFF2 <= 1'b1;
              ei_delay_q <= 1'b1;
              state_q <= ST_BOUNDARY;
            end else if (opcode_q == 8'h27) begin
              handled = 1'b1;
              begin
                z85_alu8_t o;
                o = alu_daa(s_q.A, s_q.F);
                s_q.A <= o.res;
                s_q.F <= o.f;
              end
              state_q <= ST_BOUNDARY;
            end else if (x == 2'd0 && z == 3'd6) begin
              // LD r,n
              handled = 1'b1;
              imm8_ctx_q <= (y == 3'd6) ? IMM8_LD_MEM : IMM8_LD_R;
              imm8_r_q <= y;
              mem_addr_q <= hl_eff_addr(s_q, idx_q, disp_q);

              bus_is_io_q <= 1'b0;
              bus_op_q <= FAB_OP_W'(CARBON_FABRIC_XACT_READ);
              bus_addr_q <= FAB_ADDR_W'({{(FAB_ADDR_W-16){1'b0}}, s_q.PC});
              bus_attr_q <= MEM_ATTR;
              bus_wdata_q <= '0;
              bus_wstrb_q <= '0;
              bus_size_q <= '0;
              bus_dest_q <= DEST_IMM8;
              state_after_bus_q <= ST_IMM8_DONE;
              state_q <= ST_BUS_REQ;
            end else if (opcode_q == 8'h21 || opcode_q == 8'h31) begin
              // LD HL/IX/IY,nn (21) and LD SP,nn (31)
              handled = 1'b1;
              imm16_q <= '0;
              bus_is_io_q <= 1'b0;
              bus_op_q <= FAB_OP_W'(CARBON_FABRIC_XACT_READ);
              bus_addr_q <= FAB_ADDR_W'({{(FAB_ADDR_W-16){1'b0}}, s_q.PC});
              bus_attr_q <= MEM_ATTR;
              bus_wdata_q <= '0;
              bus_wstrb_q <= '0;
              bus_size_q <= '0;
              bus_dest_q <= DEST_IMM16_LO;
              state_after_bus_q <= ST_IMM16_HI;
              state_q <= ST_BUS_REQ;
            end else if (opcode_q == 8'hC6 || opcode_q == 8'hCE || opcode_q == 8'hD6 || opcode_q == 8'hDE) begin
              // ADD/ADC/SUB/SBC A,n
              handled = 1'b1;
              imm8_ctx_q <= IMM8_ALU_A;
              imm8_aluop_q <= (opcode_q == 8'hC6) ? Z85_ALU_ADD :
                              (opcode_q == 8'hCE) ? Z85_ALU_ADC :
                              (opcode_q == 8'hD6) ? Z85_ALU_SUB : Z85_ALU_SBC;

              bus_is_io_q <= 1'b0;
              bus_op_q <= FAB_OP_W'(CARBON_FABRIC_XACT_READ);
              bus_addr_q <= FAB_ADDR_W'({{(FAB_ADDR_W-16){1'b0}}, s_q.PC});
              bus_attr_q <= MEM_ATTR;
              bus_wdata_q <= '0;
              bus_wstrb_q <= '0;
              bus_size_q <= '0;
              bus_dest_q <= DEST_IMM8;
              state_after_bus_q <= ST_IMM8_DONE;
              state_q <= ST_BUS_REQ;
            end
          end

          // CB / DDCB subset (ROT/SHIFT/BIT/RES/SET)
          if (!handled && (grp_q == Z85_GRP_CB || grp_q == Z85_GRP_DDCB)) begin
            logic [1:0] x;
            logic [2:0] y, z;
            logic [15:0] ea;
            x = op_x(opcode_q);
            y = op_y(opcode_q);
            z = op_z(opcode_q);
            ea = (grp_q == Z85_GRP_DDCB) ? hl_eff_addr(s_q, idx_q, disp_q) : get_HL(s_q);

            if (grp_q == Z85_GRP_DDCB || z == 3'd6) begin
              handled = 1'b1;
              mem_addr_q <= ea;
              bus_is_io_q <= 1'b0;
              bus_op_q <= FAB_OP_W'(CARBON_FABRIC_XACT_READ);
              bus_addr_q <= FAB_ADDR_W'({{(FAB_ADDR_W-16){1'b0}}, ea});
              bus_attr_q <= MEM_ATTR;
              bus_wdata_q <= '0;
              bus_wstrb_q <= '0;
              bus_size_q <= '0;
              bus_dest_q <= DEST_TMP8;
              state_after_bus_q <= ST_MEM_RD_DONE;
              state_q <= ST_BUS_REQ;
            end else begin
              handled = 1'b1;
              logic [7:0] v;
              v = get_r8(s_q, z, Z85_IDX_NONE);
              if (x == 2'd0) begin
                z85_alu8_t o;
                o = alu_rotshift(y, v, s_q.F);
                set_r8(s_q, z, Z85_IDX_NONE, o.res);
                s_q.F <= o.f;
              end else if (x == 2'd1) begin
                s_q.F <= flags_bitop(y, v, s_q.F, v);
              end else if (x == 2'd2) begin
                v[y] = 1'b0;
                set_r8(s_q, z, Z85_IDX_NONE, v);
              end else begin
                v[y] = 1'b1;
                set_r8(s_q, z, Z85_IDX_NONE, v);
              end
              state_q <= ST_BOUNDARY;
            end
          end

          // ED subset: LD I,A and IM0/1/2
          if (!handled && grp_q == Z85_GRP_ED) begin
            if (opcode_q == 8'h47) begin
              handled = 1'b1;
              s_q.I <= s_q.A;
              state_q <= ST_BOUNDARY;
            end else if (opcode_q == 8'h5E || opcode_q == 8'h7E) begin
              handled = 1'b1;
              s_q.IM <= 2'd2;
              state_q <= ST_BOUNDARY;
            end else if (opcode_q == 8'h56 || opcode_q == 8'h76) begin
              handled = 1'b1;
              s_q.IM <= 2'd1;
              state_q <= ST_BOUNDARY;
            end else if (opcode_q == 8'h46 || opcode_q == 8'h4E) begin
              handled = 1'b1;
              s_q.IM <= 2'd0;
              state_q <= ST_BOUNDARY;
            end
          end

          if (!handled) begin
            trapped_q <= 1'b1;
            core_trap_pulse_q <= 1'b1;
            core_trap_cause_q <= Z85_CAUSE_ILLEGAL_INSN;
            core_trap_epc_q <= {16'h0000, insn_pc_q};
            state_q <= ST_TRAP;
          end
        end

        ST_IMM8_DONE: begin
          unique case (imm8_ctx_q)
            IMM8_LD_R: begin
              set_r8(s_q, imm8_r_q, idx_q, imm8_q);
              state_q <= ST_BOUNDARY;
            end
            IMM8_LD_MEM: begin
              bus_is_io_q <= 1'b0;
              bus_op_q <= FAB_OP_W'(CARBON_FABRIC_XACT_WRITE);
              bus_addr_q <= FAB_ADDR_W'({{(FAB_ADDR_W-16){1'b0}}, mem_addr_q});
              bus_wdata_q <= FAB_DATA_W'({{(FAB_DATA_W-8){1'b0}}, imm8_q});
              bus_wstrb_q <= FAB_STRB_W'({{(FAB_STRB_W-1){1'b0}}, 1'b1});
              bus_size_q <= '0;
              bus_attr_q <= MEM_ATTR;
              bus_dest_q <= DEST_NONE;
              state_after_bus_q <= ST_BOUNDARY;
              state_q <= ST_BUS_REQ;
            end
            IMM8_ALU_A: begin
              z85_alu8_t o;
              unique case (imm8_aluop_q)
                Z85_ALU_ADD: o = alu_add8(s_q.A, imm8_q);
                Z85_ALU_ADC: o = alu_adc8(s_q.A, imm8_q, (s_q.F & Z85_F_C) != 0);
                Z85_ALU_SUB: o = alu_sub8(s_q.A, imm8_q);
                default:     o = alu_sbc8(s_q.A, imm8_q, (s_q.F & Z85_F_C) != 0);
              endcase
              s_q.A <= o.res;
              s_q.F <= o.f;
              state_q <= ST_BOUNDARY;
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
          if (opcode_q == 8'h31) begin
            s_q.SP <= imm16_q;
          end else begin
            set_ss(s_q, 2'd2, idx_q, imm16_q);
          end
          state_q <= ST_BOUNDARY;
        end

        ST_MEM_RD_DONE: begin
          logic [1:0] x;
          logic [2:0] y, z;
          logic [7:0] v;
          logic [7:0] res;
          x = op_x(opcode_q);
          y = op_y(opcode_q);
          z = op_z(opcode_q);
          v = tmp8_q;

          if (x == 2'd0) begin
            z85_alu8_t o;
            o = alu_rotshift(y, v, s_q.F);
            res = o.res;
            s_q.F <= o.f;
            if (grp_q == Z85_GRP_DDCB && z != 3'd6) begin
              set_r8(s_q, z, Z85_IDX_NONE, res);
            end
            bus_is_io_q <= 1'b0;
            bus_op_q <= FAB_OP_W'(CARBON_FABRIC_XACT_WRITE);
            bus_addr_q <= FAB_ADDR_W'({{(FAB_ADDR_W-16){1'b0}}, mem_addr_q});
            bus_wdata_q <= FAB_DATA_W'({{(FAB_DATA_W-8){1'b0}}, res});
            bus_wstrb_q <= FAB_STRB_W'({{(FAB_STRB_W-1){1'b0}}, 1'b1});
            bus_size_q <= '0;
            bus_attr_q <= MEM_ATTR;
            bus_dest_q <= DEST_NONE;
            state_after_bus_q <= ST_BOUNDARY;
            state_q <= ST_BUS_REQ;
          end else if (x == 2'd1) begin
            s_q.F <= flags_bitop(y, v, s_q.F, (grp_q == Z85_GRP_DDCB) ? mem_addr_q[15:8] : v);
            state_q <= ST_BOUNDARY;
          end else begin
            res = v;
            res[y] = (x == 2'd3);
            if (grp_q == Z85_GRP_DDCB && z != 3'd6) begin
              set_r8(s_q, z, Z85_IDX_NONE, res);
            end
            bus_is_io_q <= 1'b0;
            bus_op_q <= FAB_OP_W'(CARBON_FABRIC_XACT_WRITE);
            bus_addr_q <= FAB_ADDR_W'({{(FAB_ADDR_W-16){1'b0}}, mem_addr_q});
            bus_wdata_q <= FAB_DATA_W'({{(FAB_DATA_W-8){1'b0}}, res});
            bus_wstrb_q <= FAB_STRB_W'({{(FAB_STRB_W-1){1'b0}}, 1'b1});
            bus_size_q <= '0;
            bus_attr_q <= MEM_ATTR;
            bus_dest_q <= DEST_NONE;
            state_after_bus_q <= ST_BOUNDARY;
            state_q <= ST_BUS_REQ;
          end
        end

        // Interrupt microsequence
        ST_INT_PUSH_HI: begin
          s_q.SP <= s_q.SP - 16'd1;
          bus_is_io_q <= 1'b0;
          bus_op_q <= FAB_OP_W'(CARBON_FABRIC_XACT_WRITE);
          bus_addr_q <= FAB_ADDR_W'({{(FAB_ADDR_W-16){1'b0}}, (s_q.SP - 16'd1)});
          bus_wdata_q <= FAB_DATA_W'({{(FAB_DATA_W-8){1'b0}}, s_q.PC[15:8]});
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
          bus_wdata_q <= FAB_DATA_W'({{(FAB_DATA_W-8){1'b0}}, s_q.PC[7:0]});
          bus_wstrb_q <= FAB_STRB_W'({{(FAB_STRB_W-1){1'b0}}, 1'b1});
          bus_size_q <= '0;
          bus_attr_q <= MEM_ATTR;
          bus_dest_q <= DEST_NONE;
          state_after_bus_q <= ST_INT_VECTOR;
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
                if ((int_vec_q & 8'hC7) == 8'hC7) begin
                  s_q.PC <= {13'b0, int_vec_q[5:3], 3'b000};
                  state_q <= ST_BOUNDARY;
                end else begin
                  trapped_q <= 1'b1;
                  core_trap_pulse_q <= 1'b1;
                  core_trap_cause_q <= Z85_CAUSE_IM0_UNSUP;
                  core_trap_epc_q <= {16'h0000, insn_pc_q};
                  state_q <= ST_TRAP;
                end
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
          core_trap_cause_q <= Z85_CAUSE_ILLEGAL_INSN;
          core_trap_epc_q <= {16'h0000, insn_pc_q};
          state_q <= ST_TRAP;
        end
      endcase
    end
  end

endmodule : z85_core
