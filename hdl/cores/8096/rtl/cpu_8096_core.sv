// Project Carbon - 8096 CPU core (v1.0)
// cpu_8096_core: In-order 8086-compatible functional subset with turbo (P7) hooks.

module cpu_8096_core #(
    parameter int unsigned MODESTACK_DEPTH = carbon_arch_pkg::CARBON_MODESTACK_RECOMMENDED_DEPTH,
    parameter int unsigned PREFETCH_DEPTH  = 6
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
  import cpu_8096_pkg::*;

  localparam int unsigned FAB_ADDR_W = $bits(mem_if.req_addr);
  localparam int unsigned FAB_DATA_W = $bits(mem_if.req_wdata);
  localparam int unsigned FAB_STRB_W = $bits(mem_if.req_wstrb);
  localparam int unsigned FAB_OP_W   = $bits(mem_if.req_op);
  localparam int unsigned FAB_SIZE_W = $bits(mem_if.req_size);
  localparam int unsigned FAB_ATTR_W = $bits(mem_if.req_attr);
  localparam int unsigned FAB_ID_W   = $bits(mem_if.req_id);
  localparam int unsigned FAB_CODE_W = $bits(mem_if.rsp_code);

  localparam int unsigned CSR_DATA_W = $bits(csr.req_wdata);
  localparam int unsigned CSR_PRIV_W = $bits(csr.req_priv);

  localparam int unsigned PF_HEAD_W  = (PREFETCH_DEPTH < 2) ? 1 : $clog2(PREFETCH_DEPTH);
  localparam int unsigned PF_COUNT_W = (PREFETCH_DEPTH < 2) ? 1 : $clog2(PREFETCH_DEPTH + 1);

  localparam int unsigned MD_SP_W =
      (MODESTACK_DEPTH < 2) ? 1 : $clog2(MODESTACK_DEPTH + 1);

`ifndef SYNTHESIS
  initial begin
    if (MODESTACK_DEPTH < CARBON_MODESTACK_MIN_DEPTH) begin
      $fatal(1, "cpu_8096_core: MODESTACK_DEPTH must be >= CARBON_MODESTACK_MIN_DEPTH");
    end
    if (PREFETCH_DEPTH < 2) begin
      $fatal(1, "cpu_8096_core: PREFETCH_DEPTH must be >= 2");
    end
  end
`endif

  localparam logic [FAB_ATTR_W-1:0] MEM_ATTR =
      FAB_ATTR_W'(CARBON_FABRIC_ATTR_CACHEABLE_MASK);

  // IO bus is unused by the v1 subset; keep it idle.
  assign io_if.req_valid = 1'b0;
  assign io_if.req_op    = '0;
  assign io_if.req_addr  = '0;
  assign io_if.req_wdata = '0;
  assign io_if.req_wstrb = '0;
  assign io_if.req_size  = '0;
  assign io_if.req_attr  = FAB_ATTR_W'(CARBON_FABRIC_ATTR_ORDERED_MASK | CARBON_FABRIC_ATTR_IO_SPACE_MASK);
  assign io_if.req_id    = '0;
  assign io_if.rsp_ready = 1'b0;

  // External IRQ interface (not implemented in v1)
  assign irq.irq_ack = 1'b0;
  assign irq.irq_ack_vector = '0;

  // --------------------------------------------------------------------------
  // Debug/stop control
  // --------------------------------------------------------------------------
  logic halt_debug_q;
  logic halt_instr_q;
  logic halt_trap_q;
  logic step_token_q;
  logic step_ack_pulse_q;

  wire core_halted = halt_debug_q || halt_instr_q || halt_trap_q;

  assign dbg.halt_ack    = core_halted;
  assign dbg.step_ack    = step_ack_pulse_q;
  assign dbg.bp_ready    = 1'b1;
  assign dbg.trace_valid = 1'b0;
  assign dbg.trace_data  = '0;
  assign dbg.trace_ready = 1'b1;

  // --------------------------------------------------------------------------
  // CSR interface (minimal core-common subset)
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
  // Trap causes (implementation-defined, v1 scaffold)
  localparam logic [31:0] X96_CAUSE_ILLEGAL_INSN        = 32'h0000_0001;
  localparam logic [31:0] X96_CAUSE_BUS_FAULT           = 32'h0000_0002;
  localparam logic [31:0] X96_CAUSE_MODESTACK_OVERFLOW  = 32'h0000_0010;
  localparam logic [31:0] X96_CAUSE_MODESTACK_UNDERFLOW = 32'h0000_0011;
  localparam logic [31:0] X96_CAUSE_MODEUP_INVALID      = 32'h0000_0012;
  localparam logic [31:0] X96_CAUSE_TURBO_DENIED        = 32'h0000_0020;
  localparam logic [31:0] X96_CAUSE_UNIMPL_TIER         = 32'h0000_0030;
  localparam logic [31:0] X96_CAUSE_INTN                = 32'h0000_0100; // | imm8

  // --------------------------------------------------------------------------
  // Execution state machine
  // --------------------------------------------------------------------------
  typedef enum logic [7:0] {
    ST_RESET = 8'd0,
    ST_BOUNDARY = 8'd1,
    ST_GET_BYTE = 8'd2,
    ST_DECODE_OP = 8'd3,

    ST_SYS_GET_SUB = 8'd10,
    ST_SYS_MODEUP_TIER = 8'd11,
    ST_SYS_MODEUP_IP_LO = 8'd12,
    ST_SYS_MODEUP_IP_HI = 8'd13,
    ST_SYS_MODEUP_EXEC = 8'd14,
    ST_SYS_RETMD_EXEC = 8'd15,

    ST_TURBO_GET_SUB = 8'd20,
    ST_TURBO_B0 = 8'd21,
    ST_TURBO_B1 = 8'd22,
    ST_TURBO_IMM_LO = 8'd23,
    ST_TURBO_IMM_HI = 8'd24,
    ST_TURBO_EXEC = 8'd25,

    ST_MOV_IMM_LO = 8'd30,
    ST_MOV_IMM_HI = 8'd31,
    ST_MOV_IMM_EXEC = 8'd32,

    ST_REL8 = 8'd40,
    ST_REL16_LO = 8'd41,
    ST_REL16_HI = 8'd42,
    ST_JMP_REL16_EXEC = 8'd43,
    ST_CALL_PUSH_LO = 8'd44,
    ST_CALL_PUSH_HI = 8'd45,
    ST_CALL_SETIP = 8'd46,
    ST_RET_POP_LO = 8'd47,
    ST_RET_POP_HI = 8'd48,
    ST_RET_SETIP = 8'd49,

    ST_PUSH_LO = 8'd60,
    ST_PUSH_HI = 8'd61,
    ST_POP_LO = 8'd62,
    ST_POP_HI = 8'd63,
    ST_POP_COMMIT = 8'd64,

    ST_MODRM = 8'd80,
    ST_DISP8 = 8'd81,
    ST_DISP16_LO = 8'd82,
    ST_DISP16_HI = 8'd83,
    ST_EA_READY = 8'd84,
    ST_MEM_RD_LO = 8'd85,
    ST_MEM_RD_HI = 8'd86,
    ST_MEM_RD_DONE = 8'd87,
    ST_MEM_WR_LO = 8'd88,
    ST_MEM_WR_HI = 8'd89,
    ST_MEM_WR_DONE = 8'd90,
    ST_RM_EXEC = 8'd91,

    ST_STR_START = 8'd110,
    ST_STR_RD_LO = 8'd111,
    ST_STR_RD_HI = 8'd112,
    ST_STR_WR_LO = 8'd113,
    ST_STR_WR_HI = 8'd114,
    ST_STR_UPDATE = 8'd115,

    ST_BUS_REQ = 8'd200,
    ST_BUS_RSP = 8'd201,
    ST_TRAP = 8'd250
  } state_e;

  state_e state_q;
  state_e state_after_get_q;
  state_e state_after_bus_q;

  // --------------------------------------------------------------------------
  // Core state
  // --------------------------------------------------------------------------
  logic [15:0] gpr_q [8];  // AX,CX,DX,BX,SP,BP,SI,DI
  logic [15:0] cs_q, ds_q, es_q, ss_q;
  logic [15:0] ip_q;
  logic [15:0] flags_q;

  // Turbo regs (P7 only): R0..R15, 16-bit
  logic [15:0] tr_q [16];

  logic [7:0] tier_q;
  logic [7:0] modeflags_q;

  logic [MD_SP_W-1:0] md_sp_q;
  logic [7:0]  md_tier_q  [MODESTACK_DEPTH];
  logic [7:0]  md_flags_q [MODESTACK_DEPTH];
  logic [15:0] md_ip_q    [MODESTACK_DEPTH];

  // Prefetch queue (simple FIFO with shifting, depth PREFETCH_DEPTH)
  logic [7:0] pf_q [PREFETCH_DEPTH];
  logic [PF_COUNT_W-1:0] pf_count_q;
  logic [19:0] pf_phys_base_q;

  logic [63:0] cycle_q;

  logic [31:0] csr_cause_q;
  logic [31:0] csr_epc_q;

  // --------------------------------------------------------------------------
  // Bus engine (memory only for v1)
  // --------------------------------------------------------------------------
  typedef enum logic [2:0] {
    DEST_NONE   = 3'd0,
    DEST_PF     = 3'd1,
    DEST_TMP_LO = 3'd2,
    DEST_TMP_HI = 3'd3
  } bus_dest_e;

  logic [FAB_OP_W-1:0]   bus_op_q;
  logic [FAB_ADDR_W-1:0] bus_addr_q;
  logic [FAB_DATA_W-1:0] bus_wdata_q;
  logic [FAB_STRB_W-1:0] bus_wstrb_q;
  logic [FAB_SIZE_W-1:0] bus_size_q;
  logic [FAB_ATTR_W-1:0] bus_attr_q;
  logic [FAB_ID_W-1:0]   bus_id_q;
  bus_dest_e             bus_dest_q;

  logic [7:0] tmp_lo8_q;
  logic [7:0] tmp_hi8_q;

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
  // Decode scratch
  // --------------------------------------------------------------------------
  logic [7:0]  fetch_byte_q;
  logic [7:0]  op_q;
  logic        rep_prefix_q;
  logic [7:0]  sys_subop_q;
  logic [7:0]  turbo_subop_q;

  logic [3:0]  reg_sel_q;
  logic [15:0] imm16_q;
  logic [15:0] disp16_q;

  logic [15:0] stack_val_q;
  logic [15:0] stack_sp_tmp_q;
  logic [3:0]  pop_dest_q; // 0..7 gpr, 8/10/11 seg regs, F=IP

  logic [7:0]  modrm_q;
  logic [1:0]  mod_q;
  logic [2:0]  reg_q;
  logic [2:0]  rm_q;
  logic        rm_is_reg_q;
  logic [15:0] ea_off_q;
  logic [19:0] ea_phys_q;

  logic [15:0] mem_word_q;
  logic [15:0] store_word_q;
  logic [19:0] store_phys_q;

  typedef enum logic [3:0] {
    RMOP_NONE = 4'd0,
    RMOP_MOV  = 4'd1,
    RMOP_ADD  = 4'd2,
    RMOP_SUB  = 4'd3,
    RMOP_CMP  = 4'd4,
    RMOP_AND  = 4'd5,
    RMOP_OR   = 4'd6,
    RMOP_XOR  = 4'd7,
    RMOP_TEST = 4'd8,
    RMOP_MOV_SREG_TO_RM = 4'd9,
    RMOP_MOV_RM_TO_SREG = 4'd10
  } rmop_e;

  rmop_e rmop_q;
  logic  rm_dir_reg_is_dst_q;

  // String ops scratch
  logic [1:0]  str_kind_q; // 0=MOVS,1=STOS
  logic [1:0]  str_size_q; // 1 or 2
  logic        str_rep_q;
  logic [15:0] str_count_q;
  logic [15:0] str_src_off_q;
  logic [15:0] str_dst_off_q;

  wire tier_p7 = (tier_q == 8'(CARBON_X86_DERIVED_TIER_P7_X86_64));
  wire turbo_allowed = tier_p7 && !modeflags_q[CARBON_MODEFLAG_STRICT_BIT];

  // --------------------------------------------------------------------------
  // Helpers
  // --------------------------------------------------------------------------
  function automatic logic [19:0] phys_addr(input logic [15:0] seg, input logic [15:0] off);
    logic [20:0] sum;
    begin
      sum = {seg, 4'b0000} + {5'b0, off};
      phys_addr = sum[19:0];
    end
  endfunction

  function automatic logic [15:0] flags_apply(input logic [15:0] oldf, input x96_alu16_t o, input logic write_cf);
    logic [15:0] f;
    begin
      f = oldf;
      if (write_cf) f[X96_FLAG_CF_BIT] = o.cf;
      f[X96_FLAG_PF_BIT] = o.pf;
      f[X96_FLAG_AF_BIT] = o.af;
      f[X96_FLAG_ZF_BIT] = o.zf;
      f[X96_FLAG_SF_BIT] = o.sf;
      f[X96_FLAG_OF_BIT] = o.of;
      f[1] = 1'b1;
      flags_apply = f;
    end
  endfunction

  function automatic logic jcc_take(input logic [3:0] cc);
    logic cf, pf, zf, sf, of;
    begin
      cf = flags_q[X96_FLAG_CF_BIT];
      pf = flags_q[X96_FLAG_PF_BIT];
      zf = flags_q[X96_FLAG_ZF_BIT];
      sf = flags_q[X96_FLAG_SF_BIT];
      of = flags_q[X96_FLAG_OF_BIT];
      unique case (cc)
        4'h0: jcc_take = of;
        4'h1: jcc_take = !of;
        4'h2: jcc_take = cf;
        4'h3: jcc_take = !cf;
        4'h4: jcc_take = zf;
        4'h5: jcc_take = !zf;
        4'h6: jcc_take = cf || zf;
        4'h7: jcc_take = (!cf) && (!zf);
        4'h8: jcc_take = sf;
        4'h9: jcc_take = !sf;
        4'hA: jcc_take = pf;
        4'hB: jcc_take = !pf;
        4'hC: jcc_take = (sf != of);
        4'hD: jcc_take = (sf == of);
        4'hE: jcc_take = zf || (sf != of);
        default: jcc_take = (!zf) && (sf == of);
      endcase
    end
  endfunction

  // --------------------------------------------------------------------------
  // Main sequential process (v1)
  integer i;
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      csr_rsp_valid_q <= 1'b0;
      csr_rsp_rdata_q <= '0;
      csr_rsp_fault_q <= 1'b0;
      csr_rsp_side_q  <= 1'b0;

      halt_debug_q <= 1'b0;
      halt_instr_q <= 1'b0;
      halt_trap_q  <= 1'b0;
      step_token_q <= 1'b0;
      step_ack_pulse_q <= 1'b0;

      tier_q <= 8'(CARBON_X86_DERIVED_TIER_P0_I8086_8087);
      modeflags_q <= 8'(CARBON_MODEFLAG_STRICT_MASK);
      md_sp_q <= '0;
      for (i = 0; i < MODESTACK_DEPTH; i++) begin
        md_tier_q[i]  <= 8'h00;
        md_flags_q[i] <= 8'h00;
        md_ip_q[i]    <= 16'h0000;
      end

      for (i = 0; i < 8; i++) gpr_q[i] <= 16'h0000;
      gpr_q[4] <= 16'hFFFE; // SP
      for (i = 0; i < 16; i++) tr_q[i] <= 16'h0000;

      cs_q <= 16'h0000;
      ds_q <= 16'h0000;
      es_q <= 16'h0000;
      ss_q <= 16'h0000;
      ip_q <= 16'h0000;
      flags_q <= X96_FLAGS_RESET;

      for (i = 0; i < PREFETCH_DEPTH; i++) pf_q[i] <= 8'h00;
      pf_count_q <= '0;
      pf_phys_base_q <= 20'h00000;

      cycle_q <= 64'd0;
      csr_cause_q <= '0;
      csr_epc_q   <= '0;

      bus_op_q   <= '0;
      bus_addr_q <= '0;
      bus_wdata_q <= '0;
      bus_wstrb_q <= '0;
      bus_size_q <= '0;
      bus_attr_q <= MEM_ATTR;
      bus_id_q <= '0;
      bus_dest_q <= DEST_NONE;
      tmp_lo8_q <= 8'h00;
      tmp_hi8_q <= 8'h00;

      fetch_byte_q <= 8'h00;
      op_q <= 8'h00;
      rep_prefix_q <= 1'b0;
      sys_subop_q <= 8'h00;
      turbo_subop_q <= 8'h00;
      reg_sel_q <= 4'h0;
      imm16_q <= 16'h0000;
      disp16_q <= 16'h0000;
      stack_val_q <= 16'h0000;
      stack_sp_tmp_q <= 16'h0000;
      pop_dest_q <= 4'h0;
      modrm_q <= 8'h00;
      mod_q <= 2'b00;
      reg_q <= 3'd0;
      rm_q <= 3'd0;
      rm_is_reg_q <= 1'b0;
      ea_off_q <= 16'h0000;
      ea_phys_q <= 20'h00000;
      mem_word_q <= 16'h0000;
      store_word_q <= 16'h0000;
      store_phys_q <= 20'h00000;
      rmop_q <= RMOP_NONE;
      rm_dir_reg_is_dst_q <= 1'b0;
      str_kind_q <= 2'd0;
      str_size_q <= 2'd0;
      str_rep_q <= 1'b0;
      str_count_q <= 16'h0000;
      str_src_off_q <= 16'h0000;
      str_dst_off_q <= 16'h0000;

      state_q <= ST_RESET;
      state_after_get_q <= ST_DECODE_OP;
      state_after_bus_q <= ST_BOUNDARY;
    end else begin
      cycle_q <= cycle_q + 64'd1;
      step_ack_pulse_q <= 1'b0;

      // Debug control
      if (dbg.halt_req) halt_debug_q <= 1'b1;
      if (dbg.run_req) begin
        halt_debug_q <= 1'b0;
        halt_instr_q <= 1'b0;
      end
      if (dbg.step_req && core_halted && !step_token_q) begin
        step_token_q <= 1'b1;
      end

      // CSR response lifecycle
      if (csr_rsp_fire) csr_rsp_valid_q <= 1'b0;

      if (csr_req_fire) begin
        csr_rsp_valid_q <= 1'b1;
        csr_rsp_fault_q <= 1'b0;
        csr_rsp_side_q  <= csr.req_write;
        csr_rsp_rdata_q <= '0;

        unique case (csr.req_addr)
          CARBON_CSR_ID: begin
            if (!csr.req_write) csr_rsp_rdata_q <= 32'h3830_3936; // "8096"
            else csr_rsp_fault_q <= 1'b1;
          end
          CARBON_CSR_TIER: begin
            if (!csr.req_write) csr_rsp_rdata_q[7:0] <= tier_q;
            else csr_rsp_fault_q <= 1'b1;
          end
          CARBON_CSR_MODEFLAGS: begin
            if (!csr.req_write) begin
              csr_rsp_rdata_q[7:0] <= modeflags_q;
            end else begin
              if ((csr.req_wdata[7:0] & 8'hFC) != 8'h00) begin
                csr_rsp_fault_q <= 1'b1;
              end else if (csr.req_priv < CSR_PRIV_W'(1)) begin
                csr_rsp_fault_q <= 1'b1;
              end else begin
                modeflags_q <= csr.req_wdata[7:0];
              end
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
              if (csr.req_priv < CSR_PRIV_W'(1)) csr_rsp_fault_q <= 1'b1;
              else csr_epc_q <= csr.req_wdata;
            end
          end
          CARBON_CSR_DBG_CTRL: begin
            if (!csr.req_write) begin
              csr_rsp_rdata_q[0] <= halt_debug_q;
              csr_rsp_rdata_q[1] <= halt_instr_q;
              csr_rsp_rdata_q[2] <= halt_trap_q;
            end else begin
              if (csr.req_priv < CSR_PRIV_W'(1)) begin
                csr_rsp_fault_q <= 1'b1;
              end else begin
                if (csr.req_wdata[0]) halt_debug_q <= 1'b1;
                if (csr.req_wdata[4]) halt_debug_q <= 1'b0;
              end
            end
          end
          CARBON_CSR_DBG_STEP: begin
            if (!csr.req_write) csr_rsp_fault_q <= 1'b1;
            else if (csr.req_priv < CSR_PRIV_W'(1)) csr_rsp_fault_q <= 1'b1;
            else step_token_q <= 1'b1;
          end
          CARBON_CSR_DBG_STATUS: begin
            if (!csr.req_write) csr_rsp_rdata_q[0] <= core_halted;
            else csr_rsp_fault_q <= 1'b1;
          end
          default: begin
            csr_rsp_fault_q <= 1'b1;
          end
        endcase
      end

      // Execution FSM runs only when not halted.
      if (!core_halted) begin
        unique case (state_q)
          ST_RESET: begin
            pf_phys_base_q <= phys_addr(cs_q, ip_q);
            pf_count_q <= '0;
            state_q <= ST_BOUNDARY;
          end

          ST_BOUNDARY: begin
            // Step completion / start handling.
            if (step_token_q && !halt_debug_q && !halt_trap_q && !halt_instr_q) begin
              halt_debug_q <= 1'b1;
              step_token_q <= 1'b0;
              step_ack_pulse_q <= 1'b1;
            end else if (step_token_q && halt_debug_q && !halt_trap_q && !halt_instr_q) begin
              halt_debug_q <= 1'b0;
            end else begin
              state_after_get_q <= ST_DECODE_OP;
              state_q <= ST_GET_BYTE;
            end
          end

          ST_GET_BYTE: begin
            if (pf_count_q == 0) begin
              bus_op_q <= FAB_OP_W'(CARBON_FABRIC_XACT_READ);
              bus_addr_q <= FAB_ADDR_W'({{(FAB_ADDR_W-20){1'b0}}, pf_phys_base_q});
              bus_wdata_q <= '0;
              bus_wstrb_q <= '0;
              bus_size_q <= '0;
              bus_attr_q <= MEM_ATTR;
              bus_id_q <= '0;
              bus_dest_q <= DEST_PF;
              state_after_bus_q <= ST_GET_BYTE;
              state_q <= ST_BUS_REQ;
            end else begin
              logic [15:0] ip_next;
              fetch_byte_q <= pf_q[0];
              for (i = 0; i < (PREFETCH_DEPTH - 1); i++) begin
                pf_q[i] <= pf_q[i+1];
              end
              pf_count_q <= pf_count_q - PF_COUNT_W'(1);
              ip_next = ip_q + 16'd1;
              ip_q <= ip_next;
              pf_phys_base_q <= phys_addr(cs_q, ip_next);
              state_q <= state_after_get_q;
            end
          end

          ST_DECODE_OP: begin
            op_q <= fetch_byte_q;
            unique case (fetch_byte_q)
              8'hF3: begin
                rep_prefix_q <= 1'b1;
                state_q <= ST_BOUNDARY;
              end

              8'h62: begin
                // Carbon system prefix (MODEUP/RETMD)
                rep_prefix_q <= 1'b0;
                state_after_get_q <= ST_SYS_GET_SUB;
                state_q <= ST_GET_BYTE;
              end

              8'h63: begin
                // Carbon turbo prefix (P7-only, STRICT=0 required)
                rep_prefix_q <= 1'b0;
                if (!turbo_allowed) begin
                  halt_trap_q <= 1'b1;
                  csr_cause_q <= X96_CAUSE_TURBO_DENIED;
                  csr_epc_q <= {cs_q, ip_q};
                  state_q <= ST_TRAP;
                end else begin
                  state_after_get_q <= ST_TURBO_GET_SUB;
                  state_q <= ST_GET_BYTE;
                end
              end

              8'h90: begin // NOP
                rep_prefix_q <= 1'b0;
                state_q <= ST_BOUNDARY;
              end

              8'hF4: begin // HLT
                rep_prefix_q <= 1'b0;
                halt_instr_q <= 1'b1;
                state_q <= ST_BOUNDARY;
              end

              // MOV reg16, imm16
              8'hB8,8'hB9,8'hBA,8'hBB,8'hBC,8'hBD,8'hBE,8'hBF: begin
                rep_prefix_q <= 1'b0;
                reg_sel_q <= {1'b0, fetch_byte_q[2:0]};
                state_after_get_q <= ST_MOV_IMM_LO;
                state_q <= ST_GET_BYTE;
              end

              // INC reg16
              8'h40,8'h41,8'h42,8'h43,8'h44,8'h45,8'h46,8'h47: begin
                x96_alu16_t o;
                rep_prefix_q <= 1'b0;
                o = alu_add16(gpr_q[fetch_byte_q[2:0]], 16'd1);
                gpr_q[fetch_byte_q[2:0]] <= o.res;
                flags_q <= flags_apply(flags_q, o, 1'b0);
                state_q <= ST_BOUNDARY;
              end

              // DEC reg16
              8'h48,8'h49,8'h4A,8'h4B,8'h4C,8'h4D,8'h4E,8'h4F: begin
                x96_alu16_t o;
                rep_prefix_q <= 1'b0;
                o = alu_sub16(gpr_q[fetch_byte_q[2:0]], 16'd1);
                gpr_q[fetch_byte_q[2:0]] <= o.res;
                flags_q <= flags_apply(flags_q, o, 1'b0);
                state_q <= ST_BOUNDARY;
              end

              // PUSH reg16
              8'h50,8'h51,8'h52,8'h53,8'h54,8'h55,8'h56,8'h57: begin
                rep_prefix_q <= 1'b0;
                stack_val_q <= gpr_q[fetch_byte_q[2:0]];
                stack_sp_tmp_q <= gpr_q[4] - 16'd2;
                state_q <= ST_PUSH_LO;
              end

              // POP reg16
              8'h58,8'h59,8'h5A,8'h5B,8'h5C,8'h5D,8'h5E,8'h5F: begin
                rep_prefix_q <= 1'b0;
                pop_dest_q <= {1'b0, fetch_byte_q[2:0]};
                state_q <= ST_POP_LO;
              end

              // PUSH segment regs
              8'h06: begin rep_prefix_q <= 1'b0; stack_val_q <= es_q; stack_sp_tmp_q <= gpr_q[4] - 16'd2; state_q <= ST_PUSH_LO; end
              8'h0E: begin rep_prefix_q <= 1'b0; stack_val_q <= cs_q; stack_sp_tmp_q <= gpr_q[4] - 16'd2; state_q <= ST_PUSH_LO; end
              8'h16: begin rep_prefix_q <= 1'b0; stack_val_q <= ss_q; stack_sp_tmp_q <= gpr_q[4] - 16'd2; state_q <= ST_PUSH_LO; end
              8'h1E: begin rep_prefix_q <= 1'b0; stack_val_q <= ds_q; stack_sp_tmp_q <= gpr_q[4] - 16'd2; state_q <= ST_PUSH_LO; end

              // POP segment regs (ES,SS,DS)
              8'h07: begin rep_prefix_q <= 1'b0; pop_dest_q <= 4'h8; state_q <= ST_POP_LO; end
              8'h17: begin rep_prefix_q <= 1'b0; pop_dest_q <= 4'hA; state_q <= ST_POP_LO; end
              8'h1F: begin rep_prefix_q <= 1'b0; pop_dest_q <= 4'hB; state_q <= ST_POP_LO; end

              // RET near
              8'hC3: begin
                rep_prefix_q <= 1'b0;
                pop_dest_q <= 4'hF; // IP
                state_q <= ST_POP_LO;
              end

              // INT n (stub -> trap)
              8'hCD: begin
                rep_prefix_q <= 1'b0;
                state_after_get_q <= ST_REL8;
                state_q <= ST_GET_BYTE;
              end

              // Jcc short / JMP short
              8'h70,8'h71,8'h72,8'h73,8'h74,8'h75,8'h76,8'h77,
              8'h78,8'h79,8'h7A,8'h7B,8'h7C,8'h7D,8'h7E,8'h7F,
              8'hEB: begin
                state_after_get_q <= ST_REL8;
                state_q <= ST_GET_BYTE;
              end

              // JMP near rel16 / CALL near rel16
              8'hE9,8'hE8: begin
                state_after_get_q <= ST_REL16_LO;
                state_q <= ST_GET_BYTE;
              end

              // String ops (MOVS/STOS)
              8'hA4,8'hA5,8'hAA,8'hAB: begin
                str_kind_q <= (fetch_byte_q == 8'hAA || fetch_byte_q == 8'hAB) ? 2'd1 : 2'd0;
                str_size_q <= (fetch_byte_q == 8'hA5 || fetch_byte_q == 8'hAB) ? 2'd2 : 2'd1;
                str_rep_q <= rep_prefix_q;
                str_count_q <= rep_prefix_q ? gpr_q[1] : 16'd1; // CX
                str_src_off_q <= gpr_q[6]; // SI
                str_dst_off_q <= gpr_q[7]; // DI
                rep_prefix_q <= 1'b0;
                state_q <= ST_STR_START;
              end

              // ModRM-based ops
              8'h89: begin rep_prefix_q <= 1'b0; rmop_q <= RMOP_MOV; rm_dir_reg_is_dst_q <= 1'b0; state_after_get_q <= ST_MODRM; state_q <= ST_GET_BYTE; end
              8'h8B: begin rep_prefix_q <= 1'b0; rmop_q <= RMOP_MOV; rm_dir_reg_is_dst_q <= 1'b1; state_after_get_q <= ST_MODRM; state_q <= ST_GET_BYTE; end
              8'h01: begin rep_prefix_q <= 1'b0; rmop_q <= RMOP_ADD; rm_dir_reg_is_dst_q <= 1'b0; state_after_get_q <= ST_MODRM; state_q <= ST_GET_BYTE; end
              8'h03: begin rep_prefix_q <= 1'b0; rmop_q <= RMOP_ADD; rm_dir_reg_is_dst_q <= 1'b1; state_after_get_q <= ST_MODRM; state_q <= ST_GET_BYTE; end
              8'h29: begin rep_prefix_q <= 1'b0; rmop_q <= RMOP_SUB; rm_dir_reg_is_dst_q <= 1'b0; state_after_get_q <= ST_MODRM; state_q <= ST_GET_BYTE; end
              8'h2B: begin rep_prefix_q <= 1'b0; rmop_q <= RMOP_SUB; rm_dir_reg_is_dst_q <= 1'b1; state_after_get_q <= ST_MODRM; state_q <= ST_GET_BYTE; end
              8'h39: begin rep_prefix_q <= 1'b0; rmop_q <= RMOP_CMP; rm_dir_reg_is_dst_q <= 1'b0; state_after_get_q <= ST_MODRM; state_q <= ST_GET_BYTE; end
              8'h3B: begin rep_prefix_q <= 1'b0; rmop_q <= RMOP_CMP; rm_dir_reg_is_dst_q <= 1'b1; state_after_get_q <= ST_MODRM; state_q <= ST_GET_BYTE; end
              8'h21: begin rep_prefix_q <= 1'b0; rmop_q <= RMOP_AND; rm_dir_reg_is_dst_q <= 1'b0; state_after_get_q <= ST_MODRM; state_q <= ST_GET_BYTE; end
              8'h23: begin rep_prefix_q <= 1'b0; rmop_q <= RMOP_AND; rm_dir_reg_is_dst_q <= 1'b1; state_after_get_q <= ST_MODRM; state_q <= ST_GET_BYTE; end
              8'h09: begin rep_prefix_q <= 1'b0; rmop_q <= RMOP_OR;  rm_dir_reg_is_dst_q <= 1'b0; state_after_get_q <= ST_MODRM; state_q <= ST_GET_BYTE; end
              8'h0B: begin rep_prefix_q <= 1'b0; rmop_q <= RMOP_OR;  rm_dir_reg_is_dst_q <= 1'b1; state_after_get_q <= ST_MODRM; state_q <= ST_GET_BYTE; end
              8'h31: begin rep_prefix_q <= 1'b0; rmop_q <= RMOP_XOR; rm_dir_reg_is_dst_q <= 1'b0; state_after_get_q <= ST_MODRM; state_q <= ST_GET_BYTE; end
              8'h33: begin rep_prefix_q <= 1'b0; rmop_q <= RMOP_XOR; rm_dir_reg_is_dst_q <= 1'b1; state_after_get_q <= ST_MODRM; state_q <= ST_GET_BYTE; end
              8'h85: begin rep_prefix_q <= 1'b0; rmop_q <= RMOP_TEST; rm_dir_reg_is_dst_q <= 1'b0; state_after_get_q <= ST_MODRM; state_q <= ST_GET_BYTE; end
              8'h8C: begin rep_prefix_q <= 1'b0; rmop_q <= RMOP_MOV_SREG_TO_RM; rm_dir_reg_is_dst_q <= 1'b0; state_after_get_q <= ST_MODRM; state_q <= ST_GET_BYTE; end
              8'h8E: begin rep_prefix_q <= 1'b0; rmop_q <= RMOP_MOV_RM_TO_SREG; rm_dir_reg_is_dst_q <= 1'b0; state_after_get_q <= ST_MODRM; state_q <= ST_GET_BYTE; end

              default: begin
                halt_trap_q <= 1'b1;
                csr_cause_q <= X96_CAUSE_ILLEGAL_INSN;
                csr_epc_q <= {cs_q, ip_q};
                state_q <= ST_TRAP;
              end
            endcase
          end

          ST_MOV_IMM_LO: begin
            imm16_q[7:0] <= fetch_byte_q;
            state_after_get_q <= ST_MOV_IMM_HI;
            state_q <= ST_GET_BYTE;
          end
          ST_MOV_IMM_HI: begin
            imm16_q[15:8] <= fetch_byte_q;
            state_q <= ST_MOV_IMM_EXEC;
          end
          ST_MOV_IMM_EXEC: begin
            gpr_q[reg_sel_q[2:0]] <= imm16_q;
            state_q <= ST_BOUNDARY;
          end

          // ----------------------------------------------------------------
          // Carbon system prefix (0x62): MODEUP/RETMD
          // ----------------------------------------------------------------
          ST_SYS_GET_SUB: begin
            sys_subop_q <= fetch_byte_q;
            if (fetch_byte_q == 8'h00) begin
              state_after_get_q <= ST_SYS_MODEUP_TIER;
              state_q <= ST_GET_BYTE;
            end else if (fetch_byte_q == 8'h01) begin
              state_q <= ST_SYS_RETMD_EXEC;
            end else begin
              halt_trap_q <= 1'b1;
              csr_cause_q <= X96_CAUSE_ILLEGAL_INSN;
              csr_epc_q <= {cs_q, ip_q};
              state_q <= ST_TRAP;
            end
          end

          ST_SYS_MODEUP_TIER: begin
            // target tier in imm16_q[7:0]
            imm16_q[7:0] <= fetch_byte_q;
            state_after_get_q <= ST_SYS_MODEUP_IP_LO;
            state_q <= ST_GET_BYTE;
          end

          ST_SYS_MODEUP_IP_LO: begin
            // stash entry_ip[7:0] in imm16_q[15:8] temporarily
            imm16_q[15:8] <= fetch_byte_q;
            state_after_get_q <= ST_SYS_MODEUP_IP_HI;
            state_q <= ST_GET_BYTE;
          end

          ST_SYS_MODEUP_IP_HI: begin
            disp16_q <= {fetch_byte_q, imm16_q[15:8]};
            state_q <= ST_SYS_MODEUP_EXEC;
          end

          ST_SYS_MODEUP_EXEC: begin
            logic [7:0] target;
            logic [15:0] entry;
            target = imm16_q[7:0];
            entry  = disp16_q;

            if (target <= tier_q) begin
              halt_trap_q <= 1'b1;
              csr_cause_q <= X96_CAUSE_MODEUP_INVALID;
              csr_epc_q <= {cs_q, ip_q};
              state_q <= ST_TRAP;
            end else if (target != 8'(CARBON_X86_DERIVED_TIER_P7_X86_64)) begin
              // P1-P6 trap in v1.
              halt_trap_q <= 1'b1;
              csr_cause_q <= X96_CAUSE_UNIMPL_TIER;
              csr_epc_q <= {cs_q, ip_q};
              state_q <= ST_TRAP;
            end else if (md_sp_q == MD_SP_W'(MODESTACK_DEPTH)) begin
              halt_trap_q <= 1'b1;
              csr_cause_q <= X96_CAUSE_MODESTACK_OVERFLOW;
              csr_epc_q <= {cs_q, ip_q};
              state_q <= ST_TRAP;
            end else begin
              md_tier_q[md_sp_q]  <= tier_q;
              md_flags_q[md_sp_q] <= modeflags_q;
              md_ip_q[md_sp_q]    <= ip_q;  // return IP after MODEUP immediates
              md_sp_q <= md_sp_q + MD_SP_W'(1);

              tier_q <= target;
              ip_q <= entry;
              pf_count_q <= '0;
              pf_phys_base_q <= phys_addr(cs_q, entry);
              state_q <= ST_BOUNDARY;
            end
          end

          ST_SYS_RETMD_EXEC: begin
            if (md_sp_q == 0) begin
              halt_trap_q <= 1'b1;
              csr_cause_q <= X96_CAUSE_MODESTACK_UNDERFLOW;
              csr_epc_q <= {cs_q, ip_q};
              state_q <= ST_TRAP;
            end else begin
              md_sp_q <= md_sp_q - MD_SP_W'(1);
              tier_q <= md_tier_q[md_sp_q - MD_SP_W'(1)];
              modeflags_q <= md_flags_q[md_sp_q - MD_SP_W'(1)];
              ip_q <= md_ip_q[md_sp_q - MD_SP_W'(1)];
              pf_count_q <= '0;
              pf_phys_base_q <= phys_addr(cs_q, md_ip_q[md_sp_q - MD_SP_W'(1)]);
              state_q <= ST_BOUNDARY;
            end
          end

          // ----------------------------------------------------------------
          // Carbon turbo prefix (0x63): minimal P7-only ops
          // ----------------------------------------------------------------
          ST_TURBO_GET_SUB: begin
            turbo_subop_q <= fetch_byte_q;
            state_after_get_q <= ST_TURBO_B0;
            state_q <= ST_GET_BYTE;
          end

          ST_TURBO_B0: begin
            tmp_lo8_q <= fetch_byte_q;
            if (turbo_subop_q == 8'h00) begin
              state_after_get_q <= ST_TURBO_IMM_LO;
              state_q <= ST_GET_BYTE;
            end else begin
              state_after_get_q <= ST_TURBO_B1;
              state_q <= ST_GET_BYTE;
            end
          end

          ST_TURBO_B1: begin
            tmp_hi8_q <= fetch_byte_q;
            state_q <= ST_TURBO_EXEC;
          end

          ST_TURBO_IMM_LO: begin
            imm16_q[7:0] <= fetch_byte_q;
            state_after_get_q <= ST_TURBO_IMM_HI;
            state_q <= ST_GET_BYTE;
          end

          ST_TURBO_IMM_HI: begin
            imm16_q[15:8] <= fetch_byte_q;
            state_q <= ST_TURBO_EXEC;
          end

          ST_TURBO_EXEC: begin
            if (!turbo_allowed) begin
              halt_trap_q <= 1'b1;
              csr_cause_q <= X96_CAUSE_TURBO_DENIED;
              csr_epc_q <= {cs_q, ip_q};
              state_q <= ST_TRAP;
            end else begin
              unique case (turbo_subop_q)
                // 0x00: MOVX treg, imm16  (b0=treg)
                8'h00: tr_q[tmp_lo8_q[3:0]] <= imm16_q;

                // 0x01: MOVX treg, reg16  (b0=treg, b1=reg)
                8'h01: tr_q[tmp_lo8_q[3:0]] <= gpr_q[tmp_hi8_q[2:0]];

                // 0x02: MOVX reg16, treg  (b0=treg, b1=reg)
                8'h02: gpr_q[tmp_hi8_q[2:0]] <= tr_q[tmp_lo8_q[3:0]];

                // 0x10: ALUX_ADD dst,src  (b0=dst, b1=src)
                8'h10: begin
                  x96_alu16_t o;
                  o = alu_add16(tr_q[tmp_lo8_q[3:0]], tr_q[tmp_hi8_q[3:0]]);
                  tr_q[tmp_lo8_q[3:0]] <= o.res;
                  flags_q <= flags_apply(flags_q, o, 1'b1);
                end

                default: begin
                  halt_trap_q <= 1'b1;
                  csr_cause_q <= X96_CAUSE_ILLEGAL_INSN;
                  csr_epc_q <= {cs_q, ip_q};
                  state_q <= ST_TRAP;
                end
              endcase
              state_q <= ST_BOUNDARY;
            end
          end

          ST_REL8: begin
            if (op_q == 8'hCD) begin
              halt_trap_q <= 1'b1;
              csr_cause_q <= X96_CAUSE_INTN | 32'(fetch_byte_q);
              csr_epc_q <= {cs_q, ip_q};
              state_q <= ST_TRAP;
            end else if (op_q == 8'hEB) begin
              logic [15:0] ip_new;
              ip_new = ip_q + sext8to16(fetch_byte_q);
              ip_q <= ip_new;
              pf_count_q <= '0;
              pf_phys_base_q <= phys_addr(cs_q, ip_new);
              state_q <= ST_BOUNDARY;
            end else begin
              if (jcc_take(op_q[3:0])) begin
                logic [15:0] ip_new;
                ip_new = ip_q + sext8to16(fetch_byte_q);
                ip_q <= ip_new;
                pf_count_q <= '0;
                pf_phys_base_q <= phys_addr(cs_q, ip_new);
              end
              state_q <= ST_BOUNDARY;
            end
          end

          ST_REL16_LO: begin
            disp16_q[7:0] <= fetch_byte_q;
            state_after_get_q <= ST_REL16_HI;
            state_q <= ST_GET_BYTE;
          end
          ST_REL16_HI: begin
            disp16_q[15:8] <= fetch_byte_q;
            if (op_q == 8'hE9) begin
              state_q <= ST_JMP_REL16_EXEC;
            end else begin
              stack_val_q <= ip_q;
              stack_sp_tmp_q <= gpr_q[4] - 16'd2;
              state_q <= ST_CALL_PUSH_LO;
            end
          end
          ST_JMP_REL16_EXEC: begin
            logic [15:0] ip_new;
            ip_new = ip_q + disp16_q;
            ip_q <= ip_new;
            pf_count_q <= '0;
            pf_phys_base_q <= phys_addr(cs_q, ip_new);
            state_q <= ST_BOUNDARY;
          end

          ST_CALL_PUSH_LO: begin
            bus_op_q <= FAB_OP_W'(CARBON_FABRIC_XACT_WRITE);
            bus_addr_q <= FAB_ADDR_W'({{(FAB_ADDR_W-20){1'b0}}, phys_addr(ss_q, stack_sp_tmp_q)});
            bus_wdata_q <= FAB_DATA_W'({{(FAB_DATA_W-8){1'b0}}, stack_val_q[7:0]});
            bus_wstrb_q <= FAB_STRB_W'({{(FAB_STRB_W-1){1'b0}}, 1'b1});
            bus_size_q <= '0;
            bus_attr_q <= MEM_ATTR;
            bus_id_q <= '0;
            bus_dest_q <= DEST_NONE;
            state_after_bus_q <= ST_CALL_PUSH_HI;
            state_q <= ST_BUS_REQ;
          end
          ST_CALL_PUSH_HI: begin
            bus_op_q <= FAB_OP_W'(CARBON_FABRIC_XACT_WRITE);
            bus_addr_q <= FAB_ADDR_W'({{(FAB_ADDR_W-20){1'b0}}, phys_addr(ss_q, stack_sp_tmp_q) + 20'd1});
            bus_wdata_q <= FAB_DATA_W'({{(FAB_DATA_W-8){1'b0}}, stack_val_q[15:8]});
            bus_wstrb_q <= FAB_STRB_W'({{(FAB_STRB_W-1){1'b0}}, 1'b1});
            bus_size_q <= '0;
            bus_attr_q <= MEM_ATTR;
            bus_id_q <= '0;
            bus_dest_q <= DEST_NONE;
            state_after_bus_q <= ST_CALL_SETIP;
            state_q <= ST_BUS_REQ;
          end
          ST_CALL_SETIP: begin
            logic [15:0] ip_new;
            gpr_q[4] <= stack_sp_tmp_q;
            ip_new = ip_q + disp16_q;
            ip_q <= ip_new;
            pf_count_q <= '0;
            pf_phys_base_q <= phys_addr(cs_q, ip_new);
            state_q <= ST_BOUNDARY;
          end

          ST_PUSH_LO: begin
            bus_op_q <= FAB_OP_W'(CARBON_FABRIC_XACT_WRITE);
            bus_addr_q <= FAB_ADDR_W'({{(FAB_ADDR_W-20){1'b0}}, phys_addr(ss_q, stack_sp_tmp_q)});
            bus_wdata_q <= FAB_DATA_W'({{(FAB_DATA_W-8){1'b0}}, stack_val_q[7:0]});
            bus_wstrb_q <= FAB_STRB_W'({{(FAB_STRB_W-1){1'b0}}, 1'b1});
            bus_size_q <= '0;
            bus_attr_q <= MEM_ATTR;
            bus_id_q <= '0;
            bus_dest_q <= DEST_NONE;
            state_after_bus_q <= ST_PUSH_HI;
            state_q <= ST_BUS_REQ;
          end
          ST_PUSH_HI: begin
            bus_op_q <= FAB_OP_W'(CARBON_FABRIC_XACT_WRITE);
            bus_addr_q <= FAB_ADDR_W'({{(FAB_ADDR_W-20){1'b0}}, phys_addr(ss_q, stack_sp_tmp_q) + 20'd1});
            bus_wdata_q <= FAB_DATA_W'({{(FAB_DATA_W-8){1'b0}}, stack_val_q[15:8]});
            bus_wstrb_q <= FAB_STRB_W'({{(FAB_STRB_W-1){1'b0}}, 1'b1});
            bus_size_q <= '0;
            bus_attr_q <= MEM_ATTR;
            bus_id_q <= '0;
            bus_dest_q <= DEST_NONE;
            gpr_q[4] <= stack_sp_tmp_q;
            state_after_bus_q <= ST_BOUNDARY;
            state_q <= ST_BUS_REQ;
          end

          ST_POP_LO: begin
            bus_op_q <= FAB_OP_W'(CARBON_FABRIC_XACT_READ);
            bus_addr_q <= FAB_ADDR_W'({{(FAB_ADDR_W-20){1'b0}}, phys_addr(ss_q, gpr_q[4])});
            bus_wdata_q <= '0;
            bus_wstrb_q <= '0;
            bus_size_q <= '0;
            bus_attr_q <= MEM_ATTR;
            bus_id_q <= '0;
            bus_dest_q <= DEST_TMP_LO;
            state_after_bus_q <= ST_POP_HI;
            state_q <= ST_BUS_REQ;
          end
          ST_POP_HI: begin
            bus_op_q <= FAB_OP_W'(CARBON_FABRIC_XACT_READ);
            bus_addr_q <= FAB_ADDR_W'({{(FAB_ADDR_W-20){1'b0}}, phys_addr(ss_q, gpr_q[4]) + 20'd1});
            bus_wdata_q <= '0;
            bus_wstrb_q <= '0;
            bus_size_q <= '0;
            bus_attr_q <= MEM_ATTR;
            bus_id_q <= '0;
            bus_dest_q <= DEST_TMP_HI;
            state_after_bus_q <= ST_POP_COMMIT;
            state_q <= ST_BUS_REQ;
          end
          ST_POP_COMMIT: begin
            logic [15:0] v;
            v = {tmp_hi8_q, tmp_lo8_q};
            gpr_q[4] <= gpr_q[4] + 16'd2;
            unique case (pop_dest_q)
              4'h8: es_q <= v;
              4'hA: ss_q <= v;
              4'hB: ds_q <= v;
              4'hF: begin
                ip_q <= v;
                pf_count_q <= '0;
                pf_phys_base_q <= phys_addr(cs_q, v);
              end
              default: gpr_q[pop_dest_q[2:0]] <= v;
            endcase
            state_q <= ST_BOUNDARY;
          end

          // ----------------------------------------------------------------
          // ModRM decode + memory operand helpers (16-bit addressing)
          // ----------------------------------------------------------------
          ST_MODRM: begin
            modrm_q <= fetch_byte_q;
            mod_q <= fetch_byte_q[7:6];
            reg_q <= fetch_byte_q[5:3];
            rm_q <= fetch_byte_q[2:0];

            if (fetch_byte_q[7:6] == 2'b01) begin
              state_after_get_q <= ST_DISP8;
              state_q <= ST_GET_BYTE;
            end else if ((fetch_byte_q[7:6] == 2'b10) || ((fetch_byte_q[7:6] == 2'b00) && (fetch_byte_q[2:0] == 3'b110))) begin
              state_after_get_q <= ST_DISP16_LO;
              state_q <= ST_GET_BYTE;
            end else begin
              disp16_q <= 16'h0000;
              state_q <= ST_EA_READY;
            end
          end

          ST_DISP8: begin
            disp16_q <= sext8to16(fetch_byte_q);
            state_q <= ST_EA_READY;
          end

          ST_DISP16_LO: begin
            disp16_q[7:0] <= fetch_byte_q;
            state_after_get_q <= ST_DISP16_HI;
            state_q <= ST_GET_BYTE;
          end

          ST_DISP16_HI: begin
            disp16_q[15:8] <= fetch_byte_q;
            state_q <= ST_EA_READY;
          end

          ST_EA_READY: begin
            logic [15:0] base;
            logic use_ss;

            rm_is_reg_q <= (mod_q == 2'b11);
            use_ss = ((rm_q == 3'd2) || (rm_q == 3'd3) || ((rm_q == 3'd6) && (mod_q != 2'b00)));

            unique case (rm_q)
              3'd0: base = gpr_q[3] + gpr_q[6]; // BX+SI
              3'd1: base = gpr_q[3] + gpr_q[7]; // BX+DI
              3'd2: base = gpr_q[5] + gpr_q[6]; // BP+SI
              3'd3: base = gpr_q[5] + gpr_q[7]; // BP+DI
              3'd4: base = gpr_q[6];            // SI
              3'd5: base = gpr_q[7];            // DI
              3'd6: base = (mod_q == 2'b00) ? 16'h0000 : gpr_q[5]; // disp16 or BP
              default: base = gpr_q[3];          // BX
            endcase

            ea_off_q <= base + disp16_q;
            ea_phys_q <= phys_addr(use_ss ? ss_q : ds_q, base + disp16_q);

            if (mod_q == 2'b11) begin
              state_q <= ST_RM_EXEC;
            end else begin
              // Direct stores can skip memory read.
              if ((rmop_q == RMOP_MOV && !rm_dir_reg_is_dst_q) || (rmop_q == RMOP_MOV_SREG_TO_RM)) begin
                store_phys_q <= ea_phys_q;
                if (rmop_q == RMOP_MOV_SREG_TO_RM) begin
                  unique case (reg_q)
                    3'd0: store_word_q <= es_q;
                    3'd1: store_word_q <= cs_q;
                    3'd2: store_word_q <= ss_q;
                    default: store_word_q <= ds_q;
                  endcase
                end else begin
                  store_word_q <= gpr_q[reg_q];
                end
                state_q <= ST_MEM_WR_LO;
              end else begin
                state_q <= ST_MEM_RD_LO;
              end
            end
          end

          ST_MEM_RD_LO: begin
            bus_op_q <= FAB_OP_W'(CARBON_FABRIC_XACT_READ);
            bus_addr_q <= FAB_ADDR_W'({{(FAB_ADDR_W-20){1'b0}}, ea_phys_q});
            bus_wdata_q <= '0;
            bus_wstrb_q <= '0;
            bus_size_q <= '0;
            bus_attr_q <= MEM_ATTR;
            bus_id_q <= '0;
            bus_dest_q <= DEST_TMP_LO;
            state_after_bus_q <= ST_MEM_RD_HI;
            state_q <= ST_BUS_REQ;
          end

          ST_MEM_RD_HI: begin
            bus_op_q <= FAB_OP_W'(CARBON_FABRIC_XACT_READ);
            bus_addr_q <= FAB_ADDR_W'({{(FAB_ADDR_W-20){1'b0}}, ea_phys_q + 20'd1});
            bus_wdata_q <= '0;
            bus_wstrb_q <= '0;
            bus_size_q <= '0;
            bus_attr_q <= MEM_ATTR;
            bus_id_q <= '0;
            bus_dest_q <= DEST_TMP_HI;
            state_after_bus_q <= ST_MEM_RD_DONE;
            state_q <= ST_BUS_REQ;
          end

          ST_MEM_RD_DONE: begin
            mem_word_q <= {tmp_hi8_q, tmp_lo8_q};
            state_q <= ST_RM_EXEC;
          end

          ST_MEM_WR_LO: begin
            bus_op_q <= FAB_OP_W'(CARBON_FABRIC_XACT_WRITE);
            bus_addr_q <= FAB_ADDR_W'({{(FAB_ADDR_W-20){1'b0}}, store_phys_q});
            bus_wdata_q <= FAB_DATA_W'({{(FAB_DATA_W-8){1'b0}}, store_word_q[7:0]});
            bus_wstrb_q <= FAB_STRB_W'({{(FAB_STRB_W-1){1'b0}}, 1'b1});
            bus_size_q <= '0;
            bus_attr_q <= MEM_ATTR;
            bus_id_q <= '0;
            bus_dest_q <= DEST_NONE;
            state_after_bus_q <= ST_MEM_WR_HI;
            state_q <= ST_BUS_REQ;
          end

          ST_MEM_WR_HI: begin
            bus_op_q <= FAB_OP_W'(CARBON_FABRIC_XACT_WRITE);
            bus_addr_q <= FAB_ADDR_W'({{(FAB_ADDR_W-20){1'b0}}, store_phys_q + 20'd1});
            bus_wdata_q <= FAB_DATA_W'({{(FAB_DATA_W-8){1'b0}}, store_word_q[15:8]});
            bus_wstrb_q <= FAB_STRB_W'({{(FAB_STRB_W-1){1'b0}}, 1'b1});
            bus_size_q <= '0;
            bus_attr_q <= MEM_ATTR;
            bus_id_q <= '0;
            bus_dest_q <= DEST_NONE;
            state_after_bus_q <= ST_MEM_WR_DONE;
            state_q <= ST_BUS_REQ;
          end

          ST_MEM_WR_DONE: begin
            state_q <= ST_BOUNDARY;
          end

          ST_RM_EXEC: begin
            logic [15:0] src;
            logic [15:0] dst;
            x96_alu16_t o;
            logic wb;
            wb = 1'b0;

            if (mod_q == 2'b11) begin
              dst = rm_dir_reg_is_dst_q ? gpr_q[reg_q] : gpr_q[rm_q];
              src = rm_dir_reg_is_dst_q ? gpr_q[rm_q] : gpr_q[reg_q];
            end else begin
              dst = rm_dir_reg_is_dst_q ? gpr_q[reg_q] : mem_word_q;
              src = rm_dir_reg_is_dst_q ? mem_word_q : gpr_q[reg_q];
            end

            unique case (rmop_q)
              RMOP_MOV: begin o.res = src; wb = 1'b1; end
              RMOP_ADD: begin o = alu_add16(dst, src); flags_q <= flags_apply(flags_q, o, 1'b1); wb = 1'b1; end
              RMOP_SUB: begin o = alu_sub16(dst, src); flags_q <= flags_apply(flags_q, o, 1'b1); wb = 1'b1; end
              RMOP_CMP: begin o = alu_sub16(dst, src); flags_q <= flags_apply(flags_q, o, 1'b1); wb = 1'b0; end
              RMOP_AND: begin o = alu_and16(dst, src); flags_q <= flags_apply(flags_q, o, 1'b1); wb = 1'b1; end
              RMOP_OR:  begin o = alu_or16(dst, src);  flags_q <= flags_apply(flags_q, o, 1'b1); wb = 1'b1; end
              RMOP_XOR: begin o = alu_xor16(dst, src); flags_q <= flags_apply(flags_q, o, 1'b1); wb = 1'b1; end
              RMOP_TEST: begin o = alu_and16(dst, src); flags_q <= flags_apply(flags_q, o, 1'b1); wb = 1'b0; end
              RMOP_MOV_SREG_TO_RM: begin
                unique case (reg_q)
                  3'd0: o.res = es_q;
                  3'd1: o.res = cs_q;
                  3'd2: o.res = ss_q;
                  default: o.res = ds_q;
                endcase
                wb = 1'b1;
              end
              RMOP_MOV_RM_TO_SREG: begin
                // reg_q encodes segment: 0=ES,1=CS,2=SS,3=DS
                logic [15:0] rm_val;
                rm_val = (mod_q == 2'b11) ? gpr_q[rm_q] : mem_word_q;

                if (reg_q == 3'd0) es_q <= rm_val;
                else if (reg_q == 3'd1) cs_q <= rm_val;
                else if (reg_q == 3'd2) ss_q <= rm_val;
                else ds_q <= rm_val;

                pf_count_q <= '0;
                pf_phys_base_q <= (reg_q == 3'd1) ? phys_addr(rm_val, ip_q) : phys_addr(cs_q, ip_q);
                wb = 1'b0;
              end
              default: begin
                halt_trap_q <= 1'b1;
                csr_cause_q <= X96_CAUSE_ILLEGAL_INSN;
                csr_epc_q <= {cs_q, ip_q};
                state_q <= ST_TRAP;
              end
            endcase

            if (rmop_q == RMOP_MOV_RM_TO_SREG) begin
              state_q <= ST_BOUNDARY;
            end else if (wb) begin
              if (mod_q == 2'b11) begin
                if (rm_dir_reg_is_dst_q) gpr_q[reg_q] <= o.res;
                else gpr_q[rm_q] <= o.res;
                state_q <= ST_BOUNDARY;
              end else if (rm_dir_reg_is_dst_q) begin
                gpr_q[reg_q] <= o.res;
                state_q <= ST_BOUNDARY;
              end else begin
                store_phys_q <= ea_phys_q;
                store_word_q <= o.res;
                state_q <= ST_MEM_WR_LO;
              end
            end else begin
              state_q <= ST_BOUNDARY;
            end
          end

          // ----------------------------------------------------------------
          // String ops (MOVS/STOS), DF=0 assumed in v1
          // ----------------------------------------------------------------
          ST_STR_START: begin
            if (str_count_q == 0) begin
              state_q <= ST_BOUNDARY;
            end else begin
              store_phys_q <= phys_addr(es_q, str_dst_off_q);
              if (str_kind_q == 2'd0) begin
                ea_phys_q <= phys_addr(ds_q, str_src_off_q);
                state_q <= ST_STR_RD_LO;
              end else begin
                store_word_q <= gpr_q[0]; // AX
                state_q <= ST_STR_WR_LO;
              end
            end
          end

          ST_STR_RD_LO: begin
            bus_op_q <= FAB_OP_W'(CARBON_FABRIC_XACT_READ);
            bus_addr_q <= FAB_ADDR_W'({{(FAB_ADDR_W-20){1'b0}}, ea_phys_q});
            bus_wdata_q <= '0;
            bus_wstrb_q <= '0;
            bus_size_q <= '0;
            bus_attr_q <= MEM_ATTR;
            bus_id_q <= '0;
            bus_dest_q <= DEST_TMP_LO;
            state_after_bus_q <= (str_size_q == 2'd2) ? ST_STR_RD_HI : ST_STR_WR_LO;
            state_q <= ST_BUS_REQ;
          end

          ST_STR_RD_HI: begin
            bus_op_q <= FAB_OP_W'(CARBON_FABRIC_XACT_READ);
            bus_addr_q <= FAB_ADDR_W'({{(FAB_ADDR_W-20){1'b0}}, ea_phys_q + 20'd1});
            bus_wdata_q <= '0;
            bus_wstrb_q <= '0;
            bus_size_q <= '0;
            bus_attr_q <= MEM_ATTR;
            bus_id_q <= '0;
            bus_dest_q <= DEST_TMP_HI;
            state_after_bus_q <= ST_STR_WR_LO;
            state_q <= ST_BUS_REQ;
          end

          ST_STR_WR_LO: begin
            bus_op_q <= FAB_OP_W'(CARBON_FABRIC_XACT_WRITE);
            bus_addr_q <= FAB_ADDR_W'({{(FAB_ADDR_W-20){1'b0}}, store_phys_q});
            bus_wdata_q <= FAB_DATA_W'({{(FAB_DATA_W-8){1'b0}}, (str_kind_q == 2'd0) ? tmp_lo8_q : store_word_q[7:0]});
            bus_wstrb_q <= FAB_STRB_W'({{(FAB_STRB_W-1){1'b0}}, 1'b1});
            bus_size_q <= '0;
            bus_attr_q <= MEM_ATTR;
            bus_id_q <= '0;
            bus_dest_q <= DEST_NONE;
            state_after_bus_q <= (str_size_q == 2'd2) ? ST_STR_WR_HI : ST_STR_UPDATE;
            state_q <= ST_BUS_REQ;
          end

          ST_STR_WR_HI: begin
            bus_op_q <= FAB_OP_W'(CARBON_FABRIC_XACT_WRITE);
            bus_addr_q <= FAB_ADDR_W'({{(FAB_ADDR_W-20){1'b0}}, store_phys_q + 20'd1});
            bus_wdata_q <= FAB_DATA_W'({{(FAB_DATA_W-8){1'b0}}, (str_kind_q == 2'd0) ? tmp_hi8_q : store_word_q[15:8]});
            bus_wstrb_q <= FAB_STRB_W'({{(FAB_STRB_W-1){1'b0}}, 1'b1});
            bus_size_q <= '0;
            bus_attr_q <= MEM_ATTR;
            bus_id_q <= '0;
            bus_dest_q <= DEST_NONE;
            state_after_bus_q <= ST_STR_UPDATE;
            state_q <= ST_BUS_REQ;
          end

          ST_STR_UPDATE: begin
            logic [15:0] step;
            step = (str_size_q == 2'd2) ? 16'd2 : 16'd1;
            str_src_off_q <= str_src_off_q + step;
            str_dst_off_q <= str_dst_off_q + step;
            gpr_q[6] <= str_src_off_q + step; // SI
            gpr_q[7] <= str_dst_off_q + step; // DI

            if (str_rep_q) begin
              gpr_q[1] <= gpr_q[1] - 16'd1; // CX
              str_count_q <= str_count_q - 16'd1;
              if (str_count_q == 16'd1) state_q <= ST_BOUNDARY;
              else state_q <= ST_STR_START;
            end else begin
              state_q <= ST_BOUNDARY;
            end
          end

          ST_BUS_REQ: begin
            if (mem_if.req_ready) state_q <= ST_BUS_RSP;
          end
          ST_BUS_RSP: begin
            if (mem_if.rsp_valid) begin
              if (mem_if.rsp_code != FAB_CODE_W'(CARBON_FABRIC_RESP_OK)) begin
                halt_trap_q <= 1'b1;
                csr_cause_q <= X96_CAUSE_BUS_FAULT;
                csr_epc_q <= {cs_q, ip_q};
                state_q <= ST_TRAP;
              end else begin
                unique case (bus_dest_q)
                  DEST_PF: begin
                    if (pf_count_q != PF_COUNT_W'(PREFETCH_DEPTH)) begin
                      pf_q[pf_count_q] <= mem_if.rsp_rdata[7:0];
                      pf_count_q <= pf_count_q + PF_COUNT_W'(1);
                    end
                  end
                  DEST_TMP_LO: tmp_lo8_q <= mem_if.rsp_rdata[7:0];
                  DEST_TMP_HI: tmp_hi8_q <= mem_if.rsp_rdata[7:0];
                  default: begin end
                endcase
                state_q <= state_after_bus_q;
              end
            end
          end

          ST_TRAP: state_q <= ST_TRAP;

          default: begin
            halt_trap_q <= 1'b1;
            csr_cause_q <= X96_CAUSE_ILLEGAL_INSN;
            csr_epc_q <= {cs_q, ip_q};
            state_q <= ST_TRAP;
          end
        endcase
      end
    end
  end

endmodule : cpu_8096_core
