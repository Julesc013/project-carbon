// Project Carbon - Z90 core (turbo Z80 successor)
// z90_core: Minimal in-order core scaffolding with Z90 opcode pages and MODEUP/RETMD.
//
// NOTE: This is scaffolding: legacy execution is currently limited to a small
// 8080-compatible subset. See `hdl/cores/Z90/docs/Z90_v1.md` for explicit gaps.

module z90_core #(
    parameter int unsigned MODESTACK_DEPTH = carbon_arch_pkg::CARBON_MODESTACK_RECOMMENDED_DEPTH
) (
    input logic clk,
    input logic rst_n,

    fabric_if.master mem_if,
    fabric_if.master io_if,

    irq_if.sink irq,
    csr_if.slave csr,
    dbg_if.core dbg,
    cai_if.host cai
);
  import carbon_arch_pkg::*;
  import z85_regfile_pkg::*;
  import z85_flags_pkg::*;
  import z90_decode_pkg::*;
  import z90_alu_pkg::*;

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

  localparam int unsigned MD_SP_W =
      (MODESTACK_DEPTH < 2) ? 1 : $clog2(MODESTACK_DEPTH + 1);

`ifndef SYNTHESIS
  initial begin
    if (MODESTACK_DEPTH < CARBON_MODESTACK_MIN_DEPTH) begin
      $fatal(1, "z90_core: MODESTACK_DEPTH must be >= CARBON_MODESTACK_MIN_DEPTH");
    end
  end
`endif

  localparam logic [FAB_ATTR_W-1:0] MEM_ATTR =
      FAB_ATTR_W'(CARBON_FABRIC_ATTR_CACHEABLE_MASK);
  localparam logic [FAB_ATTR_W-1:0] IO_ATTR =
      FAB_ATTR_W'(CARBON_FABRIC_ATTR_ORDERED_MASK | CARBON_FABRIC_ATTR_IO_SPACE_MASK);
  localparam logic [FAB_ATTR_W-1:0] ATOMIC_ATTR =
      FAB_ATTR_W'(
          CARBON_FABRIC_ATTR_CACHEABLE_MASK |
          CARBON_FABRIC_ATTR_ACQUIRE_MASK |
          CARBON_FABRIC_ATTR_RELEASE_MASK
      );

  // Implementation-defined trap causes (scaffolding)
  localparam logic [31:0] Z90_CAUSE_ILLEGAL_INSN        = 32'h0000_0001;
  localparam logic [31:0] Z90_CAUSE_BUS_FAULT           = 32'h0000_0002;
  localparam logic [31:0] Z90_CAUSE_MODESTACK_OVERFLOW  = 32'h0000_0010;
  localparam logic [31:0] Z90_CAUSE_MODESTACK_UNDERFLOW = 32'h0000_0011;
  localparam logic [31:0] Z90_CAUSE_MODEUP_INVALID      = 32'h0000_0012;

  // --------------------------------------------------------------------------
  // Core architectural state (legacy + Z90)
  // --------------------------------------------------------------------------
  z85_state_t z80_q;

  logic [15:0] x_q [16];
  logic [7:0]  z90_flags_q;

  logic [7:0] tier_q;
  logic [7:0] modeflags_q;

  logic [MD_SP_W-1:0] md_sp_q;
  logic [7:0]  md_tier_q  [MODESTACK_DEPTH];
  logic [7:0]  md_flags_q [MODESTACK_DEPTH];
  logic [15:0] md_pc_q    [MODESTACK_DEPTH];

  // CSR-backed registers (placeholders)
  logic [31:0] csr_cause_q;
  logic [31:0] csr_epc_q;
  logic [31:0] csr_trace_ctl_q;

  logic [31:0] csr_z90_mmu_win0_base_q;
  logic [31:0] csr_z90_mmu_win0_mask_q;
  logic [31:0] csr_z90_mmu_win1_base_q;
  logic [31:0] csr_z90_mmu_win1_mask_q;
  logic [31:0] csr_z90_cache_ctl_q;
  logic [31:0] csr_z90_atomic_ctl_q;
  logic [31:0] csr_z90_atomic_status_q;

  logic [63:0] cycle_q;

  // Debug/stop control
  logic halt_debug_q;
  logic halt_instr_q;
  logic halt_trap_q;
  logic step_token_q;
  logic step_ack_pulse_q;

  wire core_halted = halt_debug_q || halt_instr_q || halt_trap_q;

  // CAI host registers (wired to cai_if)
  logic [63:0] cai_submit_desc_base_q;
  logic [31:0] cai_submit_ring_mask_q;
  logic [63:0] cai_comp_base_q;
  logic [15:0] cai_context_sel_q;
  logic cai_submit_pulse_q;

  assign cai.submit_desc_base  = cai_submit_desc_base_q;
  assign cai.submit_ring_mask  = cai_submit_ring_mask_q;
  assign cai.submit_doorbell   = cai_submit_pulse_q;
  assign cai.context_sel       = cai_context_sel_q;

  // External IRQ interface (not yet implemented)
  assign irq.irq_ack = 1'b0;
  assign irq.irq_ack_vector = '0;

  // Debug interface placeholders
  assign dbg.halt_ack    = core_halted;
  assign dbg.step_ack    = step_ack_pulse_q;
  assign dbg.bp_ready    = 1'b1;
  assign dbg.trace_valid = 1'b0;
  assign dbg.trace_data  = '0;
  assign dbg.trace_ready = 1'b1;

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
  // Fabric bus microsequencer
  // --------------------------------------------------------------------------
  typedef enum logic [5:0] {
    ST_RESET               = 6'd0,
    ST_BOUNDARY            = 6'd1,
    ST_BUS_REQ             = 6'd2,
    ST_BUS_RSP             = 6'd3,
    ST_DECODE0             = 6'd4,
    ST_FETCH_ED1           = 6'd5,
    ST_DECODE_ED           = 6'd6,
    ST_Z90_P0_FETCH_OP1    = 6'd7,
    ST_Z90_P0_DISPATCH     = 6'd8,
    ST_Z90_MODEUP_FETCH_LO = 6'd9,
    ST_Z90_MODEUP_FETCH_HI = 6'd10,
    ST_Z90_MODEUP_EXEC     = 6'd11,
    ST_Z90_P1_FETCH_OP1    = 6'd12,
    ST_Z90_P1_FETCH_DISP   = 6'd13,
    ST_Z90_P1_DISPATCH     = 6'd14,
    ST_Z90_LD16_FETCH_HI   = 6'd15,
    ST_Z90_LD16_DONE       = 6'd16,
    ST_Z90_ST16_WRITE_HI   = 6'd17,
    ST_Z90_ST16_DONE       = 6'd18,
    ST_Z90_CAS16_DONE      = 6'd19
  } core_state_e;

  typedef enum logic [3:0] {
    DEST_NONE   = 4'd0,
    DEST_B0     = 4'd1,
    DEST_B1     = 4'd2,
    DEST_B2     = 4'd3,
    DEST_B3     = 4'd4,
    DEST_B4     = 4'd5,
    DEST_B5     = 4'd6,
    DEST_B6     = 4'd7,
    DEST_MEM_LO = 4'd8,
    DEST_MEM_HI = 4'd9,
    DEST_ATOMIC = 4'd10
  } bus_dest_e;

  core_state_e state_q;
  core_state_e state_after_bus_q;
  bus_dest_e   bus_dest_q;

  logic bus_is_io_q;
  logic [FAB_OP_W-1:0]    bus_op_q;
  logic [FAB_ADDR_W-1:0]  bus_addr_q;
  logic [FAB_DATA_W-1:0]  bus_wdata_q;
  logic [FAB_STRB_W-1:0]  bus_wstrb_q;
  logic [FAB_SIZE_W-1:0]  bus_size_q;
  logic [FAB_ATTR_W-1:0]  bus_attr_q;
  logic [FAB_ID_W-1:0]    bus_id_q;

  wire bus_req_ready = bus_is_io_q ? io_if.req_ready : mem_if.req_ready;
  wire bus_rsp_valid = bus_is_io_q ? io_if.rsp_valid : mem_if.rsp_valid;
  wire [FAB_DATA_W-1:0] bus_rsp_rdata = bus_is_io_q ? io_if.rsp_rdata : mem_if.rsp_rdata;
  wire [FAB_CODE_W-1:0] bus_rsp_code  = bus_is_io_q ? io_if.rsp_code  : mem_if.rsp_code;

  wire bus_req_fire = (state_q == ST_BUS_REQ) && bus_req_ready;
  wire bus_rsp_fire = (state_q == ST_BUS_RSP) && bus_rsp_valid;

  // Drive fabric interfaces (master)
  assign mem_if.req_valid = (state_q == ST_BUS_REQ) && !bus_is_io_q;
  assign mem_if.req_op    = bus_op_q;
  assign mem_if.req_addr  = bus_addr_q;
  assign mem_if.req_wdata = bus_wdata_q;
  assign mem_if.req_wstrb = bus_wstrb_q;
  assign mem_if.req_size  = bus_size_q;
  assign mem_if.req_attr  = bus_attr_q;
  assign mem_if.req_id    = bus_id_q;
  assign mem_if.rsp_ready = (state_q == ST_BUS_RSP) && !bus_is_io_q;

  assign io_if.req_valid = (state_q == ST_BUS_REQ) && bus_is_io_q;
  assign io_if.req_op    = bus_op_q;
  assign io_if.req_addr  = bus_addr_q;
  assign io_if.req_wdata = bus_wdata_q;
  assign io_if.req_wstrb = bus_wstrb_q;
  assign io_if.req_size  = bus_size_q;
  assign io_if.req_attr  = bus_attr_q;
  assign io_if.req_id    = bus_id_q;
  assign io_if.rsp_ready = (state_q == ST_BUS_RSP) && bus_is_io_q;

  // --------------------------------------------------------------------------
  // Instruction staging and temporaries
  // --------------------------------------------------------------------------
  logic [15:0] insn_pc_q;
  logic [7:0]  b0_q, b1_q, b2_q, b3_q, b4_q, b5_q, b6_q;
  logic [7:0]  mem_lo_q, mem_hi_q;
  logic [15:0] eff_addr_q;
  logic [3:0]  z90_rd_q;
  logic [3:0]  z90_rs_q;

  // --------------------------------------------------------------------------
  // Helpers
  // --------------------------------------------------------------------------
  function automatic logic [15:0] x_read(input logic [3:0] idx);
    begin
      if (idx == 4'd0) x_read = 16'h0000;
      else x_read = x_q[idx];
    end
  endfunction

  function automatic logic z90_fastpath_allowed();
    logic strict;
    begin
      strict = (modeflags_q & CARBON_MODEFLAG_STRICT_MASK) != 0;
      z90_fastpath_allowed =
          (!strict) && (tier_q == 8'(CARBON_Z80_DERIVED_TIER_P3_Z180));
    end
  endfunction

  task automatic trap_now(input logic [31:0] cause);
    begin
      csr_cause_q <= cause;
      csr_epc_q   <= {16'h0000, insn_pc_q};
      halt_trap_q <= 1'b1;
      state_q     <= ST_BOUNDARY;
    end
  endtask

  integer xi;
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      z80_q <= '0;
      for (xi = 0; xi < 16; xi++) begin
        x_q[xi] <= '0;
      end
      z90_flags_q <= '0;
      tier_q <= 8'(CARBON_Z80_DERIVED_TIER_P0_I8080);
      modeflags_q <= 8'(CARBON_MODEFLAG_STRICT_MASK);
      md_sp_q <= '0;
      for (xi = 0; xi < int'(MODESTACK_DEPTH); xi++) begin
        md_tier_q[xi]  <= '0;
        md_flags_q[xi] <= '0;
        md_pc_q[xi]    <= '0;
      end

      csr_rsp_valid_q <= 1'b0;
      csr_rsp_rdata_q <= '0;
      csr_rsp_fault_q <= 1'b0;
      csr_rsp_side_q  <= 1'b0;

      csr_cause_q <= '0;
      csr_epc_q   <= '0;
      csr_trace_ctl_q <= '0;

      csr_z90_mmu_win0_base_q <= '0;
      csr_z90_mmu_win0_mask_q <= '0;
      csr_z90_mmu_win1_base_q <= '0;
      csr_z90_mmu_win1_mask_q <= '0;
      csr_z90_cache_ctl_q <= '0;
      csr_z90_atomic_ctl_q <= 32'h0000_0001;
      csr_z90_atomic_status_q <= '0;

      cycle_q <= 64'd0;

      halt_debug_q <= 1'b0;
      halt_instr_q <= 1'b0;
      halt_trap_q  <= 1'b0;
      step_token_q <= 1'b0;
      step_ack_pulse_q <= 1'b0;

      cai_submit_desc_base_q <= '0;
      cai_submit_ring_mask_q <= '0;
      cai_comp_base_q        <= '0;
      cai_context_sel_q      <= '0;
      cai_submit_pulse_q     <= 1'b0;

      insn_pc_q <= '0;
      b0_q <= '0;
      b1_q <= '0;
      b2_q <= '0;
      b3_q <= '0;
      b4_q <= '0;
      b5_q <= '0;
      b6_q <= '0;
      mem_lo_q <= '0;
      mem_hi_q <= '0;
      eff_addr_q <= '0;
      z90_rd_q <= '0;
      z90_rs_q <= '0;

      state_after_bus_q <= ST_BOUNDARY;
      bus_dest_q <= DEST_NONE;
      bus_is_io_q <= 1'b0;
      bus_op_q <= '0;
      bus_addr_q <= '0;
      bus_wdata_q <= '0;
      bus_wstrb_q <= '0;
      bus_size_q <= '0;
      bus_attr_q <= '0;
      bus_id_q <= '0;

      state_q <= ST_RESET;
    end else begin
      cycle_q <= cycle_q + 64'd1;
      step_ack_pulse_q <= 1'b0;
      cai_submit_pulse_q <= 1'b0;

      if (dbg.halt_req) halt_debug_q <= 1'b1;
      if (dbg.run_req)  halt_debug_q <= 1'b0;
      if (dbg.step_req && halt_debug_q && !step_token_q) begin
        step_token_q <= 1'b1;
      end

      if (csr_rsp_fire) csr_rsp_valid_q <= 1'b0;

      if (csr_req_fire) begin
        csr_rsp_valid_q <= 1'b1;
        csr_rsp_fault_q <= 1'b0;
        csr_rsp_side_q  <= csr.req_write;
        csr_rsp_rdata_q <= '0;

        unique case (csr.req_addr)
          CARBON_CSR_ID: begin
            if (!csr.req_write) csr_rsp_rdata_q <= 32'h5A39_3001; // "Z90"+v1 (impl-defined)
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
              // Reserved bits must be 0.
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
            if (!csr.req_write) begin
              csr_rsp_rdata_q <= csr_epc_q;
            end else begin
              if (csr.req_priv < CSR_PRIV_W'(1)) csr_rsp_fault_q <= 1'b1;
              else csr_epc_q <= csr.req_wdata;
            end
          end
          CARBON_CSR_TRACE_CTL: begin
            if (!csr.req_write) begin
              csr_rsp_rdata_q <= csr_trace_ctl_q;
            end else begin
              if (csr.req_priv < CSR_PRIV_W'(1)) csr_rsp_fault_q <= 1'b1;
              else csr_trace_ctl_q <= csr.req_wdata;
            end
          end

          CARBON_CSR_Z90_MMU_WIN0_BASE: begin
            if (!csr.req_write) csr_rsp_rdata_q <= csr_z90_mmu_win0_base_q;
            else if (csr.req_priv < CSR_PRIV_W'(1)) csr_rsp_fault_q <= 1'b1;
            else csr_z90_mmu_win0_base_q <= csr.req_wdata;
          end
          CARBON_CSR_Z90_MMU_WIN0_MASK: begin
            if (!csr.req_write) csr_rsp_rdata_q <= csr_z90_mmu_win0_mask_q;
            else if (csr.req_priv < CSR_PRIV_W'(1)) csr_rsp_fault_q <= 1'b1;
            else csr_z90_mmu_win0_mask_q <= csr.req_wdata;
          end
          CARBON_CSR_Z90_MMU_WIN1_BASE: begin
            if (!csr.req_write) csr_rsp_rdata_q <= csr_z90_mmu_win1_base_q;
            else if (csr.req_priv < CSR_PRIV_W'(1)) csr_rsp_fault_q <= 1'b1;
            else csr_z90_mmu_win1_base_q <= csr.req_wdata;
          end
          CARBON_CSR_Z90_MMU_WIN1_MASK: begin
            if (!csr.req_write) csr_rsp_rdata_q <= csr_z90_mmu_win1_mask_q;
            else if (csr.req_priv < CSR_PRIV_W'(1)) csr_rsp_fault_q <= 1'b1;
            else csr_z90_mmu_win1_mask_q <= csr.req_wdata;
          end
          CARBON_CSR_Z90_CACHE_CTL: begin
            if (!csr.req_write) csr_rsp_rdata_q <= csr_z90_cache_ctl_q;
            else if (csr.req_priv < CSR_PRIV_W'(1)) csr_rsp_fault_q <= 1'b1;
            else csr_z90_cache_ctl_q <= csr.req_wdata;
          end
          CARBON_CSR_Z90_ATOMIC_CTL: begin
            if (!csr.req_write) csr_rsp_rdata_q <= csr_z90_atomic_ctl_q;
            else if (csr.req_priv < CSR_PRIV_W'(1)) csr_rsp_fault_q <= 1'b1;
            else csr_z90_atomic_ctl_q <= csr.req_wdata;
          end
          CARBON_CSR_Z90_ATOMIC_STATUS: begin
            if (!csr.req_write) csr_rsp_rdata_q <= csr_z90_atomic_status_q;
            else csr_rsp_fault_q <= 1'b1;
          end
          default: begin
            csr_rsp_fault_q <= 1'b1;
          end
        endcase
      end

      unique case (state_q)
        ST_RESET: begin
          state_q <= ST_BOUNDARY;
        end

        ST_BOUNDARY: begin
          // Debug single-step completion: after running one instruction we return
          // to ST_BOUNDARY with halt_debug_q cleared.
          if (step_token_q && !halt_debug_q && !halt_trap_q && !halt_instr_q) begin
            halt_debug_q <= 1'b1;
            step_token_q <= 1'b0;
            step_ack_pulse_q <= 1'b1;
          end else begin
            // Debug single-step start: temporarily clear debug halt to run 1 insn.
            if (step_token_q && halt_debug_q && !halt_trap_q && !halt_instr_q) begin
              halt_debug_q <= 1'b0;
            end

            if (core_halted && !step_token_q) begin
              // Stopped.
            end else begin
              insn_pc_q <= z80_q.PC;

              // Fetch b0
              bus_is_io_q <= 1'b0;
              bus_op_q <= FAB_OP_W'(CARBON_FABRIC_XACT_READ);
              bus_addr_q <= FAB_ADDR_W'({{(FAB_ADDR_W-16){1'b0}}, z80_q.PC});
              bus_wdata_q <= '0;
              bus_wstrb_q <= '0;
              bus_size_q <= '0;
              bus_attr_q <= MEM_ATTR;
              bus_id_q <= '0;
              bus_dest_q <= DEST_B0;
              state_after_bus_q <= ST_DECODE0;
              state_q <= ST_BUS_REQ;
            end
          end
        end

        ST_BUS_REQ: begin
          if (bus_req_fire) begin
            state_q <= ST_BUS_RSP;
          end
        end

        ST_BUS_RSP: begin
          if (bus_rsp_fire) begin
            if (bus_rsp_code != FAB_CODE_W'(CARBON_FABRIC_RESP_OK)) begin
              trap_now(Z90_CAUSE_BUS_FAULT);
            end else begin
              unique case (bus_dest_q)
                DEST_B0: begin
                  b0_q <= bus_rsp_rdata[7:0];
                  z80_q.PC <= z80_q.PC + 16'd1;
                end
                DEST_B1: begin
                  b1_q <= bus_rsp_rdata[7:0];
                  z80_q.PC <= z80_q.PC + 16'd1;
                end
                DEST_B2: begin
                  b2_q <= bus_rsp_rdata[7:0];
                  z80_q.PC <= z80_q.PC + 16'd1;
                end
                DEST_B3: begin
                  b3_q <= bus_rsp_rdata[7:0];
                  z80_q.PC <= z80_q.PC + 16'd1;
                end
                DEST_B4: begin
                  b4_q <= bus_rsp_rdata[7:0];
                  z80_q.PC <= z80_q.PC + 16'd1;
                end
                DEST_B5: begin
                  b5_q <= bus_rsp_rdata[7:0];
                  z80_q.PC <= z80_q.PC + 16'd1;
                end
                DEST_B6: begin
                  b6_q <= bus_rsp_rdata[7:0];
                  z80_q.PC <= z80_q.PC + 16'd1;
                end
                DEST_MEM_LO: begin
                  mem_lo_q <= bus_rsp_rdata[7:0];
                end
                DEST_MEM_HI: begin
                  mem_hi_q <= bus_rsp_rdata[7:0];
                end
                DEST_ATOMIC: begin
                  mem_lo_q <= bus_rsp_rdata[7:0];
                  mem_hi_q <= bus_rsp_rdata[15:8];
                  csr_z90_atomic_status_q[0] <= bus_rsp_rdata[31];
                end
                default: begin end
              endcase

              state_q <= state_after_bus_q;
            end
          end
        end

        // ------------------------------------------------------------------
        // Legacy (small subset, 8080-compatible)
        // ------------------------------------------------------------------
        ST_DECODE0: begin
          unique case (b0_q)
            8'h00: begin // NOP
              state_q <= ST_BOUNDARY;
            end
            8'h76: begin // HALT
              halt_instr_q <= 1'b1;
              state_q <= ST_BOUNDARY;
            end

            // LD r,n (B,C,D,E,H,L,A)
            8'h06, 8'h0E, 8'h16, 8'h1E, 8'h26, 8'h2E, 8'h3E: begin
              bus_is_io_q <= 1'b0;
              bus_op_q <= FAB_OP_W'(CARBON_FABRIC_XACT_READ);
              bus_addr_q <= FAB_ADDR_W'({{(FAB_ADDR_W-16){1'b0}}, z80_q.PC});
              bus_wdata_q <= '0;
              bus_wstrb_q <= '0;
              bus_size_q <= '0;
              bus_attr_q <= MEM_ATTR;
              bus_id_q <= '0;
              bus_dest_q <= DEST_B1;
              state_after_bus_q <= ST_FETCH_ED1;
              state_q <= ST_BUS_REQ;
            end

            // ADD A,r (excluding (HL))
            8'h80, 8'h81, 8'h82, 8'h83, 8'h84, 8'h85, 8'h87: begin
              z85_alu8_t o;
              logic [2:0] r;
              r = b0_q[2:0];
              o = alu_add8(z80_q.A, get_r8(z80_q, r, Z85_IDX_NONE));
              z80_q.A <= o.res;
              z80_q.F <= o.f;
              state_q <= ST_BOUNDARY;
            end

            8'hED: begin // Z90 opcode page escape
              bus_is_io_q <= 1'b0;
              bus_op_q <= FAB_OP_W'(CARBON_FABRIC_XACT_READ);
              bus_addr_q <= FAB_ADDR_W'({{(FAB_ADDR_W-16){1'b0}}, z80_q.PC});
              bus_wdata_q <= '0;
              bus_wstrb_q <= '0;
              bus_size_q <= '0;
              bus_attr_q <= MEM_ATTR;
              bus_id_q <= '0;
              bus_dest_q <= DEST_B1;
              state_after_bus_q <= ST_DECODE_ED;
              state_q <= ST_BUS_REQ;
            end

            default: begin
              trap_now(Z90_CAUSE_ILLEGAL_INSN);
            end
          endcase
        end

        ST_FETCH_ED1: begin
          // LD r,n writeback
          unique case (b0_q)
            8'h06: z80_q.B <= b1_q;
            8'h0E: z80_q.C <= b1_q;
            8'h16: z80_q.D <= b1_q;
            8'h1E: z80_q.E <= b1_q;
            8'h26: z80_q.H <= b1_q;
            8'h2E: z80_q.L <= b1_q;
            8'h3E: z80_q.A <= b1_q;
            default: begin end
          endcase
          state_q <= ST_BOUNDARY;
        end

        ST_DECODE_ED: begin
          if (b1_q == CARBON_Z90_OPPAGE_P0_PREFIX1) begin
            // Fetch op0 -> b2
            bus_is_io_q <= 1'b0;
            bus_op_q <= FAB_OP_W'(CARBON_FABRIC_XACT_READ);
            bus_addr_q <= FAB_ADDR_W'({{(FAB_ADDR_W-16){1'b0}}, z80_q.PC});
            bus_wdata_q <= '0;
            bus_wstrb_q <= '0;
            bus_size_q <= '0;
            bus_attr_q <= MEM_ATTR;
            bus_id_q <= '0;
            bus_dest_q <= DEST_B2;
            state_after_bus_q <= ST_Z90_P0_FETCH_OP1;
            state_q <= ST_BUS_REQ;
          end else if (b1_q == CARBON_Z90_OPPAGE_P1_PREFIX1) begin
            // Fetch op0 -> b2
            bus_is_io_q <= 1'b0;
            bus_op_q <= FAB_OP_W'(CARBON_FABRIC_XACT_READ);
            bus_addr_q <= FAB_ADDR_W'({{(FAB_ADDR_W-16){1'b0}}, z80_q.PC});
            bus_wdata_q <= '0;
            bus_wstrb_q <= '0;
            bus_size_q <= '0;
            bus_attr_q <= MEM_ATTR;
            bus_id_q <= '0;
            bus_dest_q <= DEST_B2;
            state_after_bus_q <= ST_Z90_P1_FETCH_OP1;
            state_q <= ST_BUS_REQ;
          end else begin
            trap_now(Z90_CAUSE_ILLEGAL_INSN);
          end
        end

        // ------------------------------------------------------------------
        // Z90 page0
        // ------------------------------------------------------------------
        ST_Z90_P0_FETCH_OP1: begin
          // Fetch op1 -> b3
          bus_is_io_q <= 1'b0;
          bus_op_q <= FAB_OP_W'(CARBON_FABRIC_XACT_READ);
          bus_addr_q <= FAB_ADDR_W'({{(FAB_ADDR_W-16){1'b0}}, z80_q.PC});
          bus_wdata_q <= '0;
          bus_wstrb_q <= '0;
          bus_size_q <= '0;
          bus_attr_q <= MEM_ATTR;
          bus_id_q <= '0;
          bus_dest_q <= DEST_B3;
          state_after_bus_q <= ST_Z90_P0_DISPATCH;
          state_q <= ST_BUS_REQ;
        end

        ST_Z90_P0_DISPATCH: begin
          logic [3:0] major;
          logic [3:0] rd;
          logic [3:0] sub;
          logic [3:0] rs;
          logic is_modeop;

          major = hi_nibble(b2_q);
          rd    = lo_nibble(b2_q);
          sub   = hi_nibble(b3_q);
          rs    = lo_nibble(b3_q);

          z90_rd_q <= rd;
          z90_rs_q <= rs;

          is_modeop =
              (major == 4'(CARBON_Z90_P0_MAJOR_SYS)) &&
              ((sub == 4'(CARBON_Z90_P0_SUB_MODEUP)) || (sub == 4'(CARBON_Z90_P0_SUB_RETMD)));

          if (!is_modeop && !z90_fastpath_allowed()) begin
            trap_now(Z90_CAUSE_ILLEGAL_INSN);
          end else begin
            unique case (major)
              4'(CARBON_Z90_P0_MAJOR_REG): begin
                unique case (sub)
                  4'(CARBON_Z90_P0_SUB_MOV): begin
                    if (rd != 4'd0) x_q[rd] <= x_read(rs);
                    state_q <= ST_BOUNDARY;
                  end
                  4'(CARBON_Z90_P0_SUB_XCHG): begin
                    logic [15:0] a, b;
                    a = x_read(rd);
                    b = x_read(rs);
                    if (rd != 4'd0) x_q[rd] <= b;
                    if (rs != 4'd0) x_q[rs] <= a;
                    state_q <= ST_BOUNDARY;
                  end
                  default: begin
                    trap_now(Z90_CAUSE_ILLEGAL_INSN);
                  end
                endcase
              end

              4'(CARBON_Z90_P0_MAJOR_ALU): begin
                z90_alu16_t o16;
                unique case (sub)
                  4'(CARBON_Z90_P0_SUB_ADD): o16 = alu_add16(x_read(rd), x_read(rs));
                  4'(CARBON_Z90_P0_SUB_SUB): o16 = alu_sub16(x_read(rd), x_read(rs));
                  4'(CARBON_Z90_P0_SUB_AND): o16 = alu_and16(x_read(rd), x_read(rs));
                  4'(CARBON_Z90_P0_SUB_OR):  o16 = alu_or16(x_read(rd), x_read(rs));
                  4'(CARBON_Z90_P0_SUB_XOR): o16 = alu_xor16(x_read(rd), x_read(rs));
                  4'(CARBON_Z90_P0_SUB_CMP): o16 = alu_sub16(x_read(rd), x_read(rs));
                  default: begin
                    o16.res = '0;
                    o16.f   = '0;
                    trap_now(Z90_CAUSE_ILLEGAL_INSN);
                  end
                endcase

                if (sub != 4'(CARBON_Z90_P0_SUB_CMP)) begin
                  if (rd != 4'd0) x_q[rd] <= o16.res;
                end
                z90_flags_q <= o16.f;
                state_q <= ST_BOUNDARY;
              end

              4'(CARBON_Z90_P0_MAJOR_SYS): begin
                unique case (sub)
                  4'(CARBON_Z90_P0_SUB_MODEUP): begin
                    // Fetch target_tier -> b4, entry_lo -> b5, entry_hi -> b6
                    bus_is_io_q <= 1'b0;
                    bus_op_q <= FAB_OP_W'(CARBON_FABRIC_XACT_READ);
                    bus_addr_q <= FAB_ADDR_W'({{(FAB_ADDR_W-16){1'b0}}, z80_q.PC});
                    bus_wdata_q <= '0;
                    bus_wstrb_q <= '0;
                    bus_size_q <= '0;
                    bus_attr_q <= MEM_ATTR;
                    bus_id_q <= '0;
                    bus_dest_q <= DEST_B4;
                    state_after_bus_q <= ST_Z90_MODEUP_FETCH_LO;
                    state_q <= ST_BUS_REQ;
                  end
                  4'(CARBON_Z90_P0_SUB_RETMD): begin
                    if (md_sp_q == 0) begin
                      trap_now(Z90_CAUSE_MODESTACK_UNDERFLOW);
                    end else begin
                      md_sp_q <= md_sp_q - 1'b1;
                      tier_q <= md_tier_q[md_sp_q - 1'b1];
                      modeflags_q <= md_flags_q[md_sp_q - 1'b1];
                      z80_q.PC <= md_pc_q[md_sp_q - 1'b1];
                      state_q <= ST_BOUNDARY;
                    end
                  end
                  4'(CARBON_Z90_P0_SUB_CAI_CFG): begin
                    // Minimal mapping: fixed X registers as configuration sources.
                    cai_submit_desc_base_q <= {32'h0000_0000, x_read(4'd3), x_read(4'd2)};
                    cai_comp_base_q        <= {32'h0000_0000, x_read(4'd5), x_read(4'd4)};
                    cai_submit_ring_mask_q <= {16'h0000, x_read(4'd6)};
                    cai_context_sel_q      <= x_read(4'd7);
                    state_q <= ST_BOUNDARY;
                  end
                  4'(CARBON_Z90_P0_SUB_CAI_SUBMIT): begin
                    cai_submit_pulse_q <= 1'b1;
                    state_q <= ST_BOUNDARY;
                  end
                  default: begin
                    trap_now(Z90_CAUSE_ILLEGAL_INSN);
                  end
                endcase
              end

              default: begin
                trap_now(Z90_CAUSE_ILLEGAL_INSN);
              end
            endcase
          end
        end

        // MODEUP immediate fetch chain
        ST_Z90_MODEUP_FETCH_LO: begin
          bus_is_io_q <= 1'b0;
          bus_op_q <= FAB_OP_W'(CARBON_FABRIC_XACT_READ);
          bus_addr_q <= FAB_ADDR_W'({{(FAB_ADDR_W-16){1'b0}}, z80_q.PC});
          bus_wdata_q <= '0;
          bus_wstrb_q <= '0;
          bus_size_q <= '0;
          bus_attr_q <= MEM_ATTR;
          bus_id_q <= '0;
          bus_dest_q <= DEST_B5;
          state_after_bus_q <= ST_Z90_MODEUP_FETCH_HI;
          state_q <= ST_BUS_REQ;
        end

        ST_Z90_MODEUP_FETCH_HI: begin
          bus_is_io_q <= 1'b0;
          bus_op_q <= FAB_OP_W'(CARBON_FABRIC_XACT_READ);
          bus_addr_q <= FAB_ADDR_W'({{(FAB_ADDR_W-16){1'b0}}, z80_q.PC});
          bus_wdata_q <= '0;
          bus_wstrb_q <= '0;
          bus_size_q <= '0;
          bus_attr_q <= MEM_ATTR;
          bus_id_q <= '0;
          bus_dest_q <= DEST_B6;
          state_after_bus_q <= ST_Z90_MODEUP_EXEC;
          state_q <= ST_BUS_REQ;
        end

        ST_Z90_MODEUP_EXEC: begin
          logic [7:0] target;
          logic [15:0] entry;
          target = b4_q;
          entry = {b6_q, b5_q};

          // Only ladder 0 (Z80-derived) supported in this core scaffolding.
          if (z90_rs_q != 4'd0) begin
            trap_now(Z90_CAUSE_MODEUP_INVALID);
          end else if (target <= tier_q) begin
            trap_now(Z90_CAUSE_MODEUP_INVALID);
          end else if (md_sp_q == MD_SP_W'(MODESTACK_DEPTH)) begin
            trap_now(Z90_CAUSE_MODESTACK_OVERFLOW);
          end else begin
            md_tier_q[md_sp_q]  <= tier_q;
            md_flags_q[md_sp_q] <= modeflags_q;
            md_pc_q[md_sp_q]    <= z80_q.PC; // return PC is after MODEUP immediates
            md_sp_q <= md_sp_q + 1'b1;

            tier_q <= target;
            z80_q.PC <= entry;
            state_q <= ST_BOUNDARY;
          end
        end

        // ------------------------------------------------------------------
        // Z90 page1 (memory/addressing/atomics)
        // ------------------------------------------------------------------
        ST_Z90_P1_FETCH_OP1: begin
          // Fetch op1 -> b3
          bus_is_io_q <= 1'b0;
          bus_op_q <= FAB_OP_W'(CARBON_FABRIC_XACT_READ);
          bus_addr_q <= FAB_ADDR_W'({{(FAB_ADDR_W-16){1'b0}}, z80_q.PC});
          bus_wdata_q <= '0;
          bus_wstrb_q <= '0;
          bus_size_q <= '0;
          bus_attr_q <= MEM_ATTR;
          bus_id_q <= '0;
          bus_dest_q <= DEST_B3;
          state_after_bus_q <= ST_Z90_P1_FETCH_DISP;
          state_q <= ST_BUS_REQ;
        end

        ST_Z90_P1_FETCH_DISP: begin
          // Fetch disp8 -> b4
          bus_is_io_q <= 1'b0;
          bus_op_q <= FAB_OP_W'(CARBON_FABRIC_XACT_READ);
          bus_addr_q <= FAB_ADDR_W'({{(FAB_ADDR_W-16){1'b0}}, z80_q.PC});
          bus_wdata_q <= '0;
          bus_wstrb_q <= '0;
          bus_size_q <= '0;
          bus_attr_q <= MEM_ATTR;
          bus_id_q <= '0;
          bus_dest_q <= DEST_B4;
          state_after_bus_q <= ST_Z90_P1_DISPATCH;
          state_q <= ST_BUS_REQ;
        end

        ST_Z90_P1_DISPATCH: begin
          logic [3:0] major;
          logic [3:0] rd;
          logic [3:0] base;
          logic [3:0] index;
          logic signed [15:0] disp;
          logic signed [16:0] addr_s;
          logic [15:0] eff;

          if (!z90_fastpath_allowed()) begin
            trap_now(Z90_CAUSE_ILLEGAL_INSN);
          end else begin
            major = hi_nibble(b2_q);
            rd    = lo_nibble(b2_q);
            base  = hi_nibble(b3_q);
            index = lo_nibble(b3_q);
            disp  = sext8_to_s16(b4_q);

            z90_rd_q <= rd;
            z90_rs_q <= index;

            unique case (major)
              4'(CARBON_Z90_P1_OP_LEA): begin
                addr_s = $signed({1'b0, x_read(base)}) + $signed({1'b0, x_read(index)}) + $signed(disp);
                eff = addr_s[15:0];
                eff_addr_q <= eff;
                if (rd != 4'd0) x_q[rd] <= eff;
                state_q <= ST_BOUNDARY;
              end

              4'(CARBON_Z90_P1_OP_LD16): begin
                addr_s = $signed({1'b0, x_read(base)}) + $signed({1'b0, x_read(index)}) + $signed(disp);
                eff = addr_s[15:0];
                eff_addr_q <= eff;

                bus_is_io_q <= 1'b0;
                bus_op_q <= FAB_OP_W'(CARBON_FABRIC_XACT_READ);
                bus_addr_q <= FAB_ADDR_W'({{(FAB_ADDR_W-16){1'b0}}, eff});
                bus_wdata_q <= '0;
                bus_wstrb_q <= '0;
                bus_size_q <= '0;
                bus_attr_q <= MEM_ATTR;
                bus_id_q <= '0;
                bus_dest_q <= DEST_MEM_LO;
                state_after_bus_q <= ST_Z90_LD16_FETCH_HI;
                state_q <= ST_BUS_REQ;
              end

              4'(CARBON_Z90_P1_OP_ST16): begin
                addr_s = $signed({1'b0, x_read(base)}) + $signed({1'b0, x_read(index)}) + $signed(disp);
                eff = addr_s[15:0];
                eff_addr_q <= eff;

                bus_is_io_q <= 1'b0;
                bus_op_q <= FAB_OP_W'(CARBON_FABRIC_XACT_WRITE);
                bus_addr_q <= FAB_ADDR_W'({{(FAB_ADDR_W-16){1'b0}}, eff});
                bus_wdata_q <= FAB_DATA_W'({{(FAB_DATA_W-8){1'b0}}, x_read(rd)[7:0]});
                bus_wstrb_q <= FAB_STRB_W'({{(FAB_STRB_W-1){1'b0}}, 1'b1});
                bus_size_q <= '0;
                bus_attr_q <= MEM_ATTR;
                bus_id_q <= '0;
                bus_dest_q <= DEST_NONE;
                state_after_bus_q <= ST_Z90_ST16_WRITE_HI;
                state_q <= ST_BUS_REQ;
              end

              4'(CARBON_Z90_P1_OP_CAS16): begin
                // Address = base + disp (index is desired-value register).
                if (!csr_z90_atomic_ctl_q[0]) begin
                  trap_now(Z90_CAUSE_ILLEGAL_INSN);
                end else begin
                  addr_s = $signed({1'b0, x_read(base)}) + $signed(disp);
                  eff = addr_s[15:0];
                  eff_addr_q <= eff;

                  bus_is_io_q <= 1'b0;
                  bus_op_q <= FAB_OP_W'(CARBON_FABRIC_XACT_ATOMIC);
                  bus_addr_q <= FAB_ADDR_W'({{(FAB_ADDR_W-16){1'b0}}, eff});
                  bus_wdata_q <= FAB_DATA_W'({16'h0000, x_read(index), x_read(rd)});
                  bus_wstrb_q <= '0;
                  bus_size_q <= '0;
                  bus_attr_q <= ATOMIC_ATTR;
                  bus_id_q <= '0;
                  bus_dest_q <= DEST_ATOMIC;
                  state_after_bus_q <= ST_Z90_CAS16_DONE;
                  state_q <= ST_BUS_REQ;
                end
              end

              default: begin
                trap_now(Z90_CAUSE_ILLEGAL_INSN);
              end
            endcase
          end
        end

        ST_Z90_LD16_FETCH_HI: begin
          bus_is_io_q <= 1'b0;
          bus_op_q <= FAB_OP_W'(CARBON_FABRIC_XACT_READ);
          bus_addr_q <= FAB_ADDR_W'({{(FAB_ADDR_W-16){1'b0}}, (eff_addr_q + 16'd1)});
          bus_wdata_q <= '0;
          bus_wstrb_q <= '0;
          bus_size_q <= '0;
          bus_attr_q <= MEM_ATTR;
          bus_id_q <= '0;
          bus_dest_q <= DEST_MEM_HI;
          state_after_bus_q <= ST_Z90_LD16_DONE;
          state_q <= ST_BUS_REQ;
        end

        ST_Z90_LD16_DONE: begin
          if (z90_rd_q != 4'd0) x_q[z90_rd_q] <= {mem_hi_q, mem_lo_q};
          state_q <= ST_BOUNDARY;
        end

        ST_Z90_ST16_WRITE_HI: begin
          bus_is_io_q <= 1'b0;
          bus_op_q <= FAB_OP_W'(CARBON_FABRIC_XACT_WRITE);
          bus_addr_q <= FAB_ADDR_W'({{(FAB_ADDR_W-16){1'b0}}, (eff_addr_q + 16'd1)});
          bus_wdata_q <= FAB_DATA_W'({{(FAB_DATA_W-8){1'b0}}, x_read(z90_rd_q)[15:8]});
          bus_wstrb_q <= FAB_STRB_W'({{(FAB_STRB_W-1){1'b0}}, 1'b1});
          bus_size_q <= '0;
          bus_attr_q <= MEM_ATTR;
          bus_id_q <= '0;
          bus_dest_q <= DEST_NONE;
          state_after_bus_q <= ST_Z90_ST16_DONE;
          state_q <= ST_BUS_REQ;
        end

        ST_Z90_ST16_DONE: begin
          state_q <= ST_BOUNDARY;
        end

        ST_Z90_CAS16_DONE: begin
          logic [15:0] oldv;
          logic success;
          oldv = {mem_hi_q, mem_lo_q};
          success = (oldv == x_read(z90_rd_q));
          if (z90_rd_q != 4'd0) x_q[z90_rd_q] <= oldv;
          z90_flags_q <= (success ? Z90_F_Z : 8'h00);
          csr_z90_atomic_status_q[1] <= success;
          state_q <= ST_BOUNDARY;
        end

        default: begin
          trap_now(Z90_CAUSE_ILLEGAL_INSN);
        end
      endcase
    end
  end

endmodule : z90_core
