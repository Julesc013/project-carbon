// Project Carbon - Z480 P7 core
// z480_core: Minimal in-order scaffold for the native 64-bit tier.

module z480_core #(
    parameter logic [31:0] IO_BASE = 32'h000F_0000,
    parameter logic [31:0] IO_MASK = 32'hFFFF_0000
) (
    input logic clk,
    input logic rst_n,

    fabric_if.master mem_if,
    irq_if.sink irq,
    csr_if.slave csr,
    dbg_if.core dbg
);
  import carbon_arch_pkg::*;
  import z480_pkg::*;

  localparam int unsigned FAB_ADDR_W = $bits(mem_if.req_addr);
  localparam int unsigned FAB_DATA_W = $bits(mem_if.req_wdata);
  localparam int unsigned FAB_STRB_W = $bits(mem_if.req_wstrb);
  localparam int unsigned FAB_OP_W   = $bits(mem_if.req_op);
  localparam int unsigned FAB_SIZE_W = $bits(mem_if.req_size);
  localparam int unsigned FAB_ATTR_W = $bits(mem_if.req_attr);
  localparam int unsigned FAB_ID_W   = $bits(mem_if.req_id);
  localparam int unsigned FAB_CODE_W = $bits(mem_if.rsp_code);

  localparam logic [FAB_ATTR_W-1:0] MEM_ATTR =
      FAB_ATTR_W'(CARBON_FABRIC_ATTR_CACHEABLE_MASK);
  localparam logic [FAB_ATTR_W-1:0] IO_ATTR =
      FAB_ATTR_W'(CARBON_FABRIC_ATTR_ORDERED_MASK | CARBON_FABRIC_ATTR_IO_SPACE_MASK);

  // --------------------------------------------------------------------------
  // CSR implementation (minimal + CPUID window).
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

  // Debug pulses
  logic csr_halt_pulse_q;
  logic csr_run_pulse_q;
  logic csr_step_pulse_q;

  // Core-originated trap update
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

  // CPUID leaf implementation
  logic [63:0] cpuid_data0;
  logic [63:0] cpuid_data1;
  logic [63:0] cpuid_data2;
  logic [63:0] cpuid_data3;

  cpuid_block #(
      .CORE_COUNT(1),
      .VECTOR_BITS(128)
  ) u_cpuid (
      .leaf(csr_cpuid_leaf_q),
      .subleaf(csr_cpuid_subleaf_q),
      .data0(cpuid_data0),
      .data1(cpuid_data1),
      .data2(cpuid_data2),
      .data3(cpuid_data3)
  );

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
            if (!csr.req_write) csr_rsp_rdata_q <= 32'h5A34_8001; // "Z480"+v1
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
            if (!csr.req_write) csr_rsp_rdata_q <= 32'h0;
            else csr_rsp_fault_q <= 1'b1;
          end
          CARBON_CSR_IP: begin
            if (!csr.req_write) csr_rsp_rdata_q <= 32'h0;
            else csr_rsp_fault_q <= 1'b1;
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
            if (!csr.req_write) csr_rsp_rdata_q <= cpuid_data0[31:0];
            else csr_rsp_fault_q <= 1'b1;
          end
          CARBON_CSR_CPUID_DATA0_HI: begin
            if (!csr.req_write) csr_rsp_rdata_q <= cpuid_data0[63:32];
            else csr_rsp_fault_q <= 1'b1;
          end
          CARBON_CSR_CPUID_DATA1_LO: begin
            if (!csr.req_write) csr_rsp_rdata_q <= cpuid_data1[31:0];
            else csr_rsp_fault_q <= 1'b1;
          end
          CARBON_CSR_CPUID_DATA1_HI: begin
            if (!csr.req_write) csr_rsp_rdata_q <= cpuid_data1[63:32];
            else csr_rsp_fault_q <= 1'b1;
          end
          CARBON_CSR_CPUID_DATA2_LO: begin
            if (!csr.req_write) csr_rsp_rdata_q <= cpuid_data2[31:0];
            else csr_rsp_fault_q <= 1'b1;
          end
          CARBON_CSR_CPUID_DATA2_HI: begin
            if (!csr.req_write) csr_rsp_rdata_q <= cpuid_data2[63:32];
            else csr_rsp_fault_q <= 1'b1;
          end
          CARBON_CSR_CPUID_DATA3_LO: begin
            if (!csr.req_write) csr_rsp_rdata_q <= cpuid_data3[31:0];
            else csr_rsp_fault_q <= 1'b1;
          end
          CARBON_CSR_CPUID_DATA3_HI: begin
            if (!csr.req_write) csr_rsp_rdata_q <= cpuid_data3[63:32];
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
  // Debug control
  // --------------------------------------------------------------------------
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
  // Simple fetch/execute scaffold (NOP only in v1 skeleton).
  // --------------------------------------------------------------------------
  typedef enum logic [2:0] {
    ST_RESET,
    ST_BOUNDARY,
    ST_BUS_REQ,
    ST_BUS_RSP,
    ST_DECODE,
    ST_TRAP
  } state_e;

  state_e state_q;
  state_e state_after_bus_q;

  logic [63:0] pc_q;
  logic [31:0] instr_q;
  logic trapped_q;

  logic [FAB_OP_W-1:0]   bus_op_q;
  logic [FAB_ADDR_W-1:0] bus_addr_q;
  logic [FAB_DATA_W-1:0] bus_wdata_q;
  logic [FAB_STRB_W-1:0] bus_wstrb_q;
  logic [FAB_SIZE_W-1:0] bus_size_q;
  logic [FAB_ATTR_W-1:0] bus_attr_q;

  assign mem_if.req_valid = (state_q == ST_BUS_REQ);
  assign mem_if.req_op    = bus_op_q;
  assign mem_if.req_addr  = bus_addr_q;
  assign mem_if.req_wdata = bus_wdata_q;
  assign mem_if.req_wstrb = bus_wstrb_q;
  assign mem_if.req_size  = bus_size_q;
  assign mem_if.req_attr  = bus_attr_q;
  assign mem_if.req_id    = '0;
  assign mem_if.rsp_ready = (state_q == ST_BUS_RSP);

  wire req_fire = mem_if.req_valid && mem_if.req_ready;
  wire rsp_fire = mem_if.rsp_valid && mem_if.rsp_ready;

  function automatic logic is_io_addr(input logic [63:0] addr);
    logic [31:0] lo;
    begin
      lo = addr[31:0];
      is_io_addr = ((lo & IO_MASK) == IO_BASE);
    end
  endfunction

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      state_q <= ST_RESET;
      state_after_bus_q <= ST_BOUNDARY;
      pc_q <= 64'h0;
      instr_q <= 32'h0;
      trapped_q <= 1'b0;
      csr_modeflags_q <= CARBON_MODEFLAG_STRICT_MASK;
      csr_tier_q <= 8'(CARBON_Z80_DERIVED_TIER_P7_Z480);

      dbg_halted_q <= 1'b0;
      dbg_step_pending_q <= 1'b0;
      dbg_step_inflight_q <= 1'b0;
      dbg_step_ack_q <= 1'b0;

      core_trap_pulse_q <= 1'b0;
      core_trap_cause_q <= '0;
      core_trap_epc_q   <= '0;

      bus_op_q <= '0;
      bus_addr_q <= '0;
      bus_wdata_q <= '0;
      bus_wstrb_q <= '0;
      bus_size_q <= '0;
      bus_attr_q <= '0;
    end else begin
      dbg_step_ack_q <= 1'b0;
      core_trap_pulse_q <= 1'b0;

      if (csr_modeflags_wr) csr_modeflags_q <= csr_modeflags_wdata;

      unique case (state_q)
        ST_RESET: begin
          trapped_q <= 1'b0;
          pc_q <= 64'h0;
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

            bus_op_q <= FAB_OP_W'(CARBON_FABRIC_XACT_READ);
            bus_addr_q <= FAB_ADDR_W'(pc_q[FAB_ADDR_W-1:0]);
            bus_wdata_q <= '0;
            bus_wstrb_q <= '0;
            bus_size_q <= FAB_SIZE_W'(2);
            bus_attr_q <= is_io_addr(pc_q) ? IO_ATTR : MEM_ATTR;
            state_after_bus_q <= ST_DECODE;
            state_q <= ST_BUS_REQ;
          end
        end

        ST_BUS_REQ: begin
          if (req_fire) state_q <= ST_BUS_RSP;
        end

        ST_BUS_RSP: begin
          if (rsp_fire) begin
            if (mem_if.rsp_code != FAB_CODE_W'(CARBON_FABRIC_RESP_OK)) begin
              trapped_q <= 1'b1;
              core_trap_pulse_q <= 1'b1;
              core_trap_cause_q <= 32'h0000_0002;
              core_trap_epc_q <= pc_q[31:0];
              state_q <= ST_TRAP;
            end else begin
              instr_q <= mem_if.rsp_rdata[31:0];
              pc_q <= pc_q + 64'd4;
              state_q <= state_after_bus_q;
            end
          end
        end

        ST_DECODE: begin
          state_q <= ST_BOUNDARY; // NOP-only skeleton
        end

        default: begin
          trapped_q <= 1'b1;
          core_trap_pulse_q <= 1'b1;
          core_trap_cause_q <= 32'h0000_0001;
          core_trap_epc_q <= pc_q[31:0];
          state_q <= ST_TRAP;
        end
      endcase
    end
  end

  // IRQ interface: unused in v1 skeleton.
  assign irq.irq_ack = 1'b0;
  assign irq.irq_ack_vector = '0;

  wire _unused = ^{instr_q, mem_if.rsp_id, mem_if.req_attr, mem_if.req_id};

endmodule : z480_core
