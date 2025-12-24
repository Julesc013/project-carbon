// Project Carbon - Z480 P7 core
// z480_core: Minimal in-order core for the native 64-bit tier (ISA v1).

module z480_core #(
    parameter logic [31:0] IO_BASE = 32'h000F_0000,
    parameter logic [31:0] IO_MASK = 32'hFFFF_0000,
    parameter logic [63:0] RESET_PC = 64'h0,
    parameter logic [63:0] DISCOVERY_PTR = 64'h0,
    parameter logic [63:0] BDT_PTR = 64'h0,
    parameter int unsigned BDT_ENTRY_COUNT = 0,
    parameter logic [63:0] TOPOLOGY_PTR = 64'h0,
    parameter logic [31:0] CPU_FEAT_WORD0 =
        carbon_arch_pkg::CARBON_FEAT_CSR_NAMESPACE_MASK |
        carbon_arch_pkg::CARBON_FEAT_FABRIC_MASK |
        carbon_arch_pkg::CARBON_FEAT_CPUID_MASK |
        carbon_arch_pkg::CARBON_Z480_NATIVE_64_MASK,
    parameter logic [31:0] FPU_FEAT_WORD0 = 32'h0,
    parameter logic [31:0] PERIPH_FEAT_WORD0 = 32'h0,
    parameter int unsigned CORE_COUNT = 1,
    parameter int unsigned VECTOR_BITS = 0
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
  localparam int unsigned BYTES_PER_WORD = (FAB_DATA_W / 8);
  localparam int unsigned IRQ_VEC_W = $bits(irq.irq_vector);

  localparam logic [FAB_ATTR_W-1:0] MEM_ATTR =
      FAB_ATTR_W'(CARBON_MEM_ATTR_CACHEABLE_MASK);
  localparam logic [FAB_ATTR_W-1:0] IO_ATTR =
      FAB_ATTR_W'(CARBON_MEM_ATTR_ORDERED_MASK | CARBON_MEM_ATTR_IO_SPACE_MASK);

  // --------------------------------------------------------------------------
  // Z480-specific CSR addresses (implementation-defined).
  // --------------------------------------------------------------------------
  localparam logic [31:0] Z480_CSR_PRIV        = 32'h00a40000;
  localparam logic [31:0] Z480_CSR_TRAP_U_LO   = 32'h00a40010;
  localparam logic [31:0] Z480_CSR_TRAP_U_HI   = 32'h00a40014;
  localparam logic [31:0] Z480_CSR_TRAP_S_LO   = 32'h00a40018;
  localparam logic [31:0] Z480_CSR_TRAP_S_HI   = 32'h00a4001c;
  localparam logic [31:0] Z480_CSR_TRAP_H_LO   = 32'h00a40020;
  localparam logic [31:0] Z480_CSR_TRAP_H_HI   = 32'h00a40024;
  localparam logic [31:0] Z480_CSR_BADADDR_LO  = 32'h00a40028;
  localparam logic [31:0] Z480_CSR_BADADDR_HI  = 32'h00a4002c;
  localparam logic [31:0] Z480_CSR_MMU_CTRL    = 32'h00a40030;
  localparam logic [31:0] Z480_CSR_MMU_ROOT_LO = 32'h00a40034;
  localparam logic [31:0] Z480_CSR_MMU_ROOT_HI = 32'h00a40038;
  localparam logic [31:0] Z480_CSR_MMU_ASID    = 32'h00a4003c;
  localparam logic [31:0] Z480_CSR_MMU_VMID    = 32'h00a40040;
  localparam logic [31:0] Z480_CSR_CACHE_OP       = 32'h00a40044;
  localparam logic [31:0] Z480_CSR_CACHE_ADDR_LO  = 32'h00a40048;
  localparam logic [31:0] Z480_CSR_CACHE_ADDR_HI  = 32'h00a4004c;
  localparam logic [31:0] Z480_CSR_CACHE_LEN      = 32'h00a40050;
  localparam logic [31:0] Z480_CSR_CACHE_STATUS   = 32'h00a40054;

  // --------------------------------------------------------------------------
  // Trap causes (implementation-defined).
  // --------------------------------------------------------------------------
  localparam logic [31:0] Z480_CAUSE_ILLEGAL = 32'h0000_0001;
  localparam logic [31:0] Z480_CAUSE_BUS     = 32'h0000_0002;
  localparam logic [31:0] Z480_CAUSE_ALIGN   = 32'h0000_0003;
  localparam logic [31:0] Z480_CAUSE_CSR     = 32'h0000_0004;
  localparam logic [31:0] Z480_CAUSE_IRQ     = 32'h0000_0100;
  localparam logic [31:0] Z480_CAUSE_MODEUP_INVALID = 32'h0000_0012;

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
  logic [31:0] csr_ie_q;
  logic [31:0] csr_ip_q;
  logic [63:0] csr_trap_u_q;
  logic [63:0] csr_trap_s_q;
  logic [63:0] csr_trap_h_q;
  logic [63:0] csr_badaddr_q;
  logic [31:0] mmu_ctrl_q;
  logic [63:0] mmu_root_q;
  logic [31:0] mmu_asid_q;
  logic [31:0] mmu_vmid_q;
  logic [31:0] cache_op_q;
  logic [63:0] cache_addr_q;
  logic [31:0] cache_len_q;
  logic [31:0] cache_status_q;
  z480_priv_e priv_q;
  z480_priv_e prev_priv_q;

  // Debug pulses
  logic csr_halt_pulse_q;
  logic csr_run_pulse_q;
  logic csr_step_pulse_q;

  // Core-originated trap update
  logic        core_trap_pulse_q;
  logic [31:0] core_trap_cause_q;
  logic [31:0] core_trap_epc_q;
  logic [63:0] core_trap_badaddr_q;

  // Core-originated CSR write (for CSRW)
  logic        core_csr_write_pulse_q;
  logic [31:0] core_csr_write_addr_q;
  logic [31:0] core_csr_write_data_q;
  logic        irq_ack_q;
  logic [IRQ_VEC_W-1:0] irq_ack_vector_q;

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
  wire csr_priv_write_pulse =
      csr_req_fire && csr.req_write && (csr.req_addr == Z480_CSR_PRIV);
  wire [1:0] csr_priv_write_data = csr.req_wdata[1:0];

  // CPUID leaf implementation
  logic [63:0] cpuid_data0;
  logic [63:0] cpuid_data1;
  logic [63:0] cpuid_data2;
  logic [63:0] cpuid_data3;

  cpuid_block #(
      .CORE_COUNT(CORE_COUNT),
      .VECTOR_BITS(VECTOR_BITS),
      .DISCOVERY_PTR(DISCOVERY_PTR),
      .BDT_PTR(BDT_PTR),
      .BDT_ENTRY_COUNT(BDT_ENTRY_COUNT),
      .TOPOLOGY_PTR(TOPOLOGY_PTR),
      .CPU_FEAT_WORD0(CPU_FEAT_WORD0),
      .FPU_FEAT_WORD0(FPU_FEAT_WORD0),
      .PERIPH_FEAT_WORD0(PERIPH_FEAT_WORD0)
  ) u_cpuid (
      .leaf(csr_cpuid_leaf_q),
      .subleaf(csr_cpuid_subleaf_q),
      .data0(cpuid_data0),
      .data1(cpuid_data1),
      .data2(cpuid_data2),
      .data3(cpuid_data3)
  );

  function automatic logic [31:0] csr_read_word(
      input logic [31:0] addr,
      output logic fault
  );
    logic [31:0] v;
    begin
      v = 32'h0;
      fault = 1'b0;
      unique case (addr)
        CARBON_CSR_ID: v = 32'h5A34_8001;
        CARBON_CSR_TIER: v[7:0] = csr_tier_q;
        CARBON_CSR_MODEFLAGS: v[7:0] = csr_modeflags_q;
        CARBON_CSR_TIME: v = cycle_q[31:0];
        CARBON_CSR_TIME_HI: v = cycle_q[63:32];
        CARBON_CSR_CAUSE: v = csr_cause_q;
        CARBON_CSR_EPC: v = csr_epc_q;
        CARBON_CSR_IE: v = csr_ie_q;
        CARBON_CSR_IP: v = csr_ip_q;
        CARBON_CSR_TRACE_CTL: v = csr_trace_ctl_q;
        CARBON_CSR_CPUID_LEAF: v = csr_cpuid_leaf_q;
        CARBON_CSR_CPUID_SUBLEAF: v = csr_cpuid_subleaf_q;
        CARBON_CSR_CPUID_DATA0_LO: v = cpuid_data0[31:0];
        CARBON_CSR_CPUID_DATA0_HI: v = cpuid_data0[63:32];
        CARBON_CSR_CPUID_DATA1_LO: v = cpuid_data1[31:0];
        CARBON_CSR_CPUID_DATA1_HI: v = cpuid_data1[63:32];
        CARBON_CSR_CPUID_DATA2_LO: v = cpuid_data2[31:0];
        CARBON_CSR_CPUID_DATA2_HI: v = cpuid_data2[63:32];
        CARBON_CSR_CPUID_DATA3_LO: v = cpuid_data3[31:0];
        CARBON_CSR_CPUID_DATA3_HI: v = cpuid_data3[63:32];
        Z480_CSR_PRIV: v[1:0] = priv_q;
        Z480_CSR_TRAP_U_LO: v = csr_trap_u_q[31:0];
        Z480_CSR_TRAP_U_HI: v = csr_trap_u_q[63:32];
        Z480_CSR_TRAP_S_LO: v = csr_trap_s_q[31:0];
        Z480_CSR_TRAP_S_HI: v = csr_trap_s_q[63:32];
        Z480_CSR_TRAP_H_LO: v = csr_trap_h_q[31:0];
        Z480_CSR_TRAP_H_HI: v = csr_trap_h_q[63:32];
        Z480_CSR_BADADDR_LO: v = csr_badaddr_q[31:0];
        Z480_CSR_BADADDR_HI: v = csr_badaddr_q[63:32];
        Z480_CSR_MMU_CTRL: v = mmu_ctrl_q;
        Z480_CSR_MMU_ROOT_LO: v = mmu_root_q[31:0];
        Z480_CSR_MMU_ROOT_HI: v = mmu_root_q[63:32];
        Z480_CSR_MMU_ASID: v = mmu_asid_q;
        Z480_CSR_MMU_VMID: v = mmu_vmid_q;
        Z480_CSR_CACHE_OP: v = cache_op_q;
        Z480_CSR_CACHE_ADDR_LO: v = cache_addr_q[31:0];
        Z480_CSR_CACHE_ADDR_HI: v = cache_addr_q[63:32];
        Z480_CSR_CACHE_LEN: v = cache_len_q;
        Z480_CSR_CACHE_STATUS: v = cache_status_q;
        default: begin
          fault = 1'b1;
          v = 32'h0;
        end
      endcase
      csr_read_word = v;
    end
  endfunction

  function automatic logic csr_write_ok(
      input logic [31:0] addr,
      input z480_priv_e priv
  );
    begin
      unique case (addr)
        CARBON_CSR_MODEFLAGS,
        CARBON_CSR_EPC,
        CARBON_CSR_IE,
        CARBON_CSR_CPUID_LEAF,
        CARBON_CSR_CPUID_SUBLEAF,
        CARBON_CSR_TRACE_CTL: csr_write_ok = 1'b1;
        Z480_CSR_TRAP_U_LO,
        Z480_CSR_TRAP_U_HI,
        Z480_CSR_TRAP_S_LO,
        Z480_CSR_TRAP_S_HI,
        Z480_CSR_TRAP_H_LO,
        Z480_CSR_TRAP_H_HI,
        Z480_CSR_BADADDR_LO,
        Z480_CSR_BADADDR_HI,
        Z480_CSR_MMU_CTRL,
        Z480_CSR_MMU_ROOT_LO,
        Z480_CSR_MMU_ROOT_HI,
        Z480_CSR_MMU_ASID,
        Z480_CSR_MMU_VMID,
        Z480_CSR_CACHE_OP,
        Z480_CSR_CACHE_ADDR_LO,
        Z480_CSR_CACHE_ADDR_HI,
        Z480_CSR_CACHE_LEN: csr_write_ok = (priv == Z480_PRIV_H);
        default: csr_write_ok = 1'b0;
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
      csr_ie_q <= 32'h0;
      csr_ip_q <= 32'h0;
      csr_trap_u_q <= 64'h0;
      csr_trap_s_q <= 64'h0;
      csr_trap_h_q <= 64'h0;
      csr_badaddr_q <= 64'h0;
      mmu_ctrl_q <= 32'h0;
      mmu_root_q <= 64'h0;
      mmu_asid_q <= 32'h0;
      mmu_vmid_q <= 32'h0;
      cache_op_q <= 32'h0;
      cache_addr_q <= 64'h0;
      cache_len_q <= 32'h0;
      cache_status_q <= 32'h0;
      csr_modeflags_q <= CARBON_MODEFLAG_STRICT_MASK;
      csr_tier_q <= 8'(CARBON_Z80_DERIVED_TIER_P7_Z480);
      csr_halt_pulse_q <= 1'b0;
      csr_run_pulse_q  <= 1'b0;
      csr_step_pulse_q <= 1'b0;
    end else begin
      cycle_q <= cycle_q + 64'd1;
      csr_ip_q <= 32'(irq.irq_pending);
      csr_halt_pulse_q <= 1'b0;
      csr_run_pulse_q  <= 1'b0;
      csr_step_pulse_q <= 1'b0;

      if (csr_rsp_fire) csr_rsp_valid_q <= 1'b0;

      if (core_trap_pulse_q) begin
        csr_cause_q <= core_trap_cause_q;
        csr_epc_q   <= core_trap_epc_q;
        csr_badaddr_q <= core_trap_badaddr_q;
      end

      if (csr_modeflags_wr) csr_modeflags_q <= csr_modeflags_wdata;

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
            if (!csr.req_write) csr_rsp_rdata_q <= csr_ie_q;
            else begin
              csr_ie_q <= csr.req_wdata;
              csr_rsp_side_q <= 1'b1;
            end
          end
          CARBON_CSR_IP: begin
            if (!csr.req_write) csr_rsp_rdata_q <= csr_ip_q;
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
          Z480_CSR_PRIV: begin
            if (!csr.req_write) begin
              csr_rsp_rdata_q[1:0] <= priv_q;
            end else if (priv_q == Z480_PRIV_H) begin
              csr_rsp_side_q <= 1'b1;
            end else begin
              csr_rsp_fault_q <= 1'b1;
            end
          end
          Z480_CSR_TRAP_U_LO: begin
            if (!csr.req_write) csr_rsp_rdata_q <= csr_trap_u_q[31:0];
            else if (priv_q == Z480_PRIV_H) begin
              csr_trap_u_q[31:0] <= csr.req_wdata;
              csr_rsp_side_q <= 1'b1;
            end else csr_rsp_fault_q <= 1'b1;
          end
          Z480_CSR_TRAP_U_HI: begin
            if (!csr.req_write) csr_rsp_rdata_q <= csr_trap_u_q[63:32];
            else if (priv_q == Z480_PRIV_H) begin
              csr_trap_u_q[63:32] <= csr.req_wdata;
              csr_rsp_side_q <= 1'b1;
            end else csr_rsp_fault_q <= 1'b1;
          end
          Z480_CSR_TRAP_S_LO: begin
            if (!csr.req_write) csr_rsp_rdata_q <= csr_trap_s_q[31:0];
            else if (priv_q == Z480_PRIV_H) begin
              csr_trap_s_q[31:0] <= csr.req_wdata;
              csr_rsp_side_q <= 1'b1;
            end else csr_rsp_fault_q <= 1'b1;
          end
          Z480_CSR_TRAP_S_HI: begin
            if (!csr.req_write) csr_rsp_rdata_q <= csr_trap_s_q[63:32];
            else if (priv_q == Z480_PRIV_H) begin
              csr_trap_s_q[63:32] <= csr.req_wdata;
              csr_rsp_side_q <= 1'b1;
            end else csr_rsp_fault_q <= 1'b1;
          end
          Z480_CSR_TRAP_H_LO: begin
            if (!csr.req_write) csr_rsp_rdata_q <= csr_trap_h_q[31:0];
            else if (priv_q == Z480_PRIV_H) begin
              csr_trap_h_q[31:0] <= csr.req_wdata;
              csr_rsp_side_q <= 1'b1;
            end else csr_rsp_fault_q <= 1'b1;
          end
          Z480_CSR_TRAP_H_HI: begin
            if (!csr.req_write) csr_rsp_rdata_q <= csr_trap_h_q[63:32];
            else if (priv_q == Z480_PRIV_H) begin
              csr_trap_h_q[63:32] <= csr.req_wdata;
              csr_rsp_side_q <= 1'b1;
            end else csr_rsp_fault_q <= 1'b1;
          end
          Z480_CSR_BADADDR_LO: begin
            if (!csr.req_write) csr_rsp_rdata_q <= csr_badaddr_q[31:0];
            else if (priv_q == Z480_PRIV_H) begin
              csr_badaddr_q[31:0] <= csr.req_wdata;
              csr_rsp_side_q <= 1'b1;
            end else csr_rsp_fault_q <= 1'b1;
          end
          Z480_CSR_BADADDR_HI: begin
            if (!csr.req_write) csr_rsp_rdata_q <= csr_badaddr_q[63:32];
            else if (priv_q == Z480_PRIV_H) begin
              csr_badaddr_q[63:32] <= csr.req_wdata;
              csr_rsp_side_q <= 1'b1;
            end else csr_rsp_fault_q <= 1'b1;
          end
          Z480_CSR_MMU_CTRL: begin
            if (!csr.req_write) csr_rsp_rdata_q <= mmu_ctrl_q;
            else if (priv_q == Z480_PRIV_H) begin
              mmu_ctrl_q <= csr.req_wdata;
              csr_rsp_side_q <= 1'b1;
            end else csr_rsp_fault_q <= 1'b1;
          end
          Z480_CSR_MMU_ROOT_LO: begin
            if (!csr.req_write) csr_rsp_rdata_q <= mmu_root_q[31:0];
            else if (priv_q == Z480_PRIV_H) begin
              mmu_root_q[31:0] <= csr.req_wdata;
              csr_rsp_side_q <= 1'b1;
            end else csr_rsp_fault_q <= 1'b1;
          end
          Z480_CSR_MMU_ROOT_HI: begin
            if (!csr.req_write) csr_rsp_rdata_q <= mmu_root_q[63:32];
            else if (priv_q == Z480_PRIV_H) begin
              mmu_root_q[63:32] <= csr.req_wdata;
              csr_rsp_side_q <= 1'b1;
            end else csr_rsp_fault_q <= 1'b1;
          end
          Z480_CSR_MMU_ASID: begin
            if (!csr.req_write) csr_rsp_rdata_q <= mmu_asid_q;
            else if (priv_q == Z480_PRIV_H) begin
              mmu_asid_q <= csr.req_wdata;
              csr_rsp_side_q <= 1'b1;
            end else csr_rsp_fault_q <= 1'b1;
          end
          Z480_CSR_MMU_VMID: begin
            if (!csr.req_write) csr_rsp_rdata_q <= mmu_vmid_q;
            else if (priv_q == Z480_PRIV_H) begin
              mmu_vmid_q <= csr.req_wdata;
              csr_rsp_side_q <= 1'b1;
            end else csr_rsp_fault_q <= 1'b1;
          end
          Z480_CSR_CACHE_OP: begin
            if (!csr.req_write) csr_rsp_rdata_q <= cache_op_q;
            else if (priv_q == Z480_PRIV_H) begin
              cache_op_q <= csr.req_wdata;
              cache_status_q <= 32'h0;
              csr_rsp_side_q <= 1'b1;
            end else csr_rsp_fault_q <= 1'b1;
          end
          Z480_CSR_CACHE_ADDR_LO: begin
            if (!csr.req_write) csr_rsp_rdata_q <= cache_addr_q[31:0];
            else if (priv_q == Z480_PRIV_H) begin
              cache_addr_q[31:0] <= csr.req_wdata;
              csr_rsp_side_q <= 1'b1;
            end else csr_rsp_fault_q <= 1'b1;
          end
          Z480_CSR_CACHE_ADDR_HI: begin
            if (!csr.req_write) csr_rsp_rdata_q <= cache_addr_q[63:32];
            else if (priv_q == Z480_PRIV_H) begin
              cache_addr_q[63:32] <= csr.req_wdata;
              csr_rsp_side_q <= 1'b1;
            end else csr_rsp_fault_q <= 1'b1;
          end
          Z480_CSR_CACHE_LEN: begin
            if (!csr.req_write) csr_rsp_rdata_q <= cache_len_q;
            else if (priv_q == Z480_PRIV_H) begin
              cache_len_q <= csr.req_wdata;
              csr_rsp_side_q <= 1'b1;
            end else csr_rsp_fault_q <= 1'b1;
          end
          Z480_CSR_CACHE_STATUS: begin
            if (!csr.req_write) csr_rsp_rdata_q <= cache_status_q;
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
              csr_rsp_rdata_q[0] <= dbg_halted_q;
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

      if (core_csr_write_pulse_q) begin
        unique case (core_csr_write_addr_q)
          CARBON_CSR_MODEFLAGS: csr_modeflags_q <=
              core_csr_write_data_q[7:0] &
              (CARBON_MODEFLAG_STRICT_MASK | CARBON_MODEFLAG_INTMASK_MASK);
          CARBON_CSR_EPC: csr_epc_q <= core_csr_write_data_q;
          CARBON_CSR_IE: csr_ie_q <= core_csr_write_data_q;
          CARBON_CSR_CPUID_LEAF: csr_cpuid_leaf_q <= core_csr_write_data_q;
          CARBON_CSR_CPUID_SUBLEAF: csr_cpuid_subleaf_q <= core_csr_write_data_q;
          CARBON_CSR_TRACE_CTL: csr_trace_ctl_q <= core_csr_write_data_q;
          Z480_CSR_TRAP_U_LO: csr_trap_u_q[31:0] <= core_csr_write_data_q;
          Z480_CSR_TRAP_U_HI: csr_trap_u_q[63:32] <= core_csr_write_data_q;
          Z480_CSR_TRAP_S_LO: csr_trap_s_q[31:0] <= core_csr_write_data_q;
          Z480_CSR_TRAP_S_HI: csr_trap_s_q[63:32] <= core_csr_write_data_q;
          Z480_CSR_TRAP_H_LO: csr_trap_h_q[31:0] <= core_csr_write_data_q;
          Z480_CSR_TRAP_H_HI: csr_trap_h_q[63:32] <= core_csr_write_data_q;
          Z480_CSR_BADADDR_LO: csr_badaddr_q[31:0] <= core_csr_write_data_q;
          Z480_CSR_BADADDR_HI: csr_badaddr_q[63:32] <= core_csr_write_data_q;
          Z480_CSR_MMU_CTRL: mmu_ctrl_q <= core_csr_write_data_q;
          Z480_CSR_MMU_ROOT_LO: mmu_root_q[31:0] <= core_csr_write_data_q;
          Z480_CSR_MMU_ROOT_HI: mmu_root_q[63:32] <= core_csr_write_data_q;
          Z480_CSR_MMU_ASID: mmu_asid_q <= core_csr_write_data_q;
          Z480_CSR_MMU_VMID: mmu_vmid_q <= core_csr_write_data_q;
          Z480_CSR_CACHE_OP: begin
            cache_op_q <= core_csr_write_data_q;
            cache_status_q <= 32'h0;
          end
          Z480_CSR_CACHE_ADDR_LO: cache_addr_q[31:0] <= core_csr_write_data_q;
          Z480_CSR_CACHE_ADDR_HI: cache_addr_q[63:32] <= core_csr_write_data_q;
          Z480_CSR_CACHE_LEN: cache_len_q <= core_csr_write_data_q;
          default: begin end
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

  assign dbg.halt_ack = dbg_halted_q;
  assign dbg.step_ack = dbg_step_ack_q;
  assign dbg.bp_ready = 1'b0;
  assign dbg.trace_valid = 1'b0;
  assign dbg.trace_data  = '0;

  // --------------------------------------------------------------------------
  // Simple in-order pipeline (single outstanding fabric op).
  // --------------------------------------------------------------------------
  typedef enum logic [3:0] {
    ST_RESET,
    ST_BOUNDARY,
    ST_BUS_REQ,
    ST_BUS_RSP,
    ST_DECODE,
    ST_MEM_LOAD_HI,
    ST_MEM_STORE_HI,
    ST_MEM_COMMIT,
    ST_TRAP
  } state_e;

  typedef enum logic [1:0] {
    DEST_NONE,
    DEST_INSTR,
    DEST_LOAD_LO,
    DEST_LOAD_HI
  } dest_e;

  state_e state_q;
  state_e state_after_bus_q;
  dest_e  bus_dest_q;

  logic [63:0] pc_q;
  logic [63:0] instr_pc_q;
  logic [31:0] instr_q;

  // Register file
  logic [63:0] gpr_q [0:31];

  // Load/store context
  logic [63:0] load_addr_q;
  logic [3:0]  load_size_q;
  logic        load_sign_q;
  logic [4:0]  load_rd_q;
  logic [31:0] load_data_lo_q;
  logic [31:0] load_data_hi_q;

  logic [63:0] store_addr_q;
  logic [3:0]  store_size_q;
  logic [63:0] store_data_q;

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
  wire irq_masked = csr_modeflags_q[CARBON_MODEFLAG_INTMASK_BIT];
  wire irq_enable = irq.irq_valid ? csr_ie_q[irq.irq_vector] : 1'b0;
  wire irq_take = irq.irq_valid && !irq_masked && irq_enable;

  function automatic logic [FAB_SIZE_W-1:0] size_to_code(input int unsigned size_bytes);
    begin
      unique case (size_bytes)
        1: size_to_code = FAB_SIZE_W'(0);
        2: size_to_code = FAB_SIZE_W'(1);
        4: size_to_code = FAB_SIZE_W'(2);
        8: size_to_code = FAB_SIZE_W'(3);
        default: size_to_code = FAB_SIZE_W'(0);
      endcase
    end
  endfunction

  function automatic logic [FAB_STRB_W-1:0] wstrb_for_size(input int unsigned size_bytes);
    begin
      unique case (size_bytes)
        1: wstrb_for_size = FAB_STRB_W'(1);
        2: wstrb_for_size = FAB_STRB_W'(3);
        4: wstrb_for_size = FAB_STRB_W'(15);
        default: wstrb_for_size = FAB_STRB_W'(0);
      endcase
    end
  endfunction

  function automatic logic is_io_addr(input logic [63:0] addr);
    logic [31:0] lo;
    begin
      lo = addr[31:0];
      is_io_addr = ((lo & IO_MASK) == IO_BASE);
    end
  endfunction

  function automatic z480_priv_e trap_target_priv(input z480_priv_e cur_priv);
    begin
      if (cur_priv == Z480_PRIV_U) trap_target_priv = Z480_PRIV_S;
      else trap_target_priv = Z480_PRIV_H;
    end
  endfunction

  function automatic logic [63:0] trap_base_for(input z480_priv_e target);
    begin
      unique case (target)
        Z480_PRIV_U: trap_base_for = csr_trap_u_q;
        Z480_PRIV_S: trap_base_for = csr_trap_s_q;
        default: trap_base_for = csr_trap_h_q;
      endcase
    end
  endfunction

  task automatic enter_trap(
      input logic [31:0] cause,
      input logic [63:0] epc,
      input logic [63:0] badaddr,
      input logic is_irq,
      input logic [IRQ_VEC_W-1:0] irq_vec
  );
    z480_priv_e target_priv;
    logic [63:0] base;
    logic [63:0] vector_off;
    begin
      target_priv = trap_target_priv(priv_q);
      base = trap_base_for(target_priv);
      vector_off = 64'h0;
      if (is_irq) vector_off = ({{(64-IRQ_VEC_W){1'b0}}, irq_vec} << 2);
      prev_priv_q <= priv_q;
      priv_q <= target_priv;
      pc_q <= base + vector_off;
      core_trap_pulse_q <= 1'b1;
      core_trap_cause_q <= cause;
      core_trap_epc_q <= epc[31:0];
      core_trap_badaddr_q <= badaddr;
      state_q <= ST_BOUNDARY;
    end
  endtask

  task automatic start_bus_read(
      input logic [63:0] addr,
      input int unsigned size_bytes,
      input dest_e dest,
      input state_e next_state
  );
    begin
      bus_op_q <= FAB_OP_W'(CARBON_FABRIC_XACT_READ);
      bus_addr_q <= FAB_ADDR_W'(addr[FAB_ADDR_W-1:0]);
      bus_wdata_q <= '0;
      bus_wstrb_q <= '0;
      bus_size_q <= size_to_code(size_bytes);
      bus_attr_q <= is_io_addr(addr) ? IO_ATTR : MEM_ATTR;
      bus_dest_q <= dest;
      state_after_bus_q <= next_state;
      state_q <= ST_BUS_REQ;
    end
  endtask

  task automatic start_bus_write(
      input logic [63:0] addr,
      input logic [FAB_DATA_W-1:0] data,
      input logic [FAB_STRB_W-1:0] wstrb,
      input int unsigned size_bytes,
      input state_e next_state
  );
    begin
      bus_op_q <= FAB_OP_W'(CARBON_FABRIC_XACT_WRITE);
      bus_addr_q <= FAB_ADDR_W'(addr[FAB_ADDR_W-1:0]);
      bus_wdata_q <= data;
      bus_wstrb_q <= wstrb;
      bus_size_q <= size_to_code(size_bytes);
      bus_attr_q <= is_io_addr(addr) ? IO_ATTR : MEM_ATTR;
      bus_dest_q <= DEST_NONE;
      state_after_bus_q <= next_state;
      state_q <= ST_BUS_REQ;
    end
  endtask

  task automatic write_gpr(input logic [4:0] rd, input logic [63:0] value);
    begin
      if (rd != 5'd0) gpr_q[rd] <= value;
    end
  endtask

  wire [5:0] op = instr_q[31:26];
  wire [4:0] rs = instr_q[25:21];
  wire [4:0] rt = instr_q[20:16];
  wire [4:0] rd = instr_q[15:11];
  wire [5:0] funct = instr_q[5:0];
  wire [15:0] imm16 = instr_q[15:0];
  wire signed [15:0] simm16 = instr_q[15:0];
  wire [25:0] imm26 = instr_q[25:0];

  // --------------------------------------------------------------------------
  // Core FSM
  // --------------------------------------------------------------------------
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      int i;
      state_q <= ST_RESET;
      state_after_bus_q <= ST_BOUNDARY;
      bus_dest_q <= DEST_NONE;
      pc_q <= RESET_PC;
      instr_pc_q <= RESET_PC;
      instr_q <= 32'h0;
      priv_q <= Z480_PRIV_H;
      prev_priv_q <= Z480_PRIV_H;

      for (i = 0; i < 32; i++) begin
        gpr_q[i] <= 64'h0;
      end

      load_addr_q <= '0;
      load_size_q <= '0;
      load_sign_q <= 1'b0;
      load_rd_q <= '0;
      load_data_lo_q <= '0;
      load_data_hi_q <= '0;

      store_addr_q <= '0;
      store_size_q <= '0;
      store_data_q <= '0;

      dbg_halted_q <= 1'b0;
      dbg_step_pending_q <= 1'b0;
      dbg_step_inflight_q <= 1'b0;
      dbg_step_ack_q <= 1'b0;

      core_trap_pulse_q <= 1'b0;
      core_trap_cause_q <= '0;
      core_trap_epc_q   <= '0;
      core_trap_badaddr_q <= 64'h0;

      core_csr_write_pulse_q <= 1'b0;
      core_csr_write_addr_q <= '0;
      core_csr_write_data_q <= '0;
      irq_ack_q <= 1'b0;
      irq_ack_vector_q <= '0;

      bus_op_q <= '0;
      bus_addr_q <= '0;
      bus_wdata_q <= '0;
      bus_wstrb_q <= '0;
      bus_size_q <= '0;
      bus_attr_q <= '0;
    end else begin
      dbg_step_ack_q <= 1'b0;
      core_trap_pulse_q <= 1'b0;
      core_csr_write_pulse_q <= 1'b0;
      irq_ack_q <= 1'b0;
      irq_ack_vector_q <= '0;

      if (csr_priv_write_pulse && (priv_q == Z480_PRIV_H)) begin
        priv_q <= z480_priv_e'(csr_priv_write_data);
      end

      gpr_q[0] <= 64'h0;

      unique case (state_q)
        ST_RESET: begin
          pc_q <= RESET_PC;
          state_q <= ST_BOUNDARY;
        end

        ST_TRAP: begin
          state_q <= ST_BOUNDARY;
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

          if (dbg_halted_q && !dbg_step_pending_q) begin
            state_q <= ST_BOUNDARY;
          end else begin
            if (dbg_halted_q && dbg_step_pending_q) begin
              dbg_step_pending_q <= 1'b0;
              dbg_step_inflight_q <= 1'b1;
            end

            if (irq_take) begin
              irq_ack_q <= 1'b1;
              irq_ack_vector_q <= irq.irq_vector;
              enter_trap(Z480_CAUSE_IRQ |
                             {{(32-IRQ_VEC_W){1'b0}}, irq.irq_vector},
                         pc_q, 64'h0, 1'b1, irq.irq_vector);
            end else if (pc_q[1:0] != 2'b00) begin
              enter_trap(Z480_CAUSE_ALIGN, pc_q, pc_q, 1'b0, '0);
            end else begin
              start_bus_read(pc_q, 4, DEST_INSTR, ST_DECODE);
            end
          end
        end

        ST_BUS_REQ: begin
          if (req_fire) state_q <= ST_BUS_RSP;
        end

        ST_BUS_RSP: begin
          if (rsp_fire) begin
            if (mem_if.rsp_code != FAB_CODE_W'(CARBON_FABRIC_RESP_OK)) begin
              logic [31:0] fault_epc;
              fault_epc = (bus_dest_q == DEST_INSTR) ? pc_q[31:0] : instr_pc_q[31:0];
              enter_trap(Z480_CAUSE_BUS,
                         {32'h0, fault_epc},
                         {{(64-FAB_ADDR_W){1'b0}}, bus_addr_q},
                         1'b0,
                         '0);
            end else begin
              unique case (bus_dest_q)
                DEST_INSTR: begin
                  instr_pc_q <= pc_q;
                  instr_q <= mem_if.rsp_rdata[31:0];
                  pc_q <= pc_q + 64'd4;
                end
                DEST_LOAD_LO: begin
                  load_data_lo_q <= mem_if.rsp_rdata[31:0];
                end
                DEST_LOAD_HI: begin
                  load_data_hi_q <= mem_if.rsp_rdata[31:0];
                end
                default: begin end
              endcase
              state_q <= state_after_bus_q;
            end
          end
        end

        ST_DECODE: begin
          logic [63:0] rs_val;
          logic [63:0] rt_val;
          logic [63:0] result;
          logic [63:0] addr;
          logic csr_fault;
          logic [31:0] csr_rdata;
          logic [31:0] csr_addr;

          rs_val = gpr_q[rs];
          rt_val = gpr_q[rt];
          result = 64'h0;
          addr = rs_val + {{48{simm16[15]}}, simm16};
          csr_fault = 1'b0;
          csr_rdata = 32'h0;
          csr_addr = rs_val[31:0] + {{16{simm16[15]}}, simm16};

          unique case (op)
            Z480_OP_SPECIAL: begin
              unique case (funct)
                Z480_FUNCT_NOP: begin
                  state_q <= ST_BOUNDARY;
                end
                Z480_FUNCT_ADD: begin
                  result = rs_val + rt_val;
                  write_gpr(rd, result);
                  state_q <= ST_BOUNDARY;
                end
                Z480_FUNCT_SUB: begin
                  result = rs_val - rt_val;
                  write_gpr(rd, result);
                  state_q <= ST_BOUNDARY;
                end
                Z480_FUNCT_AND: begin
                  result = rs_val & rt_val;
                  write_gpr(rd, result);
                  state_q <= ST_BOUNDARY;
                end
                Z480_FUNCT_OR: begin
                  result = rs_val | rt_val;
                  write_gpr(rd, result);
                  state_q <= ST_BOUNDARY;
                end
                Z480_FUNCT_XOR: begin
                  result = rs_val ^ rt_val;
                  write_gpr(rd, result);
                  state_q <= ST_BOUNDARY;
                end
                Z480_FUNCT_JR: begin
                  pc_q <= rs_val;
                  state_q <= ST_BOUNDARY;
                end
                default: begin
                  enter_trap(Z480_CAUSE_ILLEGAL, instr_pc_q, 64'h0, 1'b0, '0);
                end
              endcase
            end
            Z480_OP_ADDI: begin
              result = rs_val + {{48{simm16[15]}}, simm16};
              write_gpr(rt, result);
              state_q <= ST_BOUNDARY;
            end
            Z480_OP_BEQ: begin
              if (rs_val == rt_val) begin
                pc_q <= pc_q + ({{48{simm16[15]}}, simm16} << 2);
              end
              state_q <= ST_BOUNDARY;
            end
            Z480_OP_BNE: begin
              if (rs_val != rt_val) begin
                pc_q <= pc_q + ({{48{simm16[15]}}, simm16} << 2);
              end
              state_q <= ST_BOUNDARY;
            end
            Z480_OP_J: begin
              pc_q <= {pc_q[63:28], imm26, 2'b00};
              state_q <= ST_BOUNDARY;
            end
            Z480_OP_JAL: begin
              write_gpr(5'd31, pc_q);
              pc_q <= {pc_q[63:28], imm26, 2'b00};
              state_q <= ST_BOUNDARY;
            end
            Z480_OP_LDB: begin
              load_addr_q <= addr;
              load_size_q <= 4'd1;
              load_sign_q <= 1'b1;
              load_rd_q <= rt;
              start_bus_read(addr, 1, DEST_LOAD_LO, ST_MEM_COMMIT);
            end
            Z480_OP_LDH: begin
              if (addr[0] != 1'b0) begin
                enter_trap(Z480_CAUSE_ALIGN, instr_pc_q, addr, 1'b0, '0);
              end else begin
                load_addr_q <= addr;
                load_size_q <= 4'd2;
                load_sign_q <= 1'b1;
                load_rd_q <= rt;
                start_bus_read(addr, 2, DEST_LOAD_LO, ST_MEM_COMMIT);
              end
            end
            Z480_OP_LDW: begin
              if (addr[1:0] != 2'b00) begin
                enter_trap(Z480_CAUSE_ALIGN, instr_pc_q, addr, 1'b0, '0);
              end else begin
                load_addr_q <= addr;
                load_size_q <= 4'd4;
                load_sign_q <= 1'b1;
                load_rd_q <= rt;
                start_bus_read(addr, 4, DEST_LOAD_LO, ST_MEM_COMMIT);
              end
            end
            Z480_OP_LDD: begin
              if (addr[1:0] != 2'b00) begin
                enter_trap(Z480_CAUSE_ALIGN, instr_pc_q, addr, 1'b0, '0);
              end else begin
                load_addr_q <= addr;
                load_size_q <= 4'd4;
                load_sign_q <= 1'b1;
                load_rd_q <= rt;
                start_bus_read(addr, 4, DEST_LOAD_LO, ST_MEM_COMMIT);
              end
            end
            Z480_OP_LDQ: begin
              if (addr[2:0] != 3'b000) begin
                enter_trap(Z480_CAUSE_ALIGN, instr_pc_q, addr, 1'b0, '0);
              end else begin
                load_addr_q <= addr;
                load_size_q <= 4'd8;
                load_sign_q <= 1'b0;
                load_rd_q <= rt;
                start_bus_read(addr, 4, DEST_LOAD_LO, ST_MEM_LOAD_HI);
              end
            end
            Z480_OP_STB: begin
              store_addr_q <= addr;
              store_size_q <= 4'd1;
              store_data_q <= rt_val;
              start_bus_write(addr, FAB_DATA_W'(rt_val[7:0]), wstrb_for_size(1), 1, ST_BOUNDARY);
            end
            Z480_OP_STH: begin
              if (addr[0] != 1'b0) begin
                enter_trap(Z480_CAUSE_ALIGN, instr_pc_q, addr, 1'b0, '0);
              end else begin
                store_addr_q <= addr;
                store_size_q <= 4'd2;
                store_data_q <= rt_val;
                start_bus_write(addr, FAB_DATA_W'(rt_val[15:0]), wstrb_for_size(2), 2, ST_BOUNDARY);
              end
            end
            Z480_OP_STW: begin
              if (addr[1:0] != 2'b00) begin
                enter_trap(Z480_CAUSE_ALIGN, instr_pc_q, addr, 1'b0, '0);
              end else begin
                store_addr_q <= addr;
                store_size_q <= 4'd4;
                store_data_q <= rt_val;
                start_bus_write(addr, FAB_DATA_W'(rt_val[31:0]), wstrb_for_size(4), 4, ST_BOUNDARY);
              end
            end
            Z480_OP_STD: begin
              if (addr[1:0] != 2'b00) begin
                enter_trap(Z480_CAUSE_ALIGN, instr_pc_q, addr, 1'b0, '0);
              end else begin
                store_addr_q <= addr;
                store_size_q <= 4'd4;
                store_data_q <= rt_val;
                start_bus_write(addr, FAB_DATA_W'(rt_val[31:0]), wstrb_for_size(4), 4, ST_BOUNDARY);
              end
            end
            Z480_OP_STQ: begin
              if (addr[2:0] != 3'b000) begin
                enter_trap(Z480_CAUSE_ALIGN, instr_pc_q, addr, 1'b0, '0);
              end else begin
                store_addr_q <= addr;
                store_size_q <= 4'd8;
                store_data_q <= rt_val;
                start_bus_write(addr, FAB_DATA_W'(rt_val[31:0]), wstrb_for_size(4), 4, ST_MEM_STORE_HI);
              end
            end
            Z480_OP_CSRR: begin
              csr_rdata = csr_read_word(csr_addr, csr_fault);
              if (csr_fault) begin
                enter_trap(Z480_CAUSE_CSR, instr_pc_q, 64'h0, 1'b0, '0);
              end else begin
                write_gpr(rt, {32'h0, csr_rdata});
                state_q <= ST_BOUNDARY;
              end
            end
            Z480_OP_CSRW: begin
              if (csr_addr == Z480_CSR_PRIV) begin
                if (priv_q == Z480_PRIV_H) begin
                  priv_q <= z480_priv_e'(rt_val[1:0]);
                  state_q <= ST_BOUNDARY;
                end else begin
                  enter_trap(Z480_CAUSE_CSR, instr_pc_q, 64'h0, 1'b0, '0);
                end
              end else if (csr_write_ok(csr_addr, priv_q)) begin
                core_csr_write_pulse_q <= 1'b1;
                core_csr_write_addr_q <= csr_addr;
                core_csr_write_data_q <= rt_val[31:0];
                state_q <= ST_BOUNDARY;
              end else begin
                enter_trap(Z480_CAUSE_CSR, instr_pc_q, 64'h0, 1'b0, '0);
              end
            end
            Z480_OP_FENCE,
            Z480_OP_FENCE_IO: begin
              state_q <= ST_BOUNDARY;
            end
            Z480_OP_MODEUP,
            Z480_OP_RETMD: begin
              enter_trap(Z480_CAUSE_MODEUP_INVALID, instr_pc_q, 64'h0, 1'b0, '0);
            end
            Z480_OP_RFE: begin
              pc_q <= {32'h0, csr_epc_q};
              priv_q <= prev_priv_q;
              state_q <= ST_BOUNDARY;
            end
            default: begin
              enter_trap(Z480_CAUSE_ILLEGAL, instr_pc_q, 64'h0, 1'b0, '0);
            end
          endcase
        end

        ST_MEM_LOAD_HI: begin
          start_bus_read(load_addr_q + 64'd4, 4, DEST_LOAD_HI, ST_MEM_COMMIT);
        end

        ST_MEM_STORE_HI: begin
          start_bus_write(store_addr_q + 64'd4,
                          FAB_DATA_W'(store_data_q[63:32]),
                          wstrb_for_size(4), 4, ST_BOUNDARY);
        end

        ST_MEM_COMMIT: begin
          logic [63:0] load_val;
          load_val = 64'h0;
          unique case (load_size_q)
            4'd1: begin
              if (load_sign_q) load_val = {{56{load_data_lo_q[7]}}, load_data_lo_q[7:0]};
              else load_val = {56'h0, load_data_lo_q[7:0]};
            end
            4'd2: begin
              if (load_sign_q) load_val = {{48{load_data_lo_q[15]}}, load_data_lo_q[15:0]};
              else load_val = {48'h0, load_data_lo_q[15:0]};
            end
            4'd4: begin
              if (load_sign_q) load_val = {{32{load_data_lo_q[31]}}, load_data_lo_q[31:0]};
              else load_val = {32'h0, load_data_lo_q[31:0]};
            end
            4'd8: begin
              load_val = {load_data_hi_q, load_data_lo_q};
            end
            default: begin
              load_val = 64'h0;
            end
          endcase
          write_gpr(load_rd_q, load_val);
          state_q <= ST_BOUNDARY;
        end

        default: begin
          enter_trap(Z480_CAUSE_ILLEGAL, instr_pc_q, 64'h0, 1'b0, '0);
        end
      endcase
    end
  end

  assign irq.irq_ack = irq_ack_q;
  assign irq.irq_ack_vector = irq_ack_vector_q;

  wire _unused = ^{mem_if.rsp_id, mem_if.req_attr, mem_if.req_id};

endmodule : z480_core
