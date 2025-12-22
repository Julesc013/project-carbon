// Project Carbon - Z480 P7 core scaffold
// z480_core: Modular OoO-ready core skeleton with CSR/CPUID/debug scaffolding.

module z480_core #(
    parameter int unsigned CORE_COUNT  = 1,
    parameter int unsigned VECTOR_BITS = 128,
    parameter int unsigned UOPQ_DEPTH  = 16,
    parameter int unsigned ROB_DEPTH   = 64
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

  localparam int unsigned CSR_ADDR_W = $bits(csr.req_addr);
  localparam int unsigned CSR_DATA_W = $bits(csr.req_wdata);
  localparam int unsigned CSR_PRIV_W = $bits(csr.req_priv);

  // --------------------------------------------------------------------------
  // External interfaces (fabric/irq) - v1 scaffolding keeps fabric idle
  // --------------------------------------------------------------------------
  assign mem_if.req_valid = 1'b0;
  assign mem_if.req_op    = FAB_OP_W'(CARBON_FABRIC_XACT_READ);
  assign mem_if.req_addr  = '0;
  assign mem_if.req_wdata = '0;
  assign mem_if.req_wstrb = '0;
  assign mem_if.req_size  = '0;
  assign mem_if.req_attr  = FAB_ATTR_W'(CARBON_FABRIC_ATTR_CACHEABLE_MASK);
  assign mem_if.req_id    = '0;
  assign mem_if.rsp_ready = 1'b1;

  // External IRQ interface (not yet implemented)
  assign irq.irq_ack = 1'b0;
  assign irq.irq_ack_vector = '0;

  // --------------------------------------------------------------------------
  // Core-global state
  // --------------------------------------------------------------------------
  logic [63:0] cycle_q;
  logic [7:0]  tier_q;
  logic [7:0]  modeflags_q;

  // CPUID CSR window selectors
  logic [31:0] cpuid_leaf_q;
  logic [31:0] cpuid_subleaf_q;
  logic [63:0] cpuid_d0, cpuid_d1, cpuid_d2, cpuid_d3;

  cpuid_block #(
      .CORE_COUNT(CORE_COUNT),
      .VECTOR_BITS(VECTOR_BITS)
  ) u_cpuid (
      .leaf(cpuid_leaf_q),
      .subleaf(cpuid_subleaf_q),
      .data0(cpuid_d0),
      .data1(cpuid_d1),
      .data2(cpuid_d2),
      .data3(cpuid_d3)
  );

  // --------------------------------------------------------------------------
  // Privilege/MMU/trap scaffolding blocks
  // --------------------------------------------------------------------------
  z480_priv_e priv_mode;
  logic [31:0] ie_q, ip_q;
  logic irq_any_pending;

  priv_ctrl #(.IRQ_N(32)) u_priv (
      .clk(clk),
      .rst_n(rst_n),

      .set_priv_valid(1'b0),
      .set_priv_mode(Z480_PRIV_S),
      .priv_mode(priv_mode),

      .tv_u_we(1'b0),
      .tv_u_wdata('0),
      .tv_u_base(),
      .tv_s_we(1'b0),
      .tv_s_wdata('0),
      .tv_s_base(),
      .tv_h_we(1'b0),
      .tv_h_wdata('0),
      .tv_h_base(),

      .ie_we(csr.req_valid && csr.req_ready && csr.req_write &&
             (csr.req_addr == CSR_ADDR_W'(CARBON_CSR_IE)) &&
             (csr.req_priv >= CSR_PRIV_W'(1))),
      .ie_wdata(csr.req_wdata[31:0]),
      .ie(ie_q),

      .irq_pending_in(irq.irq_pending[31:0]),
      .ip(ip_q),

      .irq_any_pending(irq_any_pending)
  );

  logic mmu_req_valid, mmu_req_ready, mmu_rsp_valid, mmu_rsp_ready, mmu_rsp_fault;
  logic [63:0] mmu_req_vaddr, mmu_rsp_paddr;
  logic [2:0]  mmu_req_access;
  logic [63:0] mmu_pt_base;
  logic [15:0] mmu_asid, mmu_vmid;

  mmu u_mmu (
      .clk(clk),
      .rst_n(rst_n),
      .pt_base_we(1'b0),
      .pt_base_wdata('0),
      .pt_base(mmu_pt_base),
      .asid_we(1'b0),
      .asid_wdata('0),
      .asid(mmu_asid),
      .vmid_we(1'b0),
      .vmid_wdata('0),
      .vmid(mmu_vmid),
      .req_valid(mmu_req_valid),
      .req_vaddr(mmu_req_vaddr),
      .req_access(mmu_req_access),
      .req_ready(mmu_req_ready),
      .rsp_valid(mmu_rsp_valid),
      .rsp_paddr(mmu_rsp_paddr),
      .rsp_fault(mmu_rsp_fault),
      .rsp_ready(mmu_rsp_ready)
  );

  // Default MMU hook signals (no translation consumers yet).
  assign mmu_req_valid  = 1'b0;
  assign mmu_req_vaddr  = '0;
  assign mmu_req_access = '0;
  assign mmu_rsp_ready  = 1'b1;

  logic trap_raise_valid;
  logic [31:0] trap_raise_cause;
  logic [63:0] trap_raise_epc;

  logic trap_in_trap;
  logic [31:0] trap_cause_q;
  logic [63:0] trap_epc_q;
  logic trap_ret_valid;
  logic [63:0] trap_ret_pc;

  trap_unit u_trap (
      .clk(clk),
      .rst_n(rst_n),
      .raise_valid(trap_raise_valid),
      .raise_cause(trap_raise_cause),
      .raise_epc(trap_raise_epc),
      .sret(1'b0),
      .hret(1'b0),
      .epc_we(csr.req_valid && csr.req_ready && csr.req_write &&
              (csr.req_addr == CSR_ADDR_W'(CARBON_CSR_EPC)) &&
              (csr.req_priv >= CSR_PRIV_W'(1))),
      .epc_wdata(csr.req_wdata),
      .in_trap(trap_in_trap),
      .cause(trap_cause_q),
      .epc(trap_epc_q),
      .ret_valid(trap_ret_valid),
      .ret_pc(trap_ret_pc)
  );

  // --------------------------------------------------------------------------
  // Debug control (halt/step) - dbg_if + CSR mirror
  // --------------------------------------------------------------------------
  logic halt_debug_q;
  logic halt_trap_q;
  logic halt_instr_q;
  logic step_token_q;
  logic step_ack_pulse_q;
  logic step_ack_sticky_q;

  wire core_halted = halt_debug_q || halt_trap_q || halt_instr_q;

  assign dbg.halt_ack    = core_halted;
  assign dbg.step_ack    = step_ack_pulse_q;
  assign dbg.bp_ready    = 1'b1;
  assign dbg.trace_valid = 1'b0;
  assign dbg.trace_data  = '0;

  // --------------------------------------------------------------------------
  // Front-end + OoO pipeline skeleton wiring
  // --------------------------------------------------------------------------
  wire run_en = !core_halted;
  wire flush_pipe = 1'b0;

  // I$ hook between fetch and stub port
  logic ic_req_valid, ic_req_ready;
  logic [63:0] ic_req_pc;
  logic ic_rsp_valid, ic_rsp_ready, ic_rsp_fault;
  logic [63:0] ic_rsp_pc;
  logic [31:0] ic_rsp_inst;

  fe_icache_port u_fe_ic (
      .clk(clk),
      .rst_n(rst_n),
      .req_valid(ic_req_valid),
      .req_pc(ic_req_pc),
      .req_ready(ic_req_ready),
      .rsp_valid(ic_rsp_valid),
      .rsp_pc(ic_rsp_pc),
      .rsp_inst(ic_rsp_inst),
      .rsp_fault(ic_rsp_fault),
      .rsp_ready(ic_rsp_ready)
  );

  logic inst_valid, inst_ready, inst_fault;
  logic [63:0] inst_pc;
  logic [31:0] inst_word;

  fe_fetch u_fetch (
      .clk(clk),
      .rst_n(rst_n),
      .run_en(run_en),
      .redirect_valid(1'b0),
      .redirect_pc('0),
      .ic_req_valid(ic_req_valid),
      .ic_req_pc(ic_req_pc),
      .ic_req_ready(ic_req_ready),
      .ic_rsp_valid(ic_rsp_valid),
      .ic_rsp_pc(ic_rsp_pc),
      .ic_rsp_inst(ic_rsp_inst),
      .ic_rsp_fault(ic_rsp_fault),
      .ic_rsp_ready(ic_rsp_ready),
      .inst_valid(inst_valid),
      .inst_pc(inst_pc),
      .inst_word(inst_word),
      .inst_fault(inst_fault),
      .inst_ready(inst_ready)
  );

  logic dec_uop_valid, dec_uop_ready;
  z480_uop_t dec_uop;

  fe_decode u_decode (
      .clk(clk),
      .rst_n(rst_n),
      .inst_valid(inst_valid),
      .inst_pc(inst_pc),
      .inst_word(inst_word),
      .inst_fault(inst_fault),
      .inst_ready(inst_ready),
      .uop_valid(dec_uop_valid),
      .uop(dec_uop),
      .uop_ready(dec_uop_ready)
  );

  logic uc_uop_valid, uc_uop_ready;
  z480_uop_t uc_uop;

  fe_uop_cache u_uop_cache (
      .clk(clk),
      .rst_n(rst_n),
      .in_valid(dec_uop_valid),
      .in_uop(dec_uop),
      .in_ready(dec_uop_ready),
      .out_valid(uc_uop_valid),
      .out_uop(uc_uop),
      .out_ready(uc_uop_ready)
  );

  logic uq_out_valid, uq_out_ready;
  z480_uop_t uq_out_uop;
  logic [$clog2(UOPQ_DEPTH+1)-1:0] uq_level;

  uop_queue #(
      .DEPTH(UOPQ_DEPTH),
      .T(z480_uop_t)
  ) u_uopq (
      .clk(clk),
      .rst_n(rst_n),
      .in_valid(uc_uop_valid),
      .in_data(uc_uop),
      .in_ready(uc_uop_ready),
      .out_valid(uq_out_valid),
      .out_data(uq_out_uop),
      .out_ready(uq_out_ready),
      .level(uq_level)
  );

  logic rn_out_valid, rn_out_ready;
  z480_uop_rn_t rn_out_uop;

  renamer u_renamer (
      .clk(clk),
      .rst_n(rst_n),
      .flush(flush_pipe),
      .in_valid(uq_out_valid),
      .in_uop(uq_out_uop),
      .in_ready(uq_out_ready),
      .out_valid(rn_out_valid),
      .out_uop(rn_out_uop),
      .out_ready(rn_out_ready)
  );

  logic rob_alloc_valid, rob_alloc_ready;
  z480_uop_rn_t rob_alloc_uop;
  logic [5:0] rob_alloc_idx;

  logic rs_in_valid, rs_in_ready;
  z480_uop_tagged_t rs_in_uop;

  logic lsq_in_valid, lsq_in_ready;
  z480_uop_tagged_t lsq_in_uop;

  dispatch u_dispatch (
      .clk(clk),
      .rst_n(rst_n),
      .in_valid(rn_out_valid),
      .in_uop(rn_out_uop),
      .in_ready(rn_out_ready),
      .rob_alloc_valid(rob_alloc_valid),
      .rob_alloc_uop(rob_alloc_uop),
      .rob_alloc_ready(rob_alloc_ready),
      .rob_alloc_idx(rob_alloc_idx),
      .rs_valid(rs_in_valid),
      .rs_uop(rs_in_uop),
      .rs_ready(rs_in_ready),
      .lsq_valid(lsq_in_valid),
      .lsq_uop(lsq_in_uop),
      .lsq_ready(lsq_in_ready)
  );

  logic rob_wb_valid, rob_wb_ready;
  z480_wb_t rob_wb;

  logic rob_head_valid, rob_head_done, rob_head_has_trap;
  z480_uop_rn_t rob_head_uop;
  logic [5:0] rob_head_idx;
  logic [31:0] rob_head_trap_cause;
  logic rob_head_pop;

  rob #(.DEPTH(ROB_DEPTH)) u_rob (
      .clk(clk),
      .rst_n(rst_n),
      .flush(flush_pipe),
      .alloc_valid(rob_alloc_valid),
      .alloc_uop(rob_alloc_uop),
      .alloc_ready(rob_alloc_ready),
      .alloc_idx(rob_alloc_idx),
      .wb_valid(rob_wb_valid),
      .wb(rob_wb),
      .wb_ready(rob_wb_ready),
      .head_valid(rob_head_valid),
      .head_done(rob_head_done),
      .head_uop(rob_head_uop),
      .head_idx(rob_head_idx),
      .head_has_trap(rob_head_has_trap),
      .head_trap_cause(rob_head_trap_cause),
      .head_pop(rob_head_pop)
  );

  // For v1, drive scheduler from RS/LSQ FIFO outputs.
  logic rs_issue_valid, rs_issue_ready;
  z480_uop_tagged_t rs_issue_uop;

  logic lsq_issue_valid, lsq_issue_ready;
  z480_uop_tagged_t lsq_issue_uop;

  rs_int u_rs (
      .clk(clk),
      .rst_n(rst_n),
      .flush(flush_pipe),
      .in_valid(rs_in_valid),
      .in_uop(rs_in_uop),
      .in_ready(rs_in_ready),
      .issue_valid(rs_issue_valid),
      .issue_uop(rs_issue_uop),
      .issue_ready(rs_issue_ready)
  );

  // v1: LSQ is instantiated but decode emits no loads/stores.
  lsq u_lsq (
      .clk(clk),
      .rst_n(rst_n),
      .flush(flush_pipe),
      .in_valid(lsq_in_valid),
      .in_uop(lsq_in_uop),
      .in_ready(lsq_in_ready),
      .issue_valid(lsq_issue_valid),
      .issue_uop(lsq_issue_uop),
      .issue_ready(lsq_issue_ready)
  );

  logic sched_int_valid, sched_int_ready;
  z480_uop_tagged_t sched_int_uop;
  logic sched_br_valid, sched_br_ready;
  z480_uop_tagged_t sched_br_uop;
  logic sched_md_valid, sched_md_ready;
  z480_uop_tagged_t sched_md_uop;
  logic sched_vec_valid, sched_vec_ready;
  z480_uop_tagged_t sched_vec_uop;
  logic sched_mem_valid, sched_mem_ready;
  z480_uop_tagged_t sched_mem_uop;

  scheduler u_sched (
      .clk(clk),
      .rst_n(rst_n),
      .flush(flush_pipe),
      .rs_valid(rs_issue_valid),
      .rs_uop(rs_issue_uop),
      .rs_ready(rs_issue_ready),
      .lsq_valid(lsq_issue_valid),
      .lsq_uop(lsq_issue_uop),
      .lsq_ready(lsq_issue_ready),
      .int_valid(sched_int_valid),
      .int_uop(sched_int_uop),
      .int_ready(sched_int_ready),
      .br_valid(sched_br_valid),
      .br_uop(sched_br_uop),
      .br_ready(sched_br_ready),
      .md_valid(sched_md_valid),
      .md_uop(sched_md_uop),
      .md_ready(sched_md_ready),
      .vec_valid(sched_vec_valid),
      .vec_uop(sched_vec_uop),
      .vec_ready(sched_vec_ready),
      .mem_valid(sched_mem_valid),
      .mem_uop(sched_mem_uop),
      .mem_ready(sched_mem_ready)
  );

  assign sched_mem_ready = 1'b0;

  logic int_wb_valid, int_wb_ready;
  z480_wb_t int_wb;
  exec_int_alu u_exec_int (
      .clk(clk),
      .rst_n(rst_n),
      .flush(flush_pipe),
      .in_valid(sched_int_valid),
      .in_uop(sched_int_uop),
      .in_ready(sched_int_ready),
      .wb_valid(int_wb_valid),
      .wb(int_wb),
      .wb_ready(int_wb_ready)
  );

  logic br_wb_valid, br_wb_ready;
  z480_wb_t br_wb;
  exec_branch u_exec_br (
      .clk(clk),
      .rst_n(rst_n),
      .flush(flush_pipe),
      .in_valid(sched_br_valid),
      .in_uop(sched_br_uop),
      .in_ready(sched_br_ready),
      .wb_valid(br_wb_valid),
      .wb(br_wb),
      .wb_ready(br_wb_ready)
  );

  logic md_wb_valid, md_wb_ready;
  z480_wb_t md_wb;
  exec_muldiv u_exec_md (
      .clk(clk),
      .rst_n(rst_n),
      .flush(flush_pipe),
      .in_valid(sched_md_valid),
      .in_uop(sched_md_uop),
      .in_ready(sched_md_ready),
      .wb_valid(md_wb_valid),
      .wb(md_wb),
      .wb_ready(md_wb_ready)
  );

  logic vec_wb_valid, vec_wb_ready;
  z480_wb_t vec_wb;
  exec_vec u_exec_vec (
      .clk(clk),
      .rst_n(rst_n),
      .flush(flush_pipe),
      .in_valid(sched_vec_valid),
      .in_uop(sched_vec_uop),
      .in_ready(sched_vec_ready),
      .wb_valid(vec_wb_valid),
      .wb(vec_wb),
      .wb_ready(vec_wb_ready)
  );

  writeback u_wb (
      .clk(clk),
      .rst_n(rst_n),
      .int_wb_valid(int_wb_valid),
      .int_wb(int_wb),
      .int_wb_ready(int_wb_ready),
      .br_wb_valid(br_wb_valid),
      .br_wb(br_wb),
      .br_wb_ready(br_wb_ready),
      .md_wb_valid(md_wb_valid),
      .md_wb(md_wb),
      .md_wb_ready(md_wb_ready),
      .vec_wb_valid(vec_wb_valid),
      .vec_wb(vec_wb),
      .vec_wb_ready(vec_wb_ready),
      .rob_wb_valid(rob_wb_valid),
      .rob_wb(rob_wb),
      .rob_wb_ready(rob_wb_ready)
  );

  logic commit_valid;
  z480_commit_evt_t commit_evt;
  logic [63:0] retired_count;

  commit u_commit (
      .clk(clk),
      .rst_n(rst_n),
      .retire_en(run_en),
      .rob_head_valid(rob_head_valid),
      .rob_head_done(rob_head_done),
      .rob_head_uop(rob_head_uop),
      .rob_head_idx(rob_head_idx),
      .rob_head_has_trap(rob_head_has_trap),
      .rob_head_trap_cause(rob_head_trap_cause),
      .rob_head_pop(rob_head_pop),
      .commit_valid(commit_valid),
      .commit_evt(commit_evt),
      .retired_count(retired_count)
  );

  assign trap_raise_valid = commit_valid && commit_evt.has_trap;
  assign trap_raise_cause = commit_evt.trap_cause;
  assign trap_raise_epc   = commit_evt.trap_epc;

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
  // Sequential control + CSR decode
  // --------------------------------------------------------------------------
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      cycle_q <= 64'd0;
      tier_q <= 8'(CARBON_Z80_DERIVED_TIER_P7_Z480);
      modeflags_q <= 8'h00;

      cpuid_leaf_q <= 32'h0;
      cpuid_subleaf_q <= 32'h0;

      csr_rsp_valid_q <= 1'b0;
      csr_rsp_rdata_q <= '0;
      csr_rsp_fault_q <= 1'b0;
      csr_rsp_side_q  <= 1'b0;

      halt_debug_q <= 1'b0;
      halt_trap_q  <= 1'b0;
      halt_instr_q <= 1'b0;
      step_token_q <= 1'b0;
      step_ack_pulse_q <= 1'b0;
      step_ack_sticky_q <= 1'b0;
    end else begin
      cycle_q <= cycle_q + 64'd1;
      step_ack_pulse_q <= 1'b0;

      // Debug control (dbg_if)
      if (dbg.halt_req) halt_debug_q <= 1'b1;
      if (dbg.run_req) begin
        halt_debug_q <= 1'b0;
        step_token_q <= 1'b0;
      end
      if (dbg.step_req && halt_debug_q && !step_token_q && !halt_trap_q && !halt_instr_q) begin
        step_token_q <= 1'b1;
      end

      // Debug single-step start/finish
      if (step_token_q && halt_debug_q && !halt_trap_q && !halt_instr_q) begin
        halt_debug_q <= 1'b0;
      end
      if (step_token_q && !halt_debug_q && commit_valid) begin
        halt_debug_q <= 1'b1;
        step_token_q <= 1'b0;
        step_ack_pulse_q <= 1'b1;
        step_ack_sticky_q <= 1'b1;
      end

      if (csr_rsp_fire) csr_rsp_valid_q <= 1'b0;

      if (csr_req_fire) begin
        csr_rsp_valid_q <= 1'b1;
        csr_rsp_fault_q <= 1'b0;
        csr_rsp_side_q  <= csr.req_write;
        csr_rsp_rdata_q <= '0;

        unique case (csr.req_addr)
          CARBON_CSR_ID: begin
            if (!csr.req_write) csr_rsp_rdata_q <= 32'h5A34_3801;  // "Z48"+v1 (impl-defined)
            else csr_rsp_fault_q <= 1'b1;
          end
          CARBON_CSR_TIER: begin
            if (!csr.req_write) begin
              csr_rsp_rdata_q[7:0] <= tier_q;
            end else begin
              if (csr.req_priv < CSR_PRIV_W'(1)) csr_rsp_fault_q <= 1'b1;
              else if (csr.req_wdata[7:0] != 8'(CARBON_Z80_DERIVED_TIER_P7_Z480)) csr_rsp_fault_q <= 1'b1;
              else tier_q <= csr.req_wdata[7:0];
            end
          end
          CARBON_CSR_MODEFLAGS: begin
            if (!csr.req_write) begin
              csr_rsp_rdata_q[7:0] <= modeflags_q;
            end else begin
              if (csr.req_priv < CSR_PRIV_W'(1)) csr_rsp_fault_q <= 1'b1;
              else if ((csr.req_wdata[7:0] & 8'hFC) != 8'h00) csr_rsp_fault_q <= 1'b1;
              else modeflags_q <= csr.req_wdata[7:0];
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
            if (!csr.req_write) begin
              if (csr.req_priv < CSR_PRIV_W'(1)) csr_rsp_fault_q <= 1'b1;
              else csr_rsp_rdata_q <= trap_cause_q;
            end else begin
              csr_rsp_fault_q <= 1'b1;
            end
          end
          CARBON_CSR_EPC: begin
            if (!csr.req_write) begin
              if (csr.req_priv < CSR_PRIV_W'(1)) csr_rsp_fault_q <= 1'b1;
              else csr_rsp_rdata_q <= trap_epc_q[31:0];
            end else begin
              if (csr.req_priv < CSR_PRIV_W'(1)) csr_rsp_fault_q <= 1'b1;
            end
          end
          CARBON_CSR_IE: begin
            if (!csr.req_write) begin
              if (csr.req_priv < CSR_PRIV_W'(1)) csr_rsp_fault_q <= 1'b1;
              else csr_rsp_rdata_q <= ie_q;
            end else begin
              if (csr.req_priv < CSR_PRIV_W'(1)) csr_rsp_fault_q <= 1'b1;
            end
          end
          CARBON_CSR_IP: begin
            if (!csr.req_write) begin
              if (csr.req_priv < CSR_PRIV_W'(1)) csr_rsp_fault_q <= 1'b1;
              else csr_rsp_rdata_q <= ip_q;
            end else begin
              csr_rsp_fault_q <= 1'b1;
            end
          end

          // CPUID CSR window
          CARBON_CSR_CPUID_LEAF: begin
            if (!csr.req_write) csr_rsp_rdata_q <= cpuid_leaf_q;
            else cpuid_leaf_q <= csr.req_wdata;
          end
          CARBON_CSR_CPUID_SUBLEAF: begin
            if (!csr.req_write) csr_rsp_rdata_q <= cpuid_subleaf_q;
            else cpuid_subleaf_q <= csr.req_wdata;
          end
          CARBON_CSR_CPUID_DATA0_LO: begin
            if (!csr.req_write) csr_rsp_rdata_q <= cpuid_d0[31:0];
            else csr_rsp_fault_q <= 1'b1;
          end
          CARBON_CSR_CPUID_DATA0_HI: begin
            if (!csr.req_write) csr_rsp_rdata_q <= cpuid_d0[63:32];
            else csr_rsp_fault_q <= 1'b1;
          end
          CARBON_CSR_CPUID_DATA1_LO: begin
            if (!csr.req_write) csr_rsp_rdata_q <= cpuid_d1[31:0];
            else csr_rsp_fault_q <= 1'b1;
          end
          CARBON_CSR_CPUID_DATA1_HI: begin
            if (!csr.req_write) csr_rsp_rdata_q <= cpuid_d1[63:32];
            else csr_rsp_fault_q <= 1'b1;
          end
          CARBON_CSR_CPUID_DATA2_LO: begin
            if (!csr.req_write) csr_rsp_rdata_q <= cpuid_d2[31:0];
            else csr_rsp_fault_q <= 1'b1;
          end
          CARBON_CSR_CPUID_DATA2_HI: begin
            if (!csr.req_write) csr_rsp_rdata_q <= cpuid_d2[63:32];
            else csr_rsp_fault_q <= 1'b1;
          end
          CARBON_CSR_CPUID_DATA3_LO: begin
            if (!csr.req_write) csr_rsp_rdata_q <= cpuid_d3[31:0];
            else csr_rsp_fault_q <= 1'b1;
          end
          CARBON_CSR_CPUID_DATA3_HI: begin
            if (!csr.req_write) csr_rsp_rdata_q <= cpuid_d3[63:32];
            else csr_rsp_fault_q <= 1'b1;
          end

          // Debug CSRs (CSR mirror of dbg_if)
          CARBON_CSR_DBG_CTRL: begin
            if (!csr.req_write) begin
              if (csr.req_priv < CSR_PRIV_W'(1)) csr_rsp_fault_q <= 1'b1;
              else csr_rsp_rdata_q[0] <= halt_debug_q;
            end else begin
              if (csr.req_priv < CSR_PRIV_W'(1)) begin
                csr_rsp_fault_q <= 1'b1;
              end else begin
                halt_debug_q <= csr.req_wdata[0];
                if (!csr.req_wdata[0]) step_token_q <= 1'b0;
              end
            end
          end
          CARBON_CSR_DBG_STEP: begin
            if (!csr.req_write) begin
              csr_rsp_fault_q <= 1'b1;
            end else begin
              if (csr.req_priv < CSR_PRIV_W'(1)) csr_rsp_fault_q <= 1'b1;
              else if (!halt_debug_q || step_token_q) csr_rsp_fault_q <= 1'b1;
              else begin
                step_token_q <= 1'b1;
              end
            end
          end
          CARBON_CSR_DBG_STATUS: begin
            if (!csr.req_write) begin
              if (csr.req_priv < CSR_PRIV_W'(1)) csr_rsp_fault_q <= 1'b1;
              else begin
                csr_rsp_rdata_q[0] <= core_halted;
                csr_rsp_rdata_q[1] <= step_ack_sticky_q;
                csr_rsp_rdata_q[2] <= step_token_q;
                csr_rsp_rdata_q[3] <= irq_any_pending;
                csr_rsp_side_q <= 1'b1;
                step_ack_sticky_q <= 1'b0;
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
    end
  end

  wire _unused = ^{priv_mode, trap_in_trap, trap_ret_valid, trap_ret_pc[0], uq_level[0]};

endmodule : z480_core
