// Project Carbon - Z480 P7 core scaffold
// mmu: Minimal MMU scaffolding (registers + translation request/response hook).

module mmu (
    input logic clk,
    input logic rst_n,

    // CSR-programmable registers (future CSR map expansion)
    input  logic        pt_base_we,
    input  logic [63:0] pt_base_wdata,
    output logic [63:0] pt_base,

    input  logic        asid_we,
    input  logic [15:0] asid_wdata,
    output logic [15:0] asid,

    input  logic        vmid_we,
    input  logic [15:0] vmid_wdata,
    output logic [15:0] vmid,

    // Translation request/response (core-side hook)
    input  logic        req_valid,
    input  logic [63:0] req_vaddr,
    input  logic [2:0]  req_access,
    output logic        req_ready,

    output logic        rsp_valid,
    output logic [63:0] rsp_paddr,
    output logic        rsp_fault,
    input  logic        rsp_ready
);
  logic [63:0] pt_base_q;
  logic [15:0] asid_q;
  logic [15:0] vmid_q;

  assign pt_base = pt_base_q;
  assign asid    = asid_q;
  assign vmid    = vmid_q;

  // v1 stub: identity mapping, single-entry response buffer.
  logic hold_q;
  logic [63:0] vaddr_q;

  assign req_ready = !hold_q;
  wire req_fire = req_valid && req_ready;

  assign rsp_valid = hold_q;
  assign rsp_paddr = vaddr_q;
  assign rsp_fault = 1'b0;
  wire rsp_fire = rsp_valid && rsp_ready;

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      pt_base_q <= 64'h0;
      asid_q    <= 16'h0;
      vmid_q    <= 16'h0;
      hold_q    <= 1'b0;
      vaddr_q   <= 64'h0;
    end else begin
      if (pt_base_we) pt_base_q <= pt_base_wdata;
      if (asid_we)    asid_q    <= asid_wdata;
      if (vmid_we)    vmid_q    <= vmid_wdata;

      if (rsp_fire) begin
        hold_q <= 1'b0;
      end
      if (req_fire) begin
        hold_q  <= 1'b1;
        vaddr_q <= req_vaddr;
      end
    end
  end

  wire _unused = ^req_access;

endmodule : mmu
