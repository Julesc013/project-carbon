// Project Carbon - Systems
// z80_bus_adapter_stub: Placeholder adapter from a conceptual Z80 bus cycle into fabric_if.
//
// This module is intentionally a stub for v1 system integration:
// - It does NOT model Z80 pin timing (MREQ/IORQ/RD/WR/WAIT, etc).
// - It exists to reserve a stable integration point for future physical adapters
//   (e.g., RC2014/S-100 socket replacement boards).

module z80_bus_adapter_stub (
    input logic clk,
    input logic rst_n,

    // Conceptual single-cycle request/response (abstracted Z80 bus cycle)
    input  logic        req_valid,
    input  logic        req_is_io,
    input  logic        req_write,
    input  logic [15:0] req_addr,
    input  logic [7:0]  req_wdata,
    output logic        req_ready,

    output logic        rsp_valid,
    output logic [7:0]  rsp_rdata,
    output logic        rsp_fault,

    // Fabric master port (future implementation will translate cycles here)
    fabric_if.master fab
);
  import carbon_arch_pkg::*;

  // Stub behavior: accept requests but perform no fabric transactions.
  assign req_ready = 1'b1;
  assign rsp_valid = 1'b0;
  assign rsp_rdata = 8'h00;
  assign rsp_fault = 1'b0;

  // Keep fabric idle.
  assign fab.req_valid = 1'b0;
  assign fab.req_op    = $bits(fab.req_op)'(CARBON_FABRIC_XACT_READ);
  assign fab.req_addr  = '0;
  assign fab.req_wdata = '0;
  assign fab.req_wstrb = '0;
  assign fab.req_size  = '0;
  assign fab.req_attr  = $bits(fab.req_attr)'(CARBON_FABRIC_ATTR_ORDERED_MASK | (req_is_io ? CARBON_FABRIC_ATTR_IO_SPACE_MASK : 0));
  assign fab.req_id    = '0;
  assign fab.rsp_ready = 1'b1;

  wire _unused = ^{clk, rst_n, req_valid, req_write, req_addr, req_wdata, fab.req_ready, fab.rsp_valid, fab.rsp_rdata, fab.rsp_code, fab.rsp_id};

endmodule : z80_bus_adapter_stub

