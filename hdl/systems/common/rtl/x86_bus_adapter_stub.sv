// Project Carbon - Systems
// x86_bus_adapter_stub: Placeholder adapter from a conceptual 8086-style bus cycle into fabric_if.
//
// This stub reserves the integration point for future physical bus adapters.
// It does NOT attempt to model 8086 pin-level timing (ALE, DEN, DT/R, READY, etc).

module x86_bus_adapter_stub (
    input logic clk,
    input logic rst_n,

    // Conceptual single-cycle request/response (abstracted 8086 bus cycle)
    input  logic         req_valid,
    input  logic         req_is_io,
    input  logic         req_write,
    input  logic [19:0]  req_addr,
    input  logic [15:0]  req_wdata,
    input  logic [1:0]   req_be,
    output logic         req_ready,

    output logic         rsp_valid,
    output logic [15:0]  rsp_rdata,
    output logic         rsp_fault,

    // Fabric master port (future implementation will translate cycles here)
    fabric_if.master fab
);
  import carbon_arch_pkg::*;

  // Stub behavior: accept requests but perform no fabric transactions.
  assign req_ready = 1'b1;
  assign rsp_valid = 1'b0;
  assign rsp_rdata = 16'h0000;
  assign rsp_fault = 1'b0;

  // Keep fabric idle.
  assign fab.req_valid = 1'b0;
  assign fab.req_op    = $bits(fab.req_op)'(CARBON_FABRIC_XACT_READ);
  assign fab.req_addr  = '0;
  assign fab.req_wdata = '0;
  assign fab.req_wstrb = '0;
  assign fab.req_size  = '0;
  assign fab.req_attr  = $bits(fab.req_attr)'(CARBON_MEM_ATTR_ORDERED_MASK | (req_is_io ? CARBON_MEM_ATTR_IO_SPACE_MASK : 0));
  assign fab.req_id    = '0;
  assign fab.rsp_ready = 1'b1;

  wire _unused = ^{clk, rst_n, req_valid, req_write, req_addr, req_wdata, req_be, fab.req_ready, fab.rsp_valid, fab.rsp_rdata, fab.rsp_code, fab.rsp_id};

endmodule : x86_bus_adapter_stub
