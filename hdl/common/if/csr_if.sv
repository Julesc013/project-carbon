// Project Carbon - Common Infrastructure
// csr_if: Simple CSR request/response channel.
//
// Contract:
// - A request is accepted on `req_valid && req_ready`.
// - A response is accepted on `rsp_valid && rsp_ready`.
// - Responses may be returned in the same cycle as request acceptance or later.
// - When `req_valid && !req_ready`, request signals must remain stable.
// - When `rsp_valid && !rsp_ready`, response signals must remain stable.

interface csr_if #(
    parameter int unsigned ADDR_W = 32,
    parameter int unsigned DATA_W = 32,
    parameter int unsigned PRIV_W = 2
) (
    input logic clk,
    input logic rst_n
);
  import carbon_arch_pkg::*;

  // Request
  logic                 req_valid;
  logic                 req_ready;
  logic                 req_write;
  logic [ADDR_W-1:0]     req_addr;
  logic [DATA_W-1:0]     req_wdata;
  logic [(DATA_W/8)-1:0] req_wstrb;
  logic [PRIV_W-1:0]     req_priv;

  // Response
  logic               rsp_valid;
  logic               rsp_ready;
  logic [DATA_W-1:0]  rsp_rdata;
  logic               rsp_fault;
  logic               rsp_side_effect;

  modport master (
      output req_valid,
      output req_write,
      output req_addr,
      output req_wdata,
      output req_wstrb,
      output req_priv,
      input  req_ready,

      input  rsp_valid,
      input  rsp_rdata,
      input  rsp_fault,
      input  rsp_side_effect,
      output rsp_ready
  );

  modport slave (
      input  req_valid,
      input  req_write,
      input  req_addr,
      input  req_wdata,
      input  req_wstrb,
      input  req_priv,
      output req_ready,

      output rsp_valid,
      output rsp_rdata,
      output rsp_fault,
      output rsp_side_effect,
      input  rsp_ready
  );

  modport monitor (
      input req_valid,
      input req_ready,
      input req_write,
      input req_addr,
      input req_wdata,
      input req_wstrb,
      input req_priv,
      input rsp_valid,
      input rsp_ready,
      input rsp_rdata,
      input rsp_fault,
      input rsp_side_effect
  );

`ifndef SYNTHESIS
`ifdef CARBON_ENABLE_SVA
  assert property (@(posedge clk) disable iff (!rst_n)
      (req_valid && !req_ready |-> $stable(
          {req_write, req_addr, req_wdata, req_wstrb, req_priv}
      ))
  )
      else $error("csr_if: request changed while backpressured");

  assert property (@(posedge clk) disable iff (!rst_n)
      (rsp_valid && !rsp_ready |-> $stable(
          {rsp_rdata, rsp_fault, rsp_side_effect}
      ))
  )
      else $error("csr_if: response changed while backpressured");
`endif
`endif

endinterface : csr_if
