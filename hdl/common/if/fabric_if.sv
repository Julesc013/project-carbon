// Project Carbon - Common Infrastructure
// fabric_if: Ready/valid request + response fabric channel.
//
// Notes:
// - Responses may return out-of-order across different `req_id` values.
// - In-order response per `req_id` is acceptable for v1.
// - When `req_valid && !req_ready`, request signals must remain stable.
// - When `rsp_valid && !rsp_ready`, response signals must remain stable.

interface fabric_if #(
    parameter int unsigned ADDR_W = 32,
    parameter int unsigned DATA_W = 32,
    parameter int unsigned ID_W   = 4,
    parameter int unsigned OP_W   = 8,
    parameter int unsigned SIZE_W = 3,
    parameter int unsigned ATTR_W = carbon_arch_pkg::CARBON_FABRIC_ATTR_WIDTH_BITS,
    parameter int unsigned CODE_W = 8
) (
    input logic clk,
    input logic rst_n
);
  import carbon_arch_pkg::*;

  // Common attribute presets (ordered + uncacheable semantics).
  localparam logic [ATTR_W-1:0] FABRIC_ATTR_IO_UNCACHED =
      logic [ATTR_W-1:0]'(CARBON_FABRIC_ATTR_IO_SPACE_MASK | CARBON_FABRIC_ATTR_ORDERED_MASK);
  localparam logic [ATTR_W-1:0] FABRIC_ATTR_CAI_UNCACHED =
      logic [ATTR_W-1:0]'(CARBON_FABRIC_ATTR_ORDERED_MASK);
  localparam logic [ATTR_W-1:0] FABRIC_ATTR_MEM_CACHEABLE =
      logic [ATTR_W-1:0]'(CARBON_FABRIC_ATTR_CACHEABLE_MASK);

  function automatic logic [ATTR_W-1:0] fabric_attr_pack(
      input logic cacheable,
      input logic ordered,
      input logic io_space,
      input logic acquire,
      input logic release,
      input logic [CARBON_FABRIC_ATTR_BURST_HINT_WIDTH-1:0] burst_hint,
      input logic [CARBON_FABRIC_ATTR_QOS_WIDTH-1:0] qos
  );
    logic [ATTR_W-1:0] v;
    begin
      v = '0;
      if (cacheable) v |= logic [ATTR_W-1:0]'(CARBON_FABRIC_ATTR_CACHEABLE_MASK);
      if (ordered)   v |= logic [ATTR_W-1:0]'(CARBON_FABRIC_ATTR_ORDERED_MASK);
      if (io_space)  v |= logic [ATTR_W-1:0]'(CARBON_FABRIC_ATTR_IO_SPACE_MASK);
      if (acquire)   v |= logic [ATTR_W-1:0]'(CARBON_FABRIC_ATTR_ACQUIRE_MASK);
      if (release)   v |= logic [ATTR_W-1:0]'(CARBON_FABRIC_ATTR_RELEASE_MASK);
      v |= (logic [ATTR_W-1:0]'(burst_hint) << CARBON_FABRIC_ATTR_BURST_HINT_LSB) &
           logic [ATTR_W-1:0]'(CARBON_FABRIC_ATTR_BURST_HINT_MASK);
      v |= (logic [ATTR_W-1:0]'(qos) << CARBON_FABRIC_ATTR_QOS_LSB) &
           logic [ATTR_W-1:0]'(CARBON_FABRIC_ATTR_QOS_MASK);
      fabric_attr_pack = v;
    end
  endfunction

  // Request channel
  logic                 req_valid;
  logic                 req_ready;
  logic [OP_W-1:0]       req_op;
  logic [ADDR_W-1:0]     req_addr;
  logic [DATA_W-1:0]     req_wdata;
  logic [(DATA_W/8)-1:0] req_wstrb;
  logic [SIZE_W-1:0]     req_size;
  logic [ATTR_W-1:0]     req_attr;
  logic [ID_W-1:0]       req_id;

  // Response channel
  logic               rsp_valid;
  logic               rsp_ready;
  logic [DATA_W-1:0]  rsp_rdata;
  logic [CODE_W-1:0]  rsp_code;
  logic [ID_W-1:0]    rsp_id;

  modport master (
      output req_valid,
      output req_op,
      output req_addr,
      output req_wdata,
      output req_wstrb,
      output req_size,
      output req_attr,
      output req_id,
      input  req_ready,

      input  rsp_valid,
      input  rsp_rdata,
      input  rsp_code,
      input  rsp_id,
      output rsp_ready
  );

  modport slave (
      input  req_valid,
      input  req_op,
      input  req_addr,
      input  req_wdata,
      input  req_wstrb,
      input  req_size,
      input  req_attr,
      input  req_id,
      output req_ready,

      output rsp_valid,
      output rsp_rdata,
      output rsp_code,
      output rsp_id,
      input  rsp_ready
  );

  modport monitor (
      input req_valid,
      input req_ready,
      input req_op,
      input req_addr,
      input req_wdata,
      input req_wstrb,
      input req_size,
      input req_attr,
      input req_id,
      input rsp_valid,
      input rsp_ready,
      input rsp_rdata,
      input rsp_code,
      input rsp_id
  );

`ifndef SYNTHESIS
`ifdef FORMAL
`define CARBON_SVA_ON
`elsif CARBON_ENABLE_SVA
`define CARBON_SVA_ON
`endif
`ifdef CARBON_SVA_ON
  // Hold request stable under backpressure.
  assert property (@(posedge clk) disable iff (!rst_n)
      (req_valid && !req_ready |-> $stable(
          {req_op, req_addr, req_wdata, req_wstrb, req_size, req_attr, req_id}
      ))
  )
      else $error("fabric_if: request changed while backpressured");

  // Hold response stable under backpressure.
  assert property (@(posedge clk) disable iff (!rst_n)
      (rsp_valid && !rsp_ready |-> $stable({rsp_rdata, rsp_code, rsp_id}))
  )
      else $error("fabric_if: response changed while backpressured");
`endif
`ifdef CARBON_SVA_ON
`undef CARBON_SVA_ON
`endif
`endif

endinterface : fabric_if
