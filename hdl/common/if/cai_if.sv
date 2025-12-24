// Project Carbon - Common Infrastructure
// cai_if: Carbon Accelerator Interface (CAI) register-level link.
//
// This interface models the accelerator-facing control registers and interrupt/doorbell
// indications. Descriptor/completion rings live in memory and are accessed via fabric.

interface cai_if #(
    parameter int unsigned ADDR_W = 64,
    parameter int unsigned STATUS_W = 32,
    parameter int unsigned CTX_W = 16,
    parameter int unsigned RING_W = 32,
    parameter int unsigned VER_W = 16,
    parameter int unsigned FEAT_W = 32
) (
    input logic clk,
    input logic rst_n
);
  import carbon_arch_pkg::*;

  // Host -> device
  logic [ADDR_W-1:0] submit_base;
  logic [RING_W-1:0] submit_size;
  logic              submit_doorbell;
  logic [CTX_W-1:0]  context_sel;

  // Device -> host
  logic [ADDR_W-1:0] comp_base;
  logic [RING_W-1:0] comp_size;
  logic [VER_W-1:0]  cai_version;
  logic [FEAT_W-1:0] cai_feature_bits;
  logic              comp_msg;
  logic              comp_irq;
  logic [STATUS_W-1:0] status;

  modport host (
      output submit_base,
      output submit_size,
      output submit_doorbell,
      output context_sel,

      input  comp_base,
      input  comp_size,
      input  cai_version,
      input  cai_feature_bits,
      input  comp_msg,
      input  comp_irq,
      input  status
  );

  modport dev (
      input  submit_base,
      input  submit_size,
      input  submit_doorbell,
      input  context_sel,

      output comp_base,
      output comp_size,
      output cai_version,
      output cai_feature_bits,
      output comp_msg,
      output comp_irq,
      output status
  );

  modport monitor (
      input submit_base,
      input submit_size,
      input submit_doorbell,
      input context_sel,
      input comp_base,
      input comp_size,
      input cai_version,
      input cai_feature_bits,
      input comp_msg,
      input comp_irq,
      input status
  );

`ifndef SYNTHESIS
  task automatic host_init(
      input logic [ADDR_W-1:0] submit_ring_base,
      input logic [RING_W-1:0] submit_ring_size,
      input logic [CTX_W-1:0]  ctx
  );
    submit_base = submit_ring_base;
    submit_size = submit_ring_size;
    context_sel = ctx;
  endtask

  task automatic ring_submit();
    submit_doorbell <= 1'b1;
    @(posedge clk);
    submit_doorbell <= 1'b0;
  endtask
`endif

`ifndef SYNTHESIS
`ifdef FORMAL
`define CARBON_SVA_ON
`elsif CARBON_ENABLE_SVA
`define CARBON_SVA_ON
`endif
`ifdef CARBON_SVA_ON
  // CAI submit doorbell requires stable ring config and context.
  assert property (@(posedge clk) disable iff (!rst_n)
      (submit_doorbell |-> $stable({submit_base, submit_size, context_sel}))
  )
      else $error("cai_if: config changed while submit_doorbell asserted");
`endif
`ifdef CARBON_SVA_ON
`undef CARBON_SVA_ON
`endif
`endif

endinterface : cai_if
