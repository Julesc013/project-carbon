// Project Carbon - Common Infrastructure
// cai_if: Carbon Accelerator Interface (CAI) register-level link.
//
// This interface models the accelerator-facing control registers and interrupt/doorbell
// indications. Descriptor/completion rings live in memory and are accessed via fabric.

interface cai_if #(
    parameter int unsigned ADDR_W = 64,
    parameter int unsigned STATUS_W = 32,
    parameter int unsigned CTX_W = 16
) (
    input logic clk,
    input logic rst_n
);
  import carbon_arch_pkg::*;

  // Host -> device
  logic [ADDR_W-1:0]  submit_desc_base;
  logic [31:0]        submit_ring_mask;
  logic               submit_doorbell;
  logic [CTX_W-1:0]   context_sel;

  // Device -> host
  logic [ADDR_W-1:0]  comp_base;
  logic               comp_doorbell;
  logic               comp_irq;
  logic [STATUS_W-1:0] status;

  modport host (
      output submit_desc_base,
      output submit_ring_mask,
      output submit_doorbell,
      output context_sel,

      input  comp_base,
      input  comp_doorbell,
      input  comp_irq,
      input  status
  );

  modport dev (
      input  submit_desc_base,
      input  submit_ring_mask,
      input  submit_doorbell,
      input  context_sel,

      output comp_base,
      output comp_doorbell,
      output comp_irq,
      output status
  );

  modport monitor (
      input submit_desc_base,
      input submit_ring_mask,
      input submit_doorbell,
      input context_sel,
      input comp_base,
      input comp_doorbell,
      input comp_irq,
      input status
  );

`ifndef SYNTHESIS
  task automatic host_init(
      input logic [ADDR_W-1:0]  desc_base,
      input logic [31:0]        ring_mask,
      input logic [ADDR_W-1:0]  completion_base,
      input logic [CTX_W-1:0]   ctx
  );
    submit_desc_base = desc_base;
    submit_ring_mask = ring_mask;
    comp_base        = completion_base;
    context_sel      = ctx;
  endtask

  task automatic ring_submit();
    submit_doorbell <= 1'b1;
    @(posedge clk);
    submit_doorbell <= 1'b0;
  endtask
`endif

endinterface : cai_if

