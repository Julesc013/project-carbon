// Project Carbon - Common Infrastructure
// irq_if: Generic interrupt delivery interface.
//
// The source (controller) presents a single interrupt vector at a time, with an
// optional pending bitmap for debug/inspection.

interface irq_if #(
    parameter int unsigned N = 32,
    parameter int unsigned PRIO_W = 0
) (
    input logic clk,
    input logic rst_n
);
  localparam int unsigned VEC_W = (N <= 1) ? 1 : $clog2(N);
  localparam int unsigned PRIO_W_E = (PRIO_W < 1) ? 1 : PRIO_W;

  logic                 irq_valid;
  logic [VEC_W-1:0]     irq_vector;
  logic [PRIO_W_E-1:0]  irq_prio;
  logic [N-1:0]         irq_pending;

  logic             irq_ack;
  logic [VEC_W-1:0] irq_ack_vector;

  modport src (
      output irq_valid,
      output irq_vector,
      output irq_prio,
      output irq_pending,
      input  irq_ack,
      input  irq_ack_vector
  );

  modport sink (
      input  irq_valid,
      input  irq_vector,
      input  irq_prio,
      input  irq_pending,
      output irq_ack,
      output irq_ack_vector
  );

  modport monitor (
      input irq_valid,
      input irq_vector,
      input irq_prio,
      input irq_pending,
      input irq_ack,
      input irq_ack_vector
  );

`ifndef SYNTHESIS
`ifdef CARBON_ENABLE_SVA
  // Ack must only occur when an interrupt is presented.
  assert property (@(posedge clk) disable iff (!rst_n)
      (irq_ack |-> irq_valid)
  )
      else $error("irq_if: irq_ack asserted when irq_valid=0");
`endif
`endif

endinterface : irq_if
