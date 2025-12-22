// Project Carbon - Common Infrastructure
// dbg_if: ISA-agnostic debug control interface.
//
// This interface is intentionally generic:
// - "halt" stops architectural retirement.
// - "step" is a token to retire one instruction (or one architectural unit of work).
// - Break/watch programming and trace streaming are placeholders for later cores.

interface dbg_if #(
    parameter int unsigned ADDR_W = 32,
    parameter int unsigned TRACE_W = 128
) (
    input logic clk,
    input logic rst_n
);
  // Halt/run control
  logic halt_req;
  logic halt_ack;   // core indicates it is halted
  logic run_req;

  // Single-step token
  logic step_req;
  logic step_ack;

  // Break/watch programming placeholder
  logic             bp_valid;
  logic             bp_ready;
  logic             bp_write;
  logic [7:0]       bp_index;
  logic [ADDR_W-1:0] bp_addr;
  logic [3:0]       bp_kind;
  logic             bp_enable;

  // Trace streaming placeholder (core -> hub)
  logic              trace_valid;
  logic              trace_ready;
  logic [TRACE_W-1:0] trace_data;

  modport hub (
      output halt_req,
      output run_req,
      output step_req,
      input  halt_ack,
      input  step_ack,

      output bp_valid,
      output bp_write,
      output bp_index,
      output bp_addr,
      output bp_kind,
      output bp_enable,
      input  bp_ready,

      input  trace_valid,
      input  trace_data,
      output trace_ready
  );

  modport core (
      input  halt_req,
      input  run_req,
      input  step_req,
      output halt_ack,
      output step_ack,

      input  bp_valid,
      input  bp_write,
      input  bp_index,
      input  bp_addr,
      input  bp_kind,
      input  bp_enable,
      output bp_ready,

      output trace_valid,
      output trace_data,
      input  trace_ready
  );

  modport monitor (
      input halt_req,
      input halt_ack,
      input run_req,
      input step_req,
      input step_ack,
      input bp_valid,
      input bp_ready,
      input bp_write,
      input bp_index,
      input bp_addr,
      input bp_kind,
      input bp_enable,
      input trace_valid,
      input trace_ready,
      input trace_data
  );

`ifndef SYNTHESIS
`ifdef FORMAL
`define CARBON_SVA_ON
`elsif CARBON_ENABLE_SVA
`define CARBON_SVA_ON
`endif
`ifdef CARBON_SVA_ON
  // Trace must remain stable under backpressure.
  assert property (@(posedge clk) disable iff (!rst_n)
      (trace_valid && !trace_ready |-> $stable(trace_data))
  )
      else $error("dbg_if: trace_data changed while backpressured");
`endif
`ifdef CARBON_SVA_ON
`undef CARBON_SVA_ON
`endif
`endif

endinterface : dbg_if
