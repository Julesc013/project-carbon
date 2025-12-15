// Project Carbon - Common Infrastructure
// debug_hub: Minimal debug/trace aggregation point.
//
// This hub aggregates:
// - debug control (halt/run/step) via dbg_if
// - trace_ring (CSR port dedicated to trace)
// - perf_counter_bank (CSR port dedicated to perf)
//
// TODO: unify into a single CSR window with decode as the system grows.

module debug_hub #(
    parameter int unsigned TRACE_W = 128,
    parameter int unsigned TRACE_DEPTH = 16,
    parameter int unsigned PERF_EVENTS = 4
) (
    input logic clk,
    input logic rst_n,

    csr_if.slave csr_dbg,
    csr_if.slave csr_trace,
    csr_if.slave csr_perf,

    dbg_if.hub dbg,

    input logic [PERF_EVENTS-1:0] perf_event_inc
);
  // Debug control registers (implementation-defined offsets on csr_dbg).
  localparam int unsigned SEL_CTRL = 0;
  localparam int unsigned SEL_STATUS = 1;

  logic halt_req_q;
  logic run_req_q;
  logic step_pulse_q;

  // csr_dbg response registers
  logic              rsp_valid_q;
  logic [31:0]       rsp_rdata_q;
  logic              rsp_fault_q;
  logic              rsp_side_q;

  assign csr_dbg.req_ready       = !rsp_valid_q;
  assign csr_dbg.rsp_valid       = rsp_valid_q;
  assign csr_dbg.rsp_rdata       = rsp_rdata_q;
  assign csr_dbg.rsp_fault       = rsp_fault_q;
  assign csr_dbg.rsp_side_effect = rsp_side_q;

  // Drive dbg_if controls.
  assign dbg.halt_req = halt_req_q;
  assign dbg.run_req  = run_req_q;
  assign dbg.step_req = step_pulse_q;

  // Break/watch programming not implemented yet.
  assign dbg.bp_valid  = 1'b0;
  assign dbg.bp_write  = 1'b0;
  assign dbg.bp_index  = '0;
  assign dbg.bp_addr   = '0;
  assign dbg.bp_kind   = '0;
  assign dbg.bp_enable = 1'b0;

  // Instantiate trace ring and connect trace stream placeholder.
  trace_ring #(
      .REC_W(TRACE_W),
      .DEPTH(TRACE_DEPTH)
  ) u_trace (
      .clk(clk),
      .rst_n(rst_n),
      .csr(csr_trace),
      .trace_valid(dbg.trace_valid),
      .trace_ready(dbg.trace_ready),
      .trace_data(dbg.trace_data)
  );

  // Instantiate perf counters.
  perf_counter_bank #(
      .EVENT_COUNT(PERF_EVENTS)
  ) u_perf (
      .clk(clk),
      .rst_n(rst_n),
      .csr(csr_perf),
      .event_inc(perf_event_inc)
  );

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      halt_req_q   <= 1'b0;
      run_req_q    <= 1'b0;
      step_pulse_q <= 1'b0;
      rsp_valid_q  <= 1'b0;
      rsp_rdata_q  <= '0;
      rsp_fault_q  <= 1'b0;
      rsp_side_q   <= 1'b0;
    end else begin
      // step_pulse is one-cycle
      step_pulse_q <= 1'b0;

      if (rsp_valid_q && csr_dbg.rsp_ready) begin
        rsp_valid_q <= 1'b0;
      end

      if (csr_dbg.req_valid && csr_dbg.req_ready) begin
        rsp_valid_q <= 1'b1;
        rsp_fault_q <= 1'b0;
        rsp_side_q  <= csr_dbg.req_write;
        rsp_rdata_q <= '0;

        unique case (csr_dbg.req_addr[3:2])
          SEL_CTRL: begin
            if (csr_dbg.req_write) begin
              halt_req_q <= csr_dbg.req_wdata[0];
              run_req_q  <= csr_dbg.req_wdata[1];
              if (csr_dbg.req_wdata[2]) begin
                step_pulse_q <= 1'b1;
              end
            end else begin
              rsp_rdata_q[0] <= halt_req_q;
              rsp_rdata_q[1] <= run_req_q;
            end
          end
          SEL_STATUS: begin
            if (!csr_dbg.req_write) begin
              rsp_rdata_q[0] <= dbg.halt_ack;
              rsp_rdata_q[1] <= dbg.step_ack;
            end else begin
              rsp_fault_q <= 1'b1;
            end
          end
          default: begin
            rsp_fault_q <= 1'b1;
          end
        endcase
      end
    end
  end

endmodule : debug_hub

