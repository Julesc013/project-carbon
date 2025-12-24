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
  import carbon_arch_pkg::*;

  // Debug control registers (canonical CSRs).
  localparam logic [31:0] ADDR_DBG_CTRL = CARBON_CSR_DBG_CTRL;
  localparam logic [31:0] ADDR_DBG_STEP = CARBON_CSR_DBG_STEP;
  localparam logic [31:0] ADDR_DBG_STATUS = CARBON_CSR_DBG_STATUS;

  // Implementation-defined breakpoint CSR slots.
  localparam logic [31:0] ADDR_BP_INDEX = CARBON_CSR_DBG_STATUS + 32'h1;
  localparam logic [31:0] ADDR_BP_ADDR  = CARBON_CSR_DBG_STATUS + 32'h2;
  localparam logic [31:0] ADDR_BP_CTRL  = CARBON_CSR_DBG_STATUS + 32'h3;

  logic halt_req_q;
  logic run_req_q;
  logic step_pulse_q;
  logic bp_pending_q;
  logic bp_write_q;
  logic bp_enable_q;
  logic [7:0] bp_index_q;
  logic [3:0] bp_kind_q;
  logic [31:0] bp_addr_q;

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

  // Break/watch programming stub.
  assign dbg.bp_valid  = bp_pending_q;
  assign dbg.bp_write  = bp_write_q;
  assign dbg.bp_index  = bp_index_q;
  assign dbg.bp_addr   = bp_addr_q;
  assign dbg.bp_kind   = bp_kind_q;
  assign dbg.bp_enable = bp_enable_q;

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
      bp_pending_q <= 1'b0;
      bp_write_q   <= 1'b0;
      bp_enable_q  <= 1'b0;
      bp_index_q   <= '0;
      bp_kind_q    <= '0;
      bp_addr_q    <= '0;
      rsp_valid_q  <= 1'b0;
      rsp_rdata_q  <= '0;
      rsp_fault_q  <= 1'b0;
      rsp_side_q   <= 1'b0;
    end else begin
      // step_pulse is one-cycle
      step_pulse_q <= 1'b0;

      if (bp_pending_q && dbg.bp_ready) begin
        bp_pending_q <= 1'b0;
        bp_write_q   <= 1'b0;
      end

      if (rsp_valid_q && csr_dbg.rsp_ready) begin
        rsp_valid_q <= 1'b0;
      end

      if (csr_dbg.req_valid && csr_dbg.req_ready) begin
        rsp_valid_q <= 1'b1;
        rsp_fault_q <= 1'b0;
        rsp_side_q  <= csr_dbg.req_write;
        rsp_rdata_q <= '0;

        unique case (csr_dbg.req_addr)
          ADDR_DBG_CTRL: begin
            if (csr_dbg.req_write) begin
              halt_req_q <= csr_dbg.req_wdata[0];
              run_req_q  <= csr_dbg.req_wdata[1];
            end else begin
              rsp_rdata_q[0] <= halt_req_q;
              rsp_rdata_q[1] <= run_req_q;
            end
          end
          ADDR_DBG_STEP: begin
            if (csr_dbg.req_write) begin
              step_pulse_q <= 1'b1;
            end else begin
              rsp_fault_q <= 1'b1;
            end
          end
          ADDR_DBG_STATUS: begin
            if (!csr_dbg.req_write) begin
              rsp_rdata_q[0] <= dbg.halt_ack;
              rsp_rdata_q[1] <= dbg.step_ack;
              rsp_rdata_q[2] <= dbg.bp_ready;
              rsp_rdata_q[3] <= bp_pending_q;
            end else begin
              rsp_fault_q <= 1'b1;
            end
          end
          ADDR_BP_INDEX: begin
            if (csr_dbg.req_write) begin
              bp_index_q <= csr_dbg.req_wdata[7:0];
            end else begin
              rsp_rdata_q[7:0] <= bp_index_q;
            end
          end
          ADDR_BP_ADDR: begin
            if (csr_dbg.req_write) begin
              bp_addr_q <= csr_dbg.req_wdata;
            end else begin
              rsp_rdata_q <= bp_addr_q;
            end
          end
          ADDR_BP_CTRL: begin
            if (csr_dbg.req_write) begin
              bp_kind_q   <= csr_dbg.req_wdata[7:4];
              bp_enable_q <= csr_dbg.req_wdata[1];
              bp_write_q  <= csr_dbg.req_wdata[0];
              if (csr_dbg.req_wdata[0]) begin
                bp_pending_q <= 1'b1;
              end
            end else begin
              rsp_rdata_q[0] <= bp_write_q;
              rsp_rdata_q[1] <= bp_enable_q;
              rsp_rdata_q[7:4] <= bp_kind_q;
              rsp_rdata_q[8] <= bp_pending_q;
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
