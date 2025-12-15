// Project Carbon - Common Infrastructure
// perf_counter_bank: Minimal performance counter skeleton.
//
// - cycles counter increments every cycle.
// - event counters increment when event_inc pulses.
// - CSR readout uses CARBON_CSR_TIME / CARBON_CSR_TIME_HI for cycles.

module perf_counter_bank #(
    parameter int unsigned EVENT_COUNT = 4,
    parameter int unsigned CSR_DATA_W = 32,
    parameter int unsigned COUNTER_W = 64
) (
    input logic clk,
    input logic rst_n,
    csr_if.slave csr,
    input logic [EVENT_COUNT-1:0] event_inc
);
  import carbon_arch_pkg::*;

  logic [COUNTER_W-1:0] cycles_q;
  logic [COUNTER_W-1:0] events_q [EVENT_COUNT];

  // CSR response registers (single outstanding transaction).
  logic                  rsp_valid_q;
  logic [CSR_DATA_W-1:0] rsp_rdata_q;
  logic                  rsp_fault_q;
  logic                  rsp_side_q;

  assign csr.req_ready       = !rsp_valid_q;
  assign csr.rsp_valid       = rsp_valid_q;
  assign csr.rsp_rdata       = rsp_rdata_q;
  assign csr.rsp_fault       = rsp_fault_q;
  assign csr.rsp_side_effect = rsp_side_q;

  integer i;
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      cycles_q     <= '0;
      for (i = 0; i < int'(EVENT_COUNT); i++) begin
        events_q[i] <= '0;
      end
      rsp_valid_q <= 1'b0;
      rsp_rdata_q <= '0;
      rsp_fault_q <= 1'b0;
      rsp_side_q  <= 1'b0;
    end else begin
      cycles_q <= cycles_q + 1'b1;
      for (i = 0; i < int'(EVENT_COUNT); i++) begin
        if (event_inc[i]) begin
          events_q[i] <= events_q[i] + 1'b1;
        end
      end

      if (rsp_valid_q && csr.rsp_ready) begin
        rsp_valid_q <= 1'b0;
      end

      if (csr.req_valid && csr.req_ready) begin
        rsp_valid_q <= 1'b1;
        rsp_fault_q <= 1'b0;
        rsp_side_q  <= csr.req_write;
        rsp_rdata_q <= '0;

        unique case (csr.req_addr)
          CARBON_CSR_TIME: begin
            if (!csr.req_write) rsp_rdata_q <= cycles_q[31:0];
            else rsp_fault_q <= 1'b1;
          end
          CARBON_CSR_TIME_HI: begin
            if (!csr.req_write) rsp_rdata_q <= cycles_q[63:32];
            else rsp_fault_q <= 1'b1;
          end
          default: begin
            // Event counters are mapped at implementation-defined addresses 0x00000100 + i*2.
            if (!csr.req_write && (csr.req_addr[31:8] == 24'h000001)) begin
              int unsigned idx;
              idx = (csr.req_addr[7:0] >> 1);
              if (idx < EVENT_COUNT) begin
                if (csr.req_addr[0]) rsp_rdata_q <= events_q[idx][63:32];
                else rsp_rdata_q <= events_q[idx][31:0];
              end else begin
                rsp_fault_q <= 1'b1;
              end
            end else begin
              rsp_fault_q <= 1'b1;
            end
          end
        endcase
      end
    end
  end

endmodule : perf_counter_bank

