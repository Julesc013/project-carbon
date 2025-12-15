// Project Carbon - Common Infrastructure
// irq_ctrl_simple: Minimal interrupt controller with CSR programming.
//
// Features:
// - Per-target enable and pending registers (fixed priority: lowest vector wins).
// - Ack clears pending bit for the acknowledged vector.
// - Placeholder inputs for timer tick and IPI injection.
//
// Notes:
// - CSR access currently programs/reads target 0 only (TODO: add per-target windows).

module irq_ctrl_simple #(
    parameter int unsigned N_SOURCES = 32,
    parameter int unsigned M_TARGETS = 1,
    parameter int unsigned IPI_VECTOR = 0,
    parameter int unsigned TIMER_VECTOR = 1
) (
    input logic clk,
    input logic rst_n,

    csr_if.slave csr,

    input  logic [M_TARGETS-1:0][N_SOURCES-1:0] irq_in,
    input  logic [M_TARGETS-1:0]               ipi_in,
    input  logic [M_TARGETS-1:0]               timer_tick,

    irq_if #(.N(N_SOURCES)).src irq_out [M_TARGETS]
);
  import carbon_arch_pkg::*;
  localparam int unsigned VEC_W = (N_SOURCES <= 1) ? 1 : $clog2(N_SOURCES);
  localparam int unsigned DATA_W = 32;

  logic [M_TARGETS-1:0][N_SOURCES-1:0] enable_q;
  logic [M_TARGETS-1:0][N_SOURCES-1:0] pending_q;

  // CSR response registers (single outstanding transaction).
  logic              rsp_valid_q;
  logic [DATA_W-1:0] rsp_rdata_q;
  logic              rsp_fault_q;
  logic              rsp_side_q;

  assign csr.req_ready     = !rsp_valid_q;
  assign csr.rsp_valid     = rsp_valid_q;
  assign csr.rsp_rdata     = rsp_rdata_q;
  assign csr.rsp_fault     = rsp_fault_q;
  assign csr.rsp_side_effect = rsp_side_q;

  function automatic logic [VEC_W-1:0] first_set(input logic [N_SOURCES-1:0] vec);
    int unsigned i;
    begin
      first_set = '0;
      for (i = 0; i < N_SOURCES; i++) begin
        if (vec[i]) begin
          first_set = VEC_W'(i);
          break;
        end
      end
    end
  endfunction

  // Drive IRQ outputs (fixed priority).
  genvar gt;
  generate
    for (gt = 0; gt < M_TARGETS; gt++) begin : g_out
      logic [N_SOURCES-1:0] active;
      assign active = pending_q[gt] & enable_q[gt];
      assign irq_out[gt].irq_valid   = |active;
      assign irq_out[gt].irq_vector  = first_set(active);
      assign irq_out[gt].irq_prio    = '0;
      assign irq_out[gt].irq_pending = pending_q[gt];
    end
  endgenerate

  // Ack and input capture
  integer t;
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      enable_q      <= '0;
      pending_q     <= '0;
      rsp_valid_q   <= 1'b0;
      rsp_rdata_q   <= '0;
      rsp_fault_q   <= 1'b0;
      rsp_side_q    <= 1'b0;
    end else begin
      // Default keep CSR response until accepted.
      if (rsp_valid_q && csr.rsp_ready) begin
        rsp_valid_q <= 1'b0;
      end

      // Capture incoming interrupts into pending.
      for (t = 0; t < int'(M_TARGETS); t++) begin
        logic [N_SOURCES-1:0] pending_next;
        pending_next = pending_q[t] | irq_in[t];
        if (IPI_VECTOR < N_SOURCES) begin
          if (ipi_in[t]) pending_next[IPI_VECTOR] = 1'b1;
        end
        if (TIMER_VECTOR < N_SOURCES) begin
          if (timer_tick[t]) pending_next[TIMER_VECTOR] = 1'b1;
        end
        if (irq_out[t].irq_ack) begin
          if (irq_out[t].irq_ack_vector < N_SOURCES) begin
            pending_next[irq_out[t].irq_ack_vector] = 1'b0;
          end
        end
        pending_q[t] <= pending_next;
      end

      // CSR transaction
      if (csr.req_valid && csr.req_ready) begin
        rsp_valid_q <= 1'b1;
        rsp_side_q  <= csr.req_write;
        rsp_fault_q <= 1'b0;
        rsp_rdata_q <= '0;

        // Privilege gating (U=0, S/H!=0); align with csr_map v1 intent.
        if (csr.req_priv == '0) begin
          rsp_fault_q <= 1'b1;
        end else begin
          unique case (csr.req_addr)
            CARBON_CSR_IE: begin
              if (csr.req_write) begin
                // Target 0 only (TODO: per-target windows).
                int unsigned b;
                for (b = 0; b < (DATA_W/8); b++) begin
                  if (csr.req_wstrb[b]) begin
                    enable_q[0][(b*8)+:8] <= csr.req_wdata[(b*8)+:8];
                  end
                end
              end else begin
                rsp_rdata_q <= enable_q[0][DATA_W-1:0];
              end
            end
            CARBON_CSR_IP: begin
              if (!csr.req_write) begin
                rsp_rdata_q <= pending_q[0][DATA_W-1:0];
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
  end

endmodule : irq_ctrl_simple
