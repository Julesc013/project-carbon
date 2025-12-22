// Project Carbon - CarbonIO peripheral
// carbonio_irq_router: Simple source->irq_if router with mask/ack.

module carbonio_irq_router #(
    parameter int unsigned N_SOURCES = 8
) (
    input  logic clk,
    input  logic rst_n,
    input  logic [N_SOURCES-1:0] src_pulse,
    input  logic [N_SOURCES-1:0] enable,
    input  logic [N_SOURCES-1:0] clear,
    output logic [N_SOURCES-1:0] pending,

    irq_if #(.N(N_SOURCES)).src irq_out
);
  localparam int unsigned VEC_W = (N_SOURCES <= 1) ? 1 : $clog2(N_SOURCES);

  logic [N_SOURCES-1:0] pending_q;
  assign pending = pending_q;

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

  wire [N_SOURCES-1:0] active = pending_q & enable;

  assign irq_out.irq_valid   = |active;
  assign irq_out.irq_vector  = first_set(active);
  assign irq_out.irq_prio    = '0;
  assign irq_out.irq_pending = pending_q;

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      pending_q <= '0;
    end else begin
      pending_q <= (pending_q | src_pulse) & ~clear;
      if (irq_out.irq_ack) begin
        if (irq_out.irq_ack_vector < N_SOURCES) begin
          pending_q[irq_out.irq_ack_vector] <= 1'b0;
        end
      end
    end
  end

endmodule : carbonio_irq_router
