// Project Carbon - Simulation BFM
// irq_bfm: Deterministic IRQ stimulus helper.

module irq_bfm #(
    parameter int unsigned N = 32,
    parameter int unsigned PRIO_W = 0
) (
    input logic clk,
    input logic rst_n,
    irq_if.src irq
);
  localparam int unsigned VEC_W = (N <= 1) ? 1 : $clog2(N);
  localparam int unsigned PRIO_W_E = (PRIO_W < 1) ? 1 : PRIO_W;

  initial begin
    irq.irq_valid = 1'b0;
    irq.irq_vector = '0;
    irq.irq_prio = '0;
    irq.irq_pending = '0;
  end

  task automatic irq_set(
      input logic [VEC_W-1:0] vec,
      input logic [PRIO_W_E-1:0] prio,
      input logic [N-1:0] pending
  );
    begin
      irq.irq_valid  = 1'b1;
      irq.irq_vector = vec;
      irq.irq_prio   = prio;
      irq.irq_pending = pending;
    end
  endtask

  task automatic irq_clear();
    begin
      irq.irq_valid  = 1'b0;
      irq.irq_vector = '0;
      irq.irq_prio   = '0;
      irq.irq_pending = '0;
    end
  endtask

  task automatic irq_pulse(
      input logic [VEC_W-1:0] vec,
      input logic [PRIO_W_E-1:0] prio,
      input logic [N-1:0] pending,
      output logic [VEC_W-1:0] ack_vec
  );
    begin
      irq_set(vec, prio, pending);
      while (!irq.irq_ack) @(posedge clk);
      ack_vec = irq.irq_ack_vector;
      @(posedge clk);
      irq_clear();
    end
  endtask

endmodule : irq_bfm
