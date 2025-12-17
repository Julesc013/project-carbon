// Project Carbon - Systems
// irq_src_tieoff: Drives an irq_if source side to an idle state.

module irq_src_tieoff (
    irq_if.src irq
);
  assign irq.irq_valid   = 1'b0;
  assign irq.irq_vector  = '0;
  assign irq.irq_prio    = '0;
  assign irq.irq_pending = '0;

endmodule : irq_src_tieoff

