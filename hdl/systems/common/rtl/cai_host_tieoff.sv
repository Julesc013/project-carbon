// Project Carbon - Systems
// cai_host_tieoff: Drives a cai_if host side to an idle state.

module cai_host_tieoff (
    cai_if.host cai
);
  assign cai.submit_desc_base = '0;
  assign cai.submit_ring_mask = '0;
  assign cai.submit_doorbell  = 1'b0;
  assign cai.context_sel      = '0;

endmodule : cai_host_tieoff

