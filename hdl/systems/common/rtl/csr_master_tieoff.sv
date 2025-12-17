// Project Carbon - Systems
// csr_master_tieoff: Drives a csr_if master to an idle state.

module csr_master_tieoff (
    csr_if.master csr
);
  assign csr.req_valid = 1'b0;
  assign csr.req_write = 1'b0;
  assign csr.req_addr  = '0;
  assign csr.req_wdata = '0;
  assign csr.req_wstrb = '0;
  assign csr.req_priv  = '0;
  assign csr.rsp_ready = 1'b1;

endmodule : csr_master_tieoff

