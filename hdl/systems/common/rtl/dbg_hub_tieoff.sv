// Project Carbon - Systems
// dbg_hub_tieoff: Drives a dbg_if hub side to an idle state.

module dbg_hub_tieoff (
    dbg_if.hub dbg
);
  assign dbg.halt_req = 1'b0;
  assign dbg.run_req  = 1'b0;
  assign dbg.step_req = 1'b0;

  assign dbg.bp_valid  = 1'b0;
  assign dbg.bp_write  = 1'b0;
  assign dbg.bp_index  = '0;
  assign dbg.bp_addr   = '0;
  assign dbg.bp_kind   = '0;
  assign dbg.bp_enable = 1'b0;

  assign dbg.trace_ready = 1'b1;

endmodule : dbg_hub_tieoff

