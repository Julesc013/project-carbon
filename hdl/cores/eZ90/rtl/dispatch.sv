// Project Carbon - eZ90 P7 core scaffold
// dispatch: Dispatch stub; allocates ROB entry and routes to RS/LSQ.

module dispatch (
    input logic clk,
    input logic rst_n,

    input  logic                  in_valid,
    input  ez90_pkg::ez90_uop_rn_t in_uop,
    output logic                  in_ready,

    // ROB allocate interface
    output logic                  rob_alloc_valid,
    output ez90_pkg::ez90_uop_rn_t rob_alloc_uop,
    input  logic                  rob_alloc_ready,
    input  logic [5:0]            rob_alloc_idx,

    // RS/LSQ outputs
    output logic                    rs_valid,
    output ez90_pkg::ez90_uop_tagged_t rs_uop,
    input  logic                    rs_ready,

    output logic                    lsq_valid,
    output ez90_pkg::ez90_uop_tagged_t lsq_uop,
    input  logic                    lsq_ready
);
  import ez90_pkg::*;

  wire to_lsq = in_uop.uop.is_load || in_uop.uop.is_store;
  wire sel_ready = to_lsq ? lsq_ready : rs_ready;

  assign in_ready = rob_alloc_ready && sel_ready;
  wire fire = in_valid && in_ready;

  assign rob_alloc_valid = fire;
  assign rob_alloc_uop   = in_uop;

  always_comb begin
    rs_valid  = 1'b0;
    rs_uop    = '0;
    lsq_valid = 1'b0;
    lsq_uop   = '0;

    if (fire) begin
      if (to_lsq) begin
        lsq_valid = 1'b1;
        lsq_uop.uop = in_uop;
        lsq_uop.rob_idx = rob_alloc_idx;
      end else begin
        rs_valid = 1'b1;
        rs_uop.uop = in_uop;
        rs_uop.rob_idx = rob_alloc_idx;
      end
    end
  end

  wire _unused = clk ^ rst_n;

endmodule : dispatch

