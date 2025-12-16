// Project Carbon - eZ90 P7 core scaffold
// fe_uop_cache: Stub uop-cache hook (v1: pass-through).

module fe_uop_cache (
    input logic clk,
    input logic rst_n,

    input  logic         in_valid,
    input  ez90_pkg::ez90_uop_t in_uop,
    output logic         in_ready,

    output logic         out_valid,
    output ez90_pkg::ez90_uop_t out_uop,
    input  logic         out_ready
);
  import ez90_pkg::*;

  assign in_ready  = out_ready;
  assign out_valid = in_valid;
  assign out_uop   = in_uop;

  wire _unused = clk ^ rst_n;

endmodule : fe_uop_cache

