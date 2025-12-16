// Project Carbon - eZ90 P7 core scaffold
// writeback: Collects FU completions and forwards to ROB (v1: fixed priority).

module writeback (
    input logic clk,
    input logic rst_n,

    input  logic           int_wb_valid,
    input  ez90_pkg::ez90_wb_t int_wb,
    output logic           int_wb_ready,

    input  logic           br_wb_valid,
    input  ez90_pkg::ez90_wb_t br_wb,
    output logic           br_wb_ready,

    input  logic           md_wb_valid,
    input  ez90_pkg::ez90_wb_t md_wb,
    output logic           md_wb_ready,

    input  logic           vec_wb_valid,
    input  ez90_pkg::ez90_wb_t vec_wb,
    output logic           vec_wb_ready,

    output logic           rob_wb_valid,
    output ez90_pkg::ez90_wb_t rob_wb,
    input  logic           rob_wb_ready
);
  import ez90_pkg::*;

  always_comb begin
    int_wb_ready = 1'b0;
    br_wb_ready  = 1'b0;
    md_wb_ready  = 1'b0;
    vec_wb_ready = 1'b0;

    rob_wb_valid = 1'b0;
    rob_wb       = '0;

    if (int_wb_valid) begin
      rob_wb_valid = 1'b1;
      rob_wb = int_wb;
      int_wb_ready = rob_wb_ready;
    end else if (br_wb_valid) begin
      rob_wb_valid = 1'b1;
      rob_wb = br_wb;
      br_wb_ready = rob_wb_ready;
    end else if (md_wb_valid) begin
      rob_wb_valid = 1'b1;
      rob_wb = md_wb;
      md_wb_ready = rob_wb_ready;
    end else if (vec_wb_valid) begin
      rob_wb_valid = 1'b1;
      rob_wb = vec_wb;
      vec_wb_ready = rob_wb_ready;
    end
  end

  wire _unused = clk ^ rst_n;

endmodule : writeback

