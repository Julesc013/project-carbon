// Project Carbon - eZ90 P7 core scaffold
// lsq: Load/store queue skeleton (v1: FIFO, no memory operations).

module lsq #(
    parameter int unsigned DEPTH = 8
) (
    input logic clk,
    input logic rst_n,

    input  logic flush,

    input  logic                     in_valid,
    input  ez90_pkg::ez90_uop_tagged_t in_uop,
    output logic                     in_ready,

    output logic                     issue_valid,
    output ez90_pkg::ez90_uop_tagged_t issue_uop,
    input  logic                     issue_ready
);
  import ez90_pkg::*;

  localparam int unsigned PTR_W = (DEPTH < 2) ? 1 : $clog2(DEPTH);
  localparam int unsigned COUNT_W = $clog2(DEPTH + 1);

  ez90_uop_tagged_t mem [DEPTH];
  logic [PTR_W-1:0] head_q;
  logic [PTR_W-1:0] tail_q;
  logic [COUNT_W-1:0] count_q;

  assign in_ready    = (count_q != COUNT_W'(DEPTH));
  assign issue_valid = (count_q != '0);
  assign issue_uop   = mem[head_q];

  wire push_fire = in_valid && in_ready;
  wire pop_fire  = issue_valid && issue_ready;

  function automatic logic [PTR_W-1:0] ptr_inc(input logic [PTR_W-1:0] p);
    if (DEPTH < 2) ptr_inc = '0;
    else if (p == PTR_W'(DEPTH - 1)) ptr_inc = '0;
    else ptr_inc = p + 1'b1;
  endfunction

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      head_q  <= '0;
      tail_q  <= '0;
      count_q <= '0;
    end else begin
      if (flush) begin
        head_q  <= '0;
        tail_q  <= '0;
        count_q <= '0;
      end else begin
        unique case ({push_fire, pop_fire})
          2'b10: begin
            mem[tail_q] <= in_uop;
            tail_q <= ptr_inc(tail_q);
            count_q <= count_q + 1'b1;
          end
          2'b01: begin
            head_q <= ptr_inc(head_q);
            count_q <= count_q - 1'b1;
          end
          2'b11: begin
            mem[tail_q] <= in_uop;
            tail_q <= ptr_inc(tail_q);
            head_q <= ptr_inc(head_q);
          end
          default: begin
          end
        endcase
      end
    end
  end

endmodule : lsq

