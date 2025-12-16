// Project Carbon - eZ90 P7 core scaffold
// uop_queue: Generic ready/valid FIFO (used for uop buffering).

module uop_queue #(
    parameter int unsigned DEPTH = 16,
    parameter type T = logic [31:0]
) (
    input logic clk,
    input logic rst_n,

    input  logic in_valid,
    input  T     in_data,
    output logic in_ready,

    output logic out_valid,
    output T     out_data,
    input  logic out_ready,

    output logic [$clog2(DEPTH+1)-1:0] level
);
  localparam int unsigned PTR_W = (DEPTH < 2) ? 1 : $clog2(DEPTH);

  T mem [DEPTH];

  logic [PTR_W-1:0] head_q;
  logic [PTR_W-1:0] tail_q;
  logic [$clog2(DEPTH+1)-1:0] count_q;

  wire push_fire = in_valid && in_ready;
  wire pop_fire  = out_valid && out_ready;

  assign in_ready = (count_q != $clog2(DEPTH+1)'(DEPTH));
  assign out_valid = (count_q != '0);
  assign out_data  = mem[head_q];
  assign level     = count_q;

  function automatic logic [PTR_W-1:0] ptr_inc(input logic [PTR_W-1:0] p);
    if (DEPTH < 2) begin
      ptr_inc = '0;
    end else if (p == PTR_W'(DEPTH - 1)) begin
      ptr_inc = '0;
    end else begin
      ptr_inc = p + 1'b1;
    end
  endfunction

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      head_q  <= '0;
      tail_q  <= '0;
      count_q <= '0;
    end else begin
      unique case ({push_fire, pop_fire})
        2'b10: begin
          mem[tail_q] <= in_data;
          tail_q <= ptr_inc(tail_q);
          count_q <= count_q + 1'b1;
        end
        2'b01: begin
          head_q <= ptr_inc(head_q);
          count_q <= count_q - 1'b1;
        end
        2'b11: begin
          mem[tail_q] <= in_data;
          tail_q <= ptr_inc(tail_q);
          head_q <= ptr_inc(head_q);
        end
        default: begin
        end
      endcase
    end
  end

endmodule : uop_queue

