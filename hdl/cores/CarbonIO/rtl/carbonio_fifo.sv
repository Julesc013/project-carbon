// Project Carbon - CarbonIO peripheral
// carbonio_fifo: Simple synchronous FIFO (single clock, single push/pop per cycle).

module carbonio_fifo #(
    parameter int unsigned WIDTH = 8,
    parameter int unsigned DEPTH = 16
) (
    input  logic clk,
    input  logic rst_n,
    input  logic push,
    input  logic [WIDTH-1:0] push_data,
    input  logic pop,
    output logic [WIDTH-1:0] pop_data,
    output logic full,
    output logic empty,
    output logic [$clog2(DEPTH+1)-1:0] count
);
  localparam int unsigned PTR_W = (DEPTH <= 1) ? 1 : $clog2(DEPTH);

  logic [WIDTH-1:0] mem [DEPTH];
  logic [PTR_W-1:0] wr_ptr_q;
  logic [PTR_W-1:0] rd_ptr_q;
  logic [$clog2(DEPTH+1)-1:0] count_q;

  assign full  = (count_q == DEPTH[$clog2(DEPTH+1)-1:0]);
  assign empty = (count_q == 0);
  assign count = count_q;

  wire push_ok = push && !full;
  wire pop_ok  = pop && !empty;

  function automatic logic [PTR_W-1:0] ptr_next(input logic [PTR_W-1:0] ptr);
    if (DEPTH <= 1) begin
      ptr_next = '0;
    end else if (ptr == PTR_W'(DEPTH - 1)) begin
      ptr_next = '0;
    end else begin
      ptr_next = ptr + PTR_W'(1);
    end
  endfunction

  assign pop_data = mem[rd_ptr_q];

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      wr_ptr_q <= '0;
      rd_ptr_q <= '0;
      count_q  <= '0;
    end else begin
      if (push_ok) begin
        mem[wr_ptr_q] <= push_data;
        wr_ptr_q <= ptr_next(wr_ptr_q);
      end
      if (pop_ok) begin
        rd_ptr_q <= ptr_next(rd_ptr_q);
      end

      unique case ({push_ok, pop_ok})
        2'b10: count_q <= count_q + 1'b1;
        2'b01: count_q <= count_q - 1'b1;
        default: count_q <= count_q;
      endcase
    end
  end

endmodule : carbonio_fifo
