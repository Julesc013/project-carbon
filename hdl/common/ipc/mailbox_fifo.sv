// Project Carbon - Common Infrastructure
// mailbox_fifo: Small ready/valid FIFO used by IPC blocks.

module mailbox_fifo #(
    parameter int unsigned WIDTH = 32,
    parameter int unsigned DEPTH = 4
) (
    input logic clk,
    input logic rst_n,

    input  logic             push_valid,
    output logic             push_ready,
    input  logic [WIDTH-1:0] push_data,

    output logic             pop_valid,
    input  logic             pop_ready,
    output logic [WIDTH-1:0] pop_data,

    output logic almost_full,
    output logic almost_empty
);
  localparam int unsigned PTR_W = (DEPTH <= 1) ? 1 : $clog2(DEPTH);
  localparam int unsigned CNT_W = $clog2(DEPTH + 1);

  logic [WIDTH-1:0] mem [DEPTH];
  logic [PTR_W-1:0] wr_ptr_q, rd_ptr_q;
  logic [CNT_W-1:0] count_q;

  function automatic logic [PTR_W-1:0] inc_ptr(input logic [PTR_W-1:0] ptr);
    if (ptr == PTR_W'(DEPTH - 1)) inc_ptr = '0;
    else inc_ptr = ptr + 1'b1;
  endfunction

  assign push_ready = (count_q < CNT_W'(DEPTH));
  assign pop_valid  = (count_q != '0);
  assign pop_data   = mem[rd_ptr_q];

  assign almost_full  = (count_q >= CNT_W'(DEPTH - 1));
  assign almost_empty = (count_q <= CNT_W'(1));

  wire push_fire = push_valid && push_ready;
  wire pop_fire  = pop_valid && pop_ready;

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      wr_ptr_q <= '0;
      rd_ptr_q <= '0;
      count_q  <= '0;
    end else begin
      unique case ({push_fire, pop_fire})
        2'b10: begin
          mem[wr_ptr_q] <= push_data;
          wr_ptr_q      <= inc_ptr(wr_ptr_q);
          count_q       <= count_q + 1'b1;
        end
        2'b01: begin
          rd_ptr_q <= inc_ptr(rd_ptr_q);
          count_q  <= count_q - 1'b1;
        end
        2'b11: begin
          mem[wr_ptr_q] <= push_data;
          wr_ptr_q      <= inc_ptr(wr_ptr_q);
          rd_ptr_q      <= inc_ptr(rd_ptr_q);
          count_q       <= count_q;
        end
        default: begin
          count_q <= count_q;
        end
      endcase
    end
  end

endmodule : mailbox_fifo

