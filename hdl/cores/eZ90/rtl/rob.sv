// Project Carbon - eZ90 P7 core scaffold
// rob: Reorder buffer skeleton (allocate, complete, commit pointers).

module rob #(
    parameter int unsigned DEPTH = 64
) (
    input logic clk,
    input logic rst_n,

    input  logic flush,

    // Allocate
    input  logic                  alloc_valid,
    input  ez90_pkg::ez90_uop_rn_t alloc_uop,
    output logic                  alloc_ready,
    output logic [5:0]            alloc_idx,

    // Writeback/complete
    input  logic           wb_valid,
    input  ez90_pkg::ez90_wb_t wb,
    output logic           wb_ready,

    // Head for commit
    output logic                  head_valid,
    output logic                  head_done,
    output ez90_pkg::ez90_uop_rn_t head_uop,
    output logic [5:0]            head_idx,
    output logic                  head_has_trap,
    output logic [31:0]           head_trap_cause,

    input  logic                  head_pop
);
  import ez90_pkg::*;

  localparam int unsigned IDX_W = 6;
  localparam int unsigned COUNT_W = $clog2(DEPTH + 1);

`ifndef SYNTHESIS
  initial begin
    if (DEPTH < 2 || DEPTH > 64) $fatal(1, "rob: DEPTH must be in [2,64]");
  end
`endif

  ez90_uop_rn_t uop_mem   [DEPTH];
  logic         valid_mem [DEPTH];
  logic         done_mem  [DEPTH];
  logic         trap_mem  [DEPTH];
  logic [31:0]  cause_mem [DEPTH];

  logic [IDX_W-1:0] head_q;
  logic [IDX_W-1:0] tail_q;
  logic [COUNT_W-1:0] count_q;

  assign alloc_ready = (count_q != COUNT_W'(DEPTH));
  assign alloc_idx   = tail_q;
  assign wb_ready    = 1'b1;

  wire alloc_fire = alloc_valid && alloc_ready;
  wire pop_fire   = head_pop && head_valid;

  function automatic logic [IDX_W-1:0] ptr_inc(input logic [IDX_W-1:0] p);
    if (p == IDX_W'(DEPTH - 1)) ptr_inc = '0;
    else ptr_inc = p + 1'b1;
  endfunction

  always_comb begin
    head_valid = (count_q != '0);
    head_idx   = head_q;
    head_uop   = uop_mem[head_q];
    head_done  = done_mem[head_q];
    head_has_trap = trap_mem[head_q];
    head_trap_cause = cause_mem[head_q];
  end

  always_ff @(posedge clk or negedge rst_n) begin
    int unsigned i;
    if (!rst_n) begin
      head_q <= '0;
      tail_q <= '0;
      count_q <= '0;
      for (i = 0; i < DEPTH; i++) begin
        valid_mem[i] <= 1'b0;
        done_mem[i]  <= 1'b0;
        trap_mem[i]  <= 1'b0;
        cause_mem[i] <= '0;
        uop_mem[i]   <= '0;
      end
    end else begin
      if (flush) begin
        head_q <= '0;
        tail_q <= '0;
        count_q <= '0;
        for (i = 0; i < DEPTH; i++) begin
          valid_mem[i] <= 1'b0;
          done_mem[i]  <= 1'b0;
          trap_mem[i]  <= 1'b0;
          cause_mem[i] <= '0;
        end
      end else begin
        logic [IDX_W-1:0] head_n;
        logic [IDX_W-1:0] tail_n;
        logic [COUNT_W-1:0] count_n;

        head_n  = head_q;
        tail_n  = tail_q;
        count_n = count_q;

        if (alloc_fire) begin
          valid_mem[tail_q] <= 1'b1;
          done_mem[tail_q]  <= 1'b0;
          trap_mem[tail_q]  <= 1'b0;
          cause_mem[tail_q] <= '0;
          uop_mem[tail_q]   <= alloc_uop;
          tail_n  = ptr_inc(tail_q);
          count_n = count_n + 1'b1;
        end

        if (wb_valid) begin
          int unsigned widx;
          widx = int'(wb.rob_idx);
          if (widx < DEPTH) begin
            if (valid_mem[widx]) begin
              done_mem[widx] <= 1'b1;
            end
          end
        end

        if (pop_fire) begin
          valid_mem[head_q] <= 1'b0;
          done_mem[head_q]  <= 1'b0;
          trap_mem[head_q]  <= 1'b0;
          cause_mem[head_q] <= '0;
          head_n  = ptr_inc(head_q);
          count_n = count_n - 1'b1;
        end

        head_q  <= head_n;
        tail_q  <= tail_n;
        count_q <= count_n;
      end
    end
  end

endmodule : rob
