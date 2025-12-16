// Project Carbon - eZ90 P7 core scaffold
// renamer: Stub renamer with architectural->physical map + monotonic allocator.

module renamer #(
    parameter int unsigned NUM_ARCH = 32,
    parameter int unsigned PREG_W   = 7
) (
    input logic clk,
    input logic rst_n,

    input  logic              flush,

    input  logic              in_valid,
    input  ez90_pkg::ez90_uop_t in_uop,
    output logic              in_ready,

    output logic                 out_valid,
    output ez90_pkg::ez90_uop_rn_t out_uop,
    input  logic                 out_ready
);
  import ez90_pkg::*;

  logic [PREG_W-1:0] map_q [NUM_ARCH];
  logic [PREG_W-1:0] next_preg_q;

  wire fire = in_valid && in_ready;

  assign in_ready  = out_ready;
  assign out_valid = in_valid;

  always_comb begin
    out_uop = '0;
    out_uop.uop = in_uop;
    out_uop.prs1 = map_q[in_uop.rs1];
    out_uop.prs2 = map_q[in_uop.rs2];
    out_uop.prd  = in_uop.rd_valid ? next_preg_q : '0;
  end

  always_ff @(posedge clk or negedge rst_n) begin
    int unsigned r;
    if (!rst_n) begin
      for (r = 0; r < NUM_ARCH; r++) begin
        map_q[r] <= PREG_W'(r);
      end
      next_preg_q <= PREG_W'(NUM_ARCH);
    end else begin
      if (flush) begin
        for (r = 0; r < NUM_ARCH; r++) begin
          map_q[r] <= PREG_W'(r);
        end
        next_preg_q <= PREG_W'(NUM_ARCH);
      end else if (fire) begin
        if (in_uop.rd_valid) begin
          map_q[in_uop.rd] <= next_preg_q;
          next_preg_q <= next_preg_q + 1'b1;
        end
      end
    end
  end

endmodule : renamer

