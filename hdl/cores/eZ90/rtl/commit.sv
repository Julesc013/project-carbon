// Project Carbon - eZ90 P7 core scaffold
// commit: Commit/retire skeleton (in-order retirement from ROB head).

module commit (
    input logic clk,
    input logic rst_n,

    input  logic retire_en,

    input  logic                  rob_head_valid,
    input  logic                  rob_head_done,
    input  ez90_pkg::ez90_uop_rn_t rob_head_uop,
    input  logic [5:0]            rob_head_idx,
    input  logic                  rob_head_has_trap,
    input  logic [31:0]           rob_head_trap_cause,

    output logic                  rob_head_pop,

    output logic                  commit_valid,
    output ez90_pkg::ez90_commit_evt_t commit_evt,
    output logic [63:0]           retired_count
);
  import ez90_pkg::*;

  logic [63:0] retired_q;

  wire can_commit = retire_en && rob_head_valid && rob_head_done;
  assign rob_head_pop  = can_commit;
  assign commit_valid  = can_commit;

  always_comb begin
    commit_evt = '0;
    commit_evt.rob_idx = rob_head_idx;
    commit_evt.pc = rob_head_uop.uop.pc;
    commit_evt.has_trap = rob_head_has_trap;
    commit_evt.trap_cause = rob_head_trap_cause;
    commit_evt.trap_epc = rob_head_uop.uop.pc;
  end

  assign retired_count = retired_q;

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      retired_q <= 64'h0;
    end else begin
      if (commit_valid && !rob_head_has_trap) begin
        retired_q <= retired_q + 1'b1;
      end
    end
  end

endmodule : commit

