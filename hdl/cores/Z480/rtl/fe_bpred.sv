// Project Carbon - Z480 P7 core scaffold
// fe_bpred: Branch predictor stub (v1: always not-taken, pc+4).

module fe_bpred (
    input  logic [63:0] pc,
    output logic [63:0] predicted_pc,
    output logic        predicted_taken,

    // Future update channel (commit/redirect feedback)
    input  logic        upd_valid,
    input  logic [63:0] upd_pc,
    input  logic        upd_taken,
    input  logic [63:0] upd_target
);
  always_comb begin
    predicted_taken = 1'b0;
    predicted_pc    = pc + 64'd4;
  end

  // v1 stub ignores updates.
  wire _unused = upd_valid ^ upd_pc[0] ^ upd_taken ^ upd_target[0];

endmodule : fe_bpred
