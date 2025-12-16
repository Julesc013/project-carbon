// Project Carbon - eZ90 P7 core scaffold
// fe_fetch: Fetch scaffolding (v1: sequential pc+4, no I$; uses icache_port hook).

module fe_fetch (
    input logic clk,
    input logic rst_n,

    input  logic        run_en,
    input  logic        redirect_valid,
    input  logic [63:0] redirect_pc,

    // I-cache port (hook)
    output logic        ic_req_valid,
    output logic [63:0] ic_req_pc,
    input  logic        ic_req_ready,

    input  logic        ic_rsp_valid,
    input  logic [63:0] ic_rsp_pc,
    input  logic [31:0] ic_rsp_inst,
    input  logic        ic_rsp_fault,
    output logic        ic_rsp_ready,

    // Output to decode
    output logic        inst_valid,
    output logic [63:0] inst_pc,
    output logic [31:0] inst_word,
    output logic        inst_fault,
    input  logic        inst_ready
);
  logic [63:0] pc_q;

  logic buf_valid_q;
  logic [63:0] buf_pc_q;
  logic [31:0] buf_inst_q;
  logic buf_fault_q;

  logic pending_q;
  logic [63:0] pending_pc_q;

  // Simple predictor stub (pc+4)
  logic [63:0] pred_pc;
  logic pred_taken;

  fe_bpred u_bpred (
      .pc(pc_q),
      .predicted_pc(pred_pc),
      .predicted_taken(pred_taken),
      .upd_valid(1'b0),
      .upd_pc('0),
      .upd_taken(1'b0),
      .upd_target('0)
  );

  assign ic_req_valid = run_en && !buf_valid_q && !pending_q;
  assign ic_req_pc    = pc_q;
  wire ic_req_fire = ic_req_valid && ic_req_ready;

  assign ic_rsp_ready = !buf_valid_q;
  wire ic_rsp_fire = ic_rsp_valid && ic_rsp_ready;

  assign inst_valid = buf_valid_q;
  assign inst_pc    = buf_pc_q;
  assign inst_word  = buf_inst_q;
  assign inst_fault = buf_fault_q;

  wire inst_fire = inst_valid && inst_ready;

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      pc_q <= 64'h0;
      buf_valid_q <= 1'b0;
      buf_pc_q <= '0;
      buf_inst_q <= '0;
      buf_fault_q <= 1'b0;
      pending_q <= 1'b0;
      pending_pc_q <= '0;
    end else begin
      if (redirect_valid) begin
        pc_q <= redirect_pc;
        buf_valid_q <= 1'b0;
        pending_q <= 1'b0;
      end else begin
        if (inst_fire) begin
          buf_valid_q <= 1'b0;
        end

        if (ic_req_fire) begin
          pending_q <= 1'b1;
          pending_pc_q <= pc_q;
        end

        if (ic_rsp_fire) begin
          pending_q <= 1'b0;
          buf_valid_q <= 1'b1;
          buf_pc_q <= ic_rsp_pc;
          buf_inst_q <= ic_rsp_inst;
          buf_fault_q <= ic_rsp_fault;
          pc_q <= pred_pc;
        end
      end
    end
  end

  wire _unused = pred_taken ^ pending_pc_q[0];

endmodule : fe_fetch

