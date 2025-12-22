// Project Carbon - Z480 P7 core scaffold
// fe_icache_port: Front-end I$ hook port (v1: no cache, no memory; returns 0s).

module fe_icache_port (
    input logic clk,
    input logic rst_n,

    input  logic        req_valid,
    input  logic [63:0] req_pc,
    output logic        req_ready,

    output logic        rsp_valid,
    output logic [63:0] rsp_pc,
    output logic [31:0] rsp_inst,
    output logic        rsp_fault,
    input  logic        rsp_ready
);
  logic hold_q;
  logic [63:0] pc_q;

  assign req_ready = !hold_q;
  assign rsp_valid = hold_q;
  assign rsp_pc    = pc_q;
  assign rsp_inst  = 32'h0000_0000;
  assign rsp_fault = 1'b0;

  wire req_fire = req_valid && req_ready;
  wire rsp_fire = rsp_valid && rsp_ready;

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      hold_q <= 1'b0;
      pc_q   <= '0;
    end else begin
      if (rsp_fire) begin
        hold_q <= 1'b0;
      end
      if (req_fire) begin
        hold_q <= 1'b1;
        pc_q   <= req_pc;
      end
    end
  end

endmodule : fe_icache_port
