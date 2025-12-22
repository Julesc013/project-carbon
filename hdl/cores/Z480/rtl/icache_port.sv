// Project Carbon - Z480 P7 core scaffold
// icache_port: Instruction cache hook interface (no cache implemented in v1).

module icache_port (
    input logic clk,
    input logic rst_n,

    input  logic        req_valid,
    input  logic [63:0] req_addr,
    output logic        req_ready,

    output logic        rsp_valid,
    output logic [63:0] rsp_addr,
    output logic [31:0] rsp_inst,
    output logic        rsp_fault,
    input  logic        rsp_ready
);
  // v1: stub returns zeros with 1-deep buffering.
  logic hold_q;
  logic [63:0] addr_q;

  assign req_ready = !hold_q;
  wire req_fire = req_valid && req_ready;

  assign rsp_valid = hold_q;
  assign rsp_addr  = addr_q;
  assign rsp_inst  = 32'h0000_0000;
  assign rsp_fault = 1'b0;
  wire rsp_fire = rsp_valid && rsp_ready;

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      hold_q <= 1'b0;
      addr_q <= 64'h0;
    end else begin
      if (rsp_fire) hold_q <= 1'b0;
      if (req_fire) begin
        hold_q <= 1'b1;
        addr_q <= req_addr;
      end
    end
  end

endmodule : icache_port
