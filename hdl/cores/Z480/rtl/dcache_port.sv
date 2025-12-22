// Project Carbon - Z480 P7 core scaffold
// dcache_port: Data cache hook interface (no cache implemented in v1).

module dcache_port (
    input logic clk,
    input logic rst_n,

    input  logic        req_valid,
    input  logic        req_write,
    input  logic [63:0] req_addr,
    input  logic [63:0] req_wdata,
    input  logic [7:0]  req_wstrb,
    output logic        req_ready,

    output logic        rsp_valid,
    output logic [63:0] rsp_rdata,
    output logic        rsp_fault,
    input  logic        rsp_ready
);
  // v1: stub accepts one request and returns zeros.
  logic hold_q;

  assign req_ready = !hold_q;
  wire req_fire = req_valid && req_ready;

  assign rsp_valid = hold_q;
  assign rsp_rdata = 64'h0;
  assign rsp_fault = 1'b0;
  wire rsp_fire = rsp_valid && rsp_ready;

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      hold_q <= 1'b0;
    end else begin
      if (rsp_fire) hold_q <= 1'b0;
      if (req_fire) hold_q <= 1'b1;
    end
  end

  wire _unused = ^{req_write, req_addr[0], req_wdata[0], req_wstrb[0]};

endmodule : dcache_port
