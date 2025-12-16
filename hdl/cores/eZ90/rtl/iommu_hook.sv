// Project Carbon - eZ90 P7 core scaffold
// iommu_hook: Placeholder IOMMU integration hook for future DMA/capability enforcement.

module iommu_hook (
    input logic clk,
    input logic rst_n,

    input  logic        req_valid,
    input  logic [63:0] req_iova,
    output logic        req_ready,

    output logic        rsp_valid,
    output logic [63:0] rsp_pa,
    output logic        rsp_fault,
    input  logic        rsp_ready
);
  logic hold_q;
  logic [63:0] iova_q;

  assign req_ready = !hold_q;
  wire req_fire = req_valid && req_ready;

  assign rsp_valid = hold_q;
  assign rsp_pa    = iova_q;
  assign rsp_fault = 1'b0;
  wire rsp_fire = rsp_valid && rsp_ready;

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      hold_q <= 1'b0;
      iova_q <= 64'h0;
    end else begin
      if (rsp_fire) hold_q <= 1'b0;
      if (req_fire) begin
        hold_q <= 1'b1;
        iova_q <= req_iova;
      end
    end
  end

endmodule : iommu_hook

