// Project Carbon - Z380 Platform
// z380_chipselect: Programmable chip-select decoder with wait profile metadata.

module z380_chipselect #(
    parameter int unsigned ADDR_W = 32,
    parameter int unsigned RANGE_COUNT = 4,
    parameter int unsigned INDEX_W = (RANGE_COUNT < 2) ? 1 : $clog2(RANGE_COUNT),
    parameter logic [31:0] CSR_BASE = 32'h00a21000
) (
    input logic clk,
    input logic rst_n,
    input logic addr_valid,
    input logic [ADDR_W-1:0] addr,
    output logic [RANGE_COUNT-1:0] cs_match,
    output logic cs_any,
    output logic [3:0] cs_wait_profile,
    output logic [INDEX_W-1:0] cs_index,
    csr_if.slave csr
);
  import carbon_arch_pkg::*;

  localparam int unsigned CSR_STRIDE = 16;

  logic csr_rsp_valid_q;
  logic [31:0] csr_rsp_rdata_q;
  logic csr_rsp_fault_q;
  logic csr_rsp_side_q;

  logic [ADDR_W-1:0] base_q [RANGE_COUNT];
  logic [ADDR_W-1:0] mask_q [RANGE_COUNT];
  logic [3:0] wait_q [RANGE_COUNT];

  assign csr.req_ready       = !csr_rsp_valid_q;
  assign csr.rsp_valid       = csr_rsp_valid_q;
  assign csr.rsp_rdata       = csr_rsp_rdata_q;
  assign csr.rsp_fault       = csr_rsp_fault_q;
  assign csr.rsp_side_effect = csr_rsp_side_q;

  wire csr_req_fire = csr.req_valid && csr.req_ready;
  wire csr_rsp_fire = csr.rsp_valid && csr.rsp_ready;

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      int i;
      csr_rsp_valid_q <= 1'b0;
      csr_rsp_rdata_q <= '0;
      csr_rsp_fault_q <= 1'b0;
      csr_rsp_side_q  <= 1'b0;
      for (i = 0; i < int'(RANGE_COUNT); i++) begin
        base_q[i] <= '0;
        mask_q[i] <= '0;
        wait_q[i] <= 4'h0;
      end
    end else begin
      if (csr_rsp_fire) csr_rsp_valid_q <= 1'b0;

      if (csr_req_fire) begin
        int i;
        logic hit;
        csr_rsp_valid_q <= 1'b1;
        csr_rsp_fault_q <= 1'b0;
        csr_rsp_side_q  <= csr.req_write;
        csr_rsp_rdata_q <= '0;
        hit = 1'b0;

        for (i = 0; i < int'(RANGE_COUNT); i++) begin
          logic [31:0] base_addr;
          base_addr = CSR_BASE + 32'(i * CSR_STRIDE);
          if (csr.req_addr == base_addr) begin
            hit = 1'b1;
            if (!csr.req_write) csr_rsp_rdata_q <= 32'(base_q[i]);
            else base_q[i] <= ADDR_W'(csr.req_wdata);
          end else if (csr.req_addr == (base_addr + 32'h4)) begin
            hit = 1'b1;
            if (!csr.req_write) csr_rsp_rdata_q <= 32'(mask_q[i]);
            else mask_q[i] <= ADDR_W'(csr.req_wdata);
          end else if (csr.req_addr == (base_addr + 32'h8)) begin
            hit = 1'b1;
            if (!csr.req_write) csr_rsp_rdata_q[3:0] <= wait_q[i];
            else wait_q[i] <= csr.req_wdata[3:0];
          end
        end

        if (!hit) csr_rsp_fault_q <= 1'b1;
      end
    end
  end

  always_comb begin
    int i;
    cs_match = '0;
    cs_any = 1'b0;
    cs_index = '0;
    cs_wait_profile = 4'h0;
    for (i = 0; i < int'(RANGE_COUNT); i++) begin
      if (addr_valid &&
          (mask_q[i] != '0) &&
          ((addr & mask_q[i]) == (base_q[i] & mask_q[i]))) begin
        cs_match[i] = 1'b1;
        if (!cs_any) begin
          cs_any = 1'b1;
          cs_index = INDEX_W'(i);
          cs_wait_profile = wait_q[i];
        end
      end
    end
  end

  wire _unused = ^{csr.req_wdata, csr.req_wstrb};

endmodule : z380_chipselect
