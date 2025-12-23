// Project Carbon - Z380 Platform
// z380_waitgen: Wait-state generator with programmable profiles.

module z380_waitgen #(
    parameter int unsigned PROFILE_COUNT = 8,
    parameter int unsigned COUNT_W = 8,
    parameter int unsigned INDEX_W = (PROFILE_COUNT < 2) ? 1 : $clog2(PROFILE_COUNT),
    parameter logic [31:0] CSR_BASE = 32'h00a22000
) (
    input logic clk,
    input logic rst_n,
    input logic req_valid,
    input logic [INDEX_W-1:0] req_profile,
    output logic req_ready,
    output logic wait_active,
    output logic wait_done,
    csr_if.slave csr
);
  import carbon_arch_pkg::*;

  logic csr_rsp_valid_q;
  logic [31:0] csr_rsp_rdata_q;
  logic csr_rsp_fault_q;
  logic csr_rsp_side_q;

  logic [COUNT_W-1:0] profile_wait_q [PROFILE_COUNT];
  logic [COUNT_W-1:0] wait_ctr_q;
  logic wait_done_q;

  assign csr.req_ready       = !csr_rsp_valid_q;
  assign csr.rsp_valid       = csr_rsp_valid_q;
  assign csr.rsp_rdata       = csr_rsp_rdata_q;
  assign csr.rsp_fault       = csr_rsp_fault_q;
  assign csr.rsp_side_effect = csr_rsp_side_q;

  wire csr_req_fire = csr.req_valid && csr.req_ready;
  wire csr_rsp_fire = csr.rsp_valid && csr.rsp_ready;

  assign req_ready = (wait_ctr_q == '0);
  assign wait_active = (wait_ctr_q != '0);
  assign wait_done = wait_done_q;

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      int i;
      csr_rsp_valid_q <= 1'b0;
      csr_rsp_rdata_q <= '0;
      csr_rsp_fault_q <= 1'b0;
      csr_rsp_side_q  <= 1'b0;
      wait_ctr_q <= '0;
      wait_done_q <= 1'b0;
      for (i = 0; i < int'(PROFILE_COUNT); i++) begin
        profile_wait_q[i] <= '0;
      end
    end else begin
      int i;
      wait_done_q <= 1'b0;

      if (csr_rsp_fire) csr_rsp_valid_q <= 1'b0;

      if (req_valid && req_ready) begin
        wait_ctr_q <= profile_wait_q[req_profile];
        if (profile_wait_q[req_profile] == '0) wait_done_q <= 1'b1;
      end else if (wait_ctr_q != '0) begin
        wait_ctr_q <= wait_ctr_q - COUNT_W'(1);
        if (wait_ctr_q == COUNT_W'(1)) begin
          wait_done_q <= 1'b1;
        end
      end

      if (csr_req_fire) begin
        logic hit;
        csr_rsp_valid_q <= 1'b1;
        csr_rsp_fault_q <= 1'b0;
        csr_rsp_side_q  <= csr.req_write;
        csr_rsp_rdata_q <= '0;
        hit = 1'b0;
        for (i = 0; i < int'(PROFILE_COUNT); i++) begin
          if (csr.req_addr == (CSR_BASE + 32'(i * 4))) begin
            hit = 1'b1;
            if (!csr.req_write) csr_rsp_rdata_q[COUNT_W-1:0] <= profile_wait_q[i];
            else profile_wait_q[i] <= csr.req_wdata[COUNT_W-1:0];
          end
        end
        if (!hit) csr_rsp_fault_q <= 1'b1;
      end
    end
  end

  wire _unused = ^{csr.req_wdata, csr.req_wstrb};

endmodule : z380_waitgen
