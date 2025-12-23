// Project Carbon - Z380 Platform
// z380_dram_refresh: Programmable refresh tick generator (placeholder model).

module z380_dram_refresh #(
    parameter logic [31:0] CSR_BASE = 32'h00a23000
) (
    input logic clk,
    input logic rst_n,
    output logic refresh_tick,
    output logic refresh_active,
    csr_if.slave csr
);
  import carbon_arch_pkg::*;

  localparam logic [31:0] CSR_CTRL   = CSR_BASE + 32'h0;
  localparam logic [31:0] CSR_PERIOD = CSR_BASE + 32'h4;
  localparam logic [31:0] CSR_PULSE  = CSR_BASE + 32'h8;
  localparam logic [31:0] CSR_STATUS = CSR_BASE + 32'hc;

  logic csr_rsp_valid_q;
  logic [31:0] csr_rsp_rdata_q;
  logic csr_rsp_fault_q;
  logic csr_rsp_side_q;

  logic enable_q;
  logic [15:0] period_q;
  logic [7:0] pulse_q;

  logic [15:0] period_cnt_q;
  logic [7:0] pulse_cnt_q;
  logic refresh_tick_q;

  assign csr.req_ready       = !csr_rsp_valid_q;
  assign csr.rsp_valid       = csr_rsp_valid_q;
  assign csr.rsp_rdata       = csr_rsp_rdata_q;
  assign csr.rsp_fault       = csr_rsp_fault_q;
  assign csr.rsp_side_effect = csr_rsp_side_q;

  wire csr_req_fire = csr.req_valid && csr.req_ready;
  wire csr_rsp_fire = csr.rsp_valid && csr.rsp_ready;

  assign refresh_tick = refresh_tick_q;
  assign refresh_active = (pulse_cnt_q != 0);

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      csr_rsp_valid_q <= 1'b0;
      csr_rsp_rdata_q <= '0;
      csr_rsp_fault_q <= 1'b0;
      csr_rsp_side_q  <= 1'b0;

      enable_q <= 1'b0;
      period_q <= 16'h0000;
      pulse_q  <= 8'h00;

      period_cnt_q <= 16'h0000;
      pulse_cnt_q  <= 8'h00;
      refresh_tick_q <= 1'b0;
    end else begin
      refresh_tick_q <= 1'b0;

      if (csr_rsp_fire) csr_rsp_valid_q <= 1'b0;

      if (enable_q) begin
        if (period_cnt_q == 16'h0000) begin
          period_cnt_q <= period_q;
          if (pulse_q != 8'h00) pulse_cnt_q <= pulse_q;
          refresh_tick_q <= 1'b1;
        end else begin
          period_cnt_q <= period_cnt_q - 16'h0001;
        end
      end else begin
        period_cnt_q <= period_q;
        pulse_cnt_q <= 8'h00;
      end

      if (pulse_cnt_q != 8'h00) begin
        pulse_cnt_q <= pulse_cnt_q - 8'h01;
      end

      if (csr_req_fire) begin
        csr_rsp_valid_q <= 1'b1;
        csr_rsp_fault_q <= 1'b0;
        csr_rsp_side_q  <= csr.req_write;
        csr_rsp_rdata_q <= '0;

        if (csr.req_addr == CSR_CTRL) begin
          if (!csr.req_write) begin
            csr_rsp_rdata_q[0] <= enable_q;
          end else begin
            enable_q <= csr.req_wdata[0];
          end
        end else if (csr.req_addr == CSR_PERIOD) begin
          if (!csr.req_write) begin
            csr_rsp_rdata_q[15:0] <= period_q;
          end else begin
            period_q <= csr.req_wdata[15:0];
          end
        end else if (csr.req_addr == CSR_PULSE) begin
          if (!csr.req_write) begin
            csr_rsp_rdata_q[7:0] <= pulse_q;
          end else begin
            pulse_q <= csr.req_wdata[7:0];
          end
        end else if (csr.req_addr == CSR_STATUS) begin
          if (!csr.req_write) begin
            csr_rsp_rdata_q[0] <= (pulse_cnt_q != 0);
            csr_rsp_rdata_q[1] <= refresh_tick_q;
            csr_rsp_rdata_q[15:8] <= pulse_cnt_q;
            csr_rsp_rdata_q[31:16] <= period_cnt_q;
          end else begin
            csr_rsp_fault_q <= 1'b1;
          end
        end else begin
          csr_rsp_fault_q <= 1'b1;
        end
      end
    end
  end

  wire _unused = ^{csr.req_wdata, csr.req_wstrb};

endmodule : z380_dram_refresh
