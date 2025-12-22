`define CARBON_ENABLE_SVA
`timescale 1ns/1ps

module csr_stub (
    input logic clk,
    input logic rst_n,
    csr_if.slave csr
);
  localparam logic [31:0] CSR_RW_ADDR = 32'h0000_0100;
  localparam logic [31:0] CSR_RO_ADDR = 32'h0000_0104;
  localparam logic [31:0] CSR_WO_ADDR = 32'h0000_0108;

  logic [31:0] reg_rw_q;
  logic [31:0] reg_wo_q;

  logic        rsp_valid_q;
  logic [31:0] rsp_rdata_q;
  logic        rsp_fault_q;
  logic        rsp_side_q;

  assign csr.req_ready = !rsp_valid_q;
  assign csr.rsp_valid = rsp_valid_q;
  assign csr.rsp_rdata = rsp_rdata_q;
  assign csr.rsp_fault = rsp_fault_q;
  assign csr.rsp_side_effect = rsp_side_q;

  wire req_fire = csr.req_valid && csr.req_ready;
  wire rsp_fire = csr.rsp_valid && csr.rsp_ready;

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      reg_rw_q    <= 32'h0000_0000;
      reg_wo_q    <= 32'h0000_0000;
      rsp_valid_q <= 1'b0;
      rsp_rdata_q <= '0;
      rsp_fault_q <= 1'b0;
      rsp_side_q  <= 1'b0;
    end else begin
      if (rsp_fire) begin
        rsp_valid_q <= 1'b0;
      end

      if (req_fire) begin
        rsp_valid_q <= 1'b1;
        rsp_rdata_q <= '0;
        rsp_fault_q <= 1'b0;
        rsp_side_q  <= csr.req_write;

        unique case (csr.req_addr)
          CSR_RW_ADDR: begin
            if (csr.req_priv < 2'(1)) begin
              rsp_fault_q <= 1'b1;
            end else if (csr.req_write) begin
              reg_rw_q <= csr.req_wdata;
            end else begin
              rsp_rdata_q <= reg_rw_q;
            end
          end
          CSR_RO_ADDR: begin
            if (csr.req_write) begin
              rsp_fault_q <= 1'b1;
            end else begin
              rsp_rdata_q <= 32'hCAFE_0001;
            end
          end
          CSR_WO_ADDR: begin
            if (csr.req_write) begin
              reg_wo_q <= csr.req_wdata;
            end else begin
              rsp_fault_q <= 1'b1;
            end
          end
          default: begin
            rsp_fault_q <= 1'b1;
          end
        endcase
      end
    end
  end
endmodule

module tb_csr_contract;
  import carbon_arch_pkg::*;

  logic clk;
  logic rst_n;

  clock_reset_bfm #(
      .CLK_PERIOD(10ns),
      .RESET_CYCLES(4)
  ) clk_rst (
      .clk(clk),
      .rst_n(rst_n)
  );

  initial begin
    clk_rst.apply_reset();
  end

  csr_if csr (.clk(clk), .rst_n(rst_n));
  csr_bfm bfm (.clk(clk), .rst_n(rst_n), .csr(csr));

  localparam logic [31:0] CSR_RW_ADDR = 32'h0000_0100;
  localparam logic [31:0] CSR_RO_ADDR = 32'h0000_0104;
  localparam logic [31:0] CSR_WO_ADDR = 32'h0000_0108;

  csr_stub dut (
      .clk(clk),
      .rst_n(rst_n),
      .csr(csr)
  );

  initial begin
    logic [31:0] rdata;
    logic fault;

    wait (rst_n);

    // RW write/read with supervisor privilege.
    bfm.csr_write(CSR_RW_ADDR, 32'h1234_5678, 4'hF, 2'b01, fault);
    if (fault) $fatal(1, "RW write fault");
    bfm.csr_read(CSR_RW_ADDR, 2'b01, rdata, fault);
    if (fault) $fatal(1, "RW read fault");
    if (rdata != 32'h1234_5678) $fatal(1, "RW read mismatch");

    // RW write should fault for user privilege.
    bfm.csr_write(CSR_RW_ADDR, 32'hAAAA_5555, 4'hF, 2'b00, fault);
    if (!fault) $fatal(1, "expected privilege fault");

    // RO read ok, write faults.
    bfm.csr_read(CSR_RO_ADDR, 2'b00, rdata, fault);
    if (fault) $fatal(1, "RO read fault");
    if (rdata != 32'hCAFE_0001) $fatal(1, "RO read mismatch");
    bfm.csr_write(CSR_RO_ADDR, 32'hDEAD_BEEF, 4'hF, 2'b01, fault);
    if (!fault) $fatal(1, "expected RO write fault");

    // WO write ok, read faults.
    bfm.csr_write(CSR_WO_ADDR, 32'h0BAD_F00D, 4'hF, 2'b01, fault);
    if (fault) $fatal(1, "WO write fault");
    bfm.csr_read(CSR_WO_ADDR, 2'b01, rdata, fault);
    if (!fault) $fatal(1, "expected WO read fault");

    $display("tb_csr_contract: PASS");
    $finish;
  end

endmodule
