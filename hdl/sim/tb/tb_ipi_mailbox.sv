`timescale 1ns/1ps

module tb_ipi_mailbox;
  localparam int unsigned CORES = 2;

  logic clk;
  logic rst_n;

  initial clk = 1'b0;
  always #5 clk = ~clk;

  initial begin
    rst_n = 1'b0;
    repeat (5) @(posedge clk);
    rst_n = 1'b1;
  end

  csr_if csr [CORES] (.clk(clk), .rst_n(rst_n));
  csr_bfm bfm0 (.clk(clk), .rst_n(rst_n), .csr(csr[0]));
  csr_bfm bfm1 (.clk(clk), .rst_n(rst_n), .csr(csr[1]));

  logic [CORES-1:0] ipi_irq;

  ipi_mailbox #(
      .CORES(CORES),
      .DATA_W(32),
      .FIFO_DEPTH(4)
  ) dut (
      .clk(clk),
      .rst_n(rst_n),
      .csr(csr),
      .ipi_irq(ipi_irq)
  );

  localparam logic [31:0] REG_SEND_MASK = 32'h0;
  localparam logic [31:0] REG_TX_DATA   = 32'h4;
  localparam logic [31:0] REG_RX_DATA   = 32'h8;

  initial begin
    logic fault;
    logic [31:0] rdata;
    wait(rst_n);

    // Core0 sends to Core1.
    bfm0.csr_write(REG_SEND_MASK, 32'h0000_0002, 4'hF, 2'b00, fault);
    if (fault) $fatal(1, "send_mask write fault");

    bfm0.csr_write(REG_TX_DATA, 32'hDEAD_BEEF, 4'hF, 2'b00, fault);
    if (fault) $fatal(1, "tx write fault");

    repeat (5) @(posedge clk);
    if (!ipi_irq[1]) $fatal(1, "expected ipi_irq[1] asserted");

    bfm1.csr_read(REG_RX_DATA, 2'b00, rdata, fault);
    if (fault) $fatal(1, "rx read fault");
    if (rdata !== 32'hDEAD_BEEF) $fatal(1, "rx data mismatch");

    repeat (2) @(posedge clk);
    if (ipi_irq[1]) $fatal(1, "expected ipi_irq[1] deasserted after pop");

    $display("tb_ipi_mailbox: PASS");
    $finish;
  end

endmodule

