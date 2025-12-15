`timescale 1ns/1ps

module tb_irq_ctrl;
  import carbon_arch_pkg::*;

  localparam int unsigned N_SOURCES = 8;

  logic clk;
  logic rst_n;

  initial clk = 1'b0;
  always #5 clk = ~clk;

  initial begin
    rst_n = 1'b0;
    repeat (5) @(posedge clk);
    rst_n = 1'b1;
  end

  csr_if csr (.clk(clk), .rst_n(rst_n));
  csr_bfm bfm (.clk(clk), .rst_n(rst_n), .csr(csr));

  irq_if #(.N(N_SOURCES)) irq_out [1] (.clk(clk), .rst_n(rst_n));

  logic [0:0][N_SOURCES-1:0] irq_in;
  logic [0:0] ipi_in;
  logic [0:0] timer_tick;

  irq_ctrl_simple #(
      .N_SOURCES(N_SOURCES),
      .M_TARGETS(1)
  ) dut (
      .clk(clk),
      .rst_n(rst_n),
      .csr(csr),
      .irq_in(irq_in),
      .ipi_in(ipi_in),
      .timer_tick(timer_tick),
      .irq_out(irq_out)
  );

  initial begin
    irq_in = '0;
    ipi_in = '0;
    timer_tick = '0;
    irq_out[0].irq_ack = 1'b0;
    irq_out[0].irq_ack_vector = '0;
  end

  initial begin
    logic fault;
    logic [31:0] rdata;
    wait(rst_n);

    // Enable vector 3 (requires privileged access).
    bfm.csr_write(CARBON_CSR_IE, 32'h0000_0008, 4'hF, 2'b01, fault);
    if (fault) $fatal(1, "enable write fault");

    // Raise IRQ3 for one cycle.
    @(posedge clk);
    irq_in[0][3] = 1'b1;
    @(posedge clk);
    irq_in[0][3] = 1'b0;

    // Wait until presented.
    repeat (20) @(posedge clk);
    if (!irq_out[0].irq_valid) $fatal(1, "irq_valid not asserted");
    if (irq_out[0].irq_vector != 3) $fatal(1, "irq_vector exp=3 got=%0d", irq_out[0].irq_vector);

    // Pending CSR should show bit 3 set.
    bfm.csr_read(CARBON_CSR_IP, 2'b01, rdata, fault);
    if (fault) $fatal(1, "pending read fault");
    if ((rdata & 32'h8) == 0) $fatal(1, "pending bit not set");

    // Ack IRQ3.
    irq_out[0].irq_ack = 1'b1;
    irq_out[0].irq_ack_vector = 3;
    @(posedge clk);
    irq_out[0].irq_ack = 1'b0;

    repeat (5) @(posedge clk);
    if (irq_out[0].irq_valid) $fatal(1, "irq_valid should clear after ack");

    bfm.csr_read(CARBON_CSR_IP, 2'b01, rdata, fault);
    if (fault) $fatal(1, "pending read fault");
    if ((rdata & 32'h8) != 0) $fatal(1, "pending bit should clear after ack");

    // Privilege fault (U-mode)
    bfm.csr_read(CARBON_CSR_IP, 2'b00, rdata, fault);
    if (!fault) $fatal(1, "expected privilege fault");

    $display("tb_irq_ctrl: PASS");
    $finish;
  end

endmodule

