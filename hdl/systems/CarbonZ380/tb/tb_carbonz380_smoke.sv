`timescale 1ns/1ps

module tb_carbonz380_smoke;
  import carbon_arch_pkg::*;

  logic clk;
  logic rst_n;

  logic [31:0] signature;
  logic poweroff;

  initial clk = 1'b0;
  always #5 clk = ~clk;

  initial begin
    rst_n = 1'b0;
    repeat (10) @(posedge clk);
    rst_n = 1'b1;
  end

  carbonz380_top dut (
      .clk(clk),
      .rst_n(rst_n),
      .signature(signature),
      .poweroff(poweroff)
  );

  localparam logic [31:0] EXP_SIG = 32'h3038_335A; // "Z380" little-endian
  localparam logic [31:0] EXP_CAUSE = 32'h0000_0001;
  localparam logic [31:0] EXP_EPC = 32'h0000_0031;

  int unsigned cycles;
  initial begin
    wait(rst_n);
    cycles = 0;
    while (!poweroff && (cycles < 400000)) begin
      @(posedge clk);
      cycles++;
    end
    if (!poweroff) $fatal(1, "tb_carbonz380_smoke: timeout waiting for poweroff");
    if (signature !== EXP_SIG) begin
      $fatal(1, "tb_carbonz380_smoke: signature mismatch exp=%08x got=%08x", EXP_SIG, signature);
    end
    repeat (20) @(posedge clk);
    if (dut.u_cpu.csr_cause_q !== EXP_CAUSE) begin
      $fatal(1, "tb_carbonz380_smoke: trap cause mismatch exp=%08x got=%08x",
             EXP_CAUSE, dut.u_cpu.csr_cause_q);
    end
    if (dut.u_cpu.csr_epc_q !== EXP_EPC) begin
      $fatal(1, "tb_carbonz380_smoke: trap epc mismatch exp=%08x got=%08x",
             EXP_EPC, dut.u_cpu.csr_epc_q);
    end
    $display("tb_carbonz380_smoke: PASS");
    $finish;
  end

endmodule
