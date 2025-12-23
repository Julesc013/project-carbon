`timescale 1ns/1ps

module tb_carbonz480_smoke;
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

  carbonz480_top dut (
      .clk(clk),
      .rst_n(rst_n),
      .signature(signature),
      .poweroff(poweroff)
  );

  localparam logic [31:0] EXP_SIG = 32'h3038_345A; // "Z480" little-endian
  localparam logic [7:0] TIER_P0 = 8'(CARBON_Z80_DERIVED_TIER_P0_I8080);
  localparam logic [7:0] TIER_P7 = 8'(CARBON_Z80_DERIVED_TIER_P7_Z480);
  localparam logic [1:0] CORE_Z480 = 2'd3;

  int unsigned cycles;
  initial begin
    wait(rst_n);
    if (dut.host_active_tier !== TIER_P0) begin
      $fatal(1, "tb_carbonz480_smoke: reset tier mismatch exp=%0d got=%0d",
             TIER_P0, dut.host_active_tier);
    end

    cycles = 0;
    while ((dut.host_active_tier !== TIER_P7) && (cycles < 2000)) begin
      @(posedge clk);
      cycles++;
    end
    if (dut.host_active_tier !== TIER_P7) begin
      $fatal(1, "tb_carbonz480_smoke: MODEUP to P7 not observed");
    end
    if (dut.host_active_core !== CORE_Z480) begin
      $fatal(1, "tb_carbonz480_smoke: active core mismatch exp=%0d got=%0d",
             CORE_Z480, dut.host_active_core);
    end

    cycles = 0;
    while (!poweroff && (cycles < 200000)) begin
      @(posedge clk);
      cycles++;
    end
    if (!poweroff) $fatal(1, "tb_carbonz480_smoke: timeout waiting for poweroff");
    if (signature !== EXP_SIG) begin
      $fatal(1, "tb_carbonz480_smoke: signature mismatch exp=%08x got=%08x",
             EXP_SIG, signature);
    end
    $display("tb_carbonz480_smoke: PASS");
    $finish;
  end

endmodule
