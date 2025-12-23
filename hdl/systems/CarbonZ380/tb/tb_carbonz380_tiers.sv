`timescale 1ns/1ps

module tb_carbonz380_tiers;
  import carbon_arch_pkg::*;

  logic clk;
  logic rst_n;

  logic [31:0] signature;
  logic poweroff;

  localparam int unsigned TIMEOUT = 40000;
  localparam logic [31:0] CAUSE_MODEUP_INVALID = 32'h0000_0012;

  initial clk = 1'b0;
  always #5 clk = ~clk;

  initial begin
    rst_n = 1'b0;
    repeat (10) @(posedge clk);
    rst_n = 1'b1;
  end

  carbonz380_top #(
      .ROM_TIER_TEST(1'b1)
  ) dut (
      .clk(clk),
      .rst_n(rst_n),
      .signature(signature),
      .poweroff(poweroff)
  );

  task automatic wait_for_tier(
      input logic [7:0] tier,
      input int unsigned sp,
      input string tag
  );
    int unsigned cycles;
    begin
      cycles = 0;
      while ((dut.u_cpu.csr_tier_q != tier) || (dut.u_cpu.md_sp_q != sp)) begin
        @(posedge clk);
        cycles++;
        if (cycles > TIMEOUT) $fatal(1, "tb_carbonz380_tiers: timeout waiting for %s", tag);
      end
    end
  endtask

  task automatic wait_for_trap(input string tag);
    int unsigned cycles;
    begin
      cycles = 0;
      while (!dut.u_cpu.trapped_q && (cycles < TIMEOUT)) begin
        @(posedge clk);
        cycles++;
      end
      if (!dut.u_cpu.trapped_q) $fatal(1, "tb_carbonz380_tiers: timeout waiting for trap (%s)", tag);
      if (dut.u_cpu.core_trap_cause_q !== CAUSE_MODEUP_INVALID) begin
        $fatal(1, "tb_carbonz380_tiers: trap cause mismatch exp=%08x got=%08x",
               CAUSE_MODEUP_INVALID, dut.u_cpu.core_trap_cause_q);
      end
    end
  endtask

  initial begin
    wait(rst_n);
    if (dut.u_cpu.csr_tier_q !== 8'(CARBON_Z80_DERIVED_TIER_P0_I8080)) begin
      $fatal(1, "tb_carbonz380_tiers: reset tier mismatch");
    end

    wait_for_tier(8'(CARBON_Z80_DERIVED_TIER_P1_I8085), 1, "P1");
    wait_for_tier(8'(CARBON_Z80_DERIVED_TIER_P0_I8080), 0, "RETMD->P0");
    wait_for_tier(8'(CARBON_Z80_DERIVED_TIER_P2_Z80), 1, "P2");
    wait_for_tier(8'(CARBON_Z80_DERIVED_TIER_P0_I8080), 0, "RETMD->P0");
    wait_for_tier(8'(CARBON_Z80_DERIVED_TIER_P3_Z180), 1, "P3");
    wait_for_tier(8'(CARBON_Z80_DERIVED_TIER_P0_I8080), 0, "RETMD->P0");
    wait_for_tier(8'(CARBON_Z80_DERIVED_TIER_P4_EZ80), 1, "P4");
    wait_for_tier(8'(CARBON_Z80_DERIVED_TIER_P0_I8080), 0, "RETMD->P0");
    wait_for_tier(8'(CARBON_Z80_DERIVED_TIER_P5_Z280), 1, "P5");
    wait_for_tier(8'(CARBON_Z80_DERIVED_TIER_P0_I8080), 0, "RETMD->P0");
    wait_for_tier(8'(CARBON_Z80_DERIVED_TIER_P6_Z380), 1, "P6");
    wait_for_tier(8'(CARBON_Z80_DERIVED_TIER_P0_I8080), 0, "RETMD->P0");
    wait_for_trap("MODEUP invalid");

    $display("tb_carbonz380_tiers: PASS");
    $finish;
  end

endmodule
