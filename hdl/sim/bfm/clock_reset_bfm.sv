// Project Carbon - Simulation BFM
// clock_reset_bfm: Standard clock/reset generation helpers.

module clock_reset_bfm #(
    parameter time CLK_PERIOD = 10ns,
    parameter int unsigned RESET_CYCLES = 5
) (
    output logic clk,
    output logic rst_n
);
  initial begin
    clk = 1'b0;
    forever #(CLK_PERIOD / 2) clk = ~clk;
  end

  task automatic apply_reset();
    begin
      rst_n = 1'b0;
      repeat (RESET_CYCLES) @(posedge clk);
      rst_n = 1'b1;
    end
  endtask

  task automatic wait_cycles(input int unsigned cycles);
    int unsigned i;
    begin
      for (i = 0; i < cycles; i++) @(posedge clk);
    end
  endtask

  initial begin
    rst_n = 1'b0;
  end

endmodule : clock_reset_bfm
