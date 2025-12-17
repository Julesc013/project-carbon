`timescale 1ns/1ps

module tb_carbonx96;
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

  carbonx96_top dut (
      .clk(clk),
      .rst_n(rst_n),
      .signature(signature),
      .poweroff(poweroff)
  );

  localparam logic [31:0] EXP_SIG = 32'h2136_3958; // "X96!" in little-endian bytes

  int unsigned cycles;
  initial begin
    wait(rst_n);
    cycles = 0;
    while (!poweroff && (cycles < 600000)) begin
      @(posedge clk);
      cycles++;
    end
    if (!poweroff) $fatal(1, "tb_carbonx96: timeout waiting for poweroff");
    if (signature !== EXP_SIG) $fatal(1, "tb_carbonx96: signature mismatch exp=%08x got=%08x", EXP_SIG, signature);
    $display("tb_carbonx96: PASS");
    $finish;
  end

endmodule

