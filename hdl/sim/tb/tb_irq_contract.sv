`define CARBON_ENABLE_SVA
`timescale 1ns/1ps

module irq_sink_stub #(
    parameter int unsigned N = 32,
    parameter int unsigned PRIO_W = 0
) (
    input logic clk,
    input logic rst_n,
    irq_if.sink irq,
    output logic [((N <= 1) ? 1 : $clog2(N))-1:0] last_vec
);
  localparam int unsigned VEC_W = (N <= 1) ? 1 : $clog2(N);

  assign irq.irq_ack = irq.irq_valid;
  assign irq.irq_ack_vector = irq.irq_vector;

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      last_vec <= '0;
    end else if (irq.irq_valid) begin
      last_vec <= irq.irq_vector;
    end
  end
endmodule

module tb_irq_contract;
  localparam int unsigned N = 8;
  localparam int unsigned PRIO_W = 2;
  localparam int unsigned VEC_W = (N <= 1) ? 1 : $clog2(N);

  logic clk;
  logic rst_n;
  logic [VEC_W-1:0] last_vec;

  clock_reset_bfm #(
      .CLK_PERIOD(10ns),
      .RESET_CYCLES(3)
  ) clk_rst (
      .clk(clk),
      .rst_n(rst_n)
  );

  initial begin
    clk_rst.apply_reset();
  end

  irq_if #(
      .N(N),
      .PRIO_W(PRIO_W)
  ) irq (
      .clk(clk),
      .rst_n(rst_n)
  );

  irq_bfm #(
      .N(N),
      .PRIO_W(PRIO_W)
  ) bfm (
      .clk(clk),
      .rst_n(rst_n),
      .irq(irq)
  );

  irq_sink_stub #(
      .N(N),
      .PRIO_W(PRIO_W)
  ) dut (
      .clk(clk),
      .rst_n(rst_n),
      .irq(irq),
      .last_vec(last_vec)
  );

  initial begin
    logic [VEC_W-1:0] ack_vec;
    logic [N-1:0] pending;

    wait (rst_n);

    pending = 8'b0001_0101;
    bfm.irq_pulse(3'(2), 2'(1), pending, ack_vec);
    if (ack_vec != 3'(2)) $fatal(1, "ack_vec mismatch");
    if (last_vec != 3'(2)) $fatal(1, "last_vec mismatch");

    pending = 8'b1010_0000;
    bfm.irq_pulse(3'(5), 2'(2), pending, ack_vec);
    if (ack_vec != 3'(5)) $fatal(1, "ack_vec mismatch");
    if (last_vec != 3'(5)) $fatal(1, "last_vec mismatch");

    $display("tb_irq_contract: PASS");
    $finish;
  end

endmodule
