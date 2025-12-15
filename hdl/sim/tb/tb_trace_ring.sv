`timescale 1ns/1ps

module tb_trace_ring;
  import carbon_arch_pkg::*;

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

  logic trace_valid;
  logic trace_ready;
  logic [127:0] trace_data;

  trace_ring #(
      .REC_W(128),
      .DEPTH(8)
  ) dut (
      .clk(clk),
      .rst_n(rst_n),
      .csr(csr),
      .trace_valid(trace_valid),
      .trace_ready(trace_ready),
      .trace_data(trace_data)
  );

  task automatic push_trace(input logic [127:0] rec);
    begin
      trace_data  = rec;
      trace_valid = 1'b1;
      while (!trace_ready) @(posedge clk);
      @(posedge clk);
      trace_valid = 1'b0;
    end
  endtask

  function automatic logic [127:0] read_rec();
    logic fault;
    logic [31:0] w0, w1, w2, w3;
    begin
      bfm.csr_read(CARBON_CSR_TRACE_CTL + 32'h4, 2'b00, w0, fault);
      if (fault) $fatal(1, "DATA0 read fault");
      bfm.csr_read(CARBON_CSR_TRACE_CTL + 32'h5, 2'b00, w1, fault);
      if (fault) $fatal(1, "DATA1 read fault");
      bfm.csr_read(CARBON_CSR_TRACE_CTL + 32'h6, 2'b00, w2, fault);
      if (fault) $fatal(1, "DATA2 read fault");
      bfm.csr_read(CARBON_CSR_TRACE_CTL + 32'h7, 2'b00, w3, fault);
      if (fault) $fatal(1, "DATA3 read fault");
      read_rec = {w3, w2, w1, w0};
    end
  endfunction

  initial begin
    logic fault;
    logic [127:0] r0, r1, r2;
    wait(rst_n);
    trace_valid = 1'b0;
    trace_data  = '0;

    // Enable trace (bit0=1).
    bfm.csr_write(CARBON_CSR_TRACE_CTL, 32'h1, 4'hF, 2'b00, fault);
    if (fault) $fatal(1, "trace_ctl write fault");

    push_trace(128'h0001_0002_0003_0004_0005_0006_0007_0008);
    push_trace(128'h1111_2222_3333_4444_5555_6666_7777_8888);
    push_trace(128'hAAAA_BBBB_CCCC_DDDD_EEEE_FFFF_0000_1234);

    r0 = read_rec();
    r1 = read_rec();
    r2 = read_rec();

    if (r0 !== 128'h0001_0002_0003_0004_0005_0006_0007_0008) $fatal(1, "record0 mismatch");
    if (r1 !== 128'h1111_2222_3333_4444_5555_6666_7777_8888) $fatal(1, "record1 mismatch");
    if (r2 !== 128'hAAAA_BBBB_CCCC_DDDD_EEEE_FFFF_0000_1234) $fatal(1, "record2 mismatch");

    $display("tb_trace_ring: PASS");
    $finish;
  end

endmodule

