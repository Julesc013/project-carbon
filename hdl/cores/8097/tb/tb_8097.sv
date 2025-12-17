`timescale 1ns/1ps

module tb_8097;
  import carbon_arch_pkg::*;
  import fpu_8097_pkg::*;

  logic clk;
  logic rst_n;

  fabric_if mem_if (.*);
  csr_if    csr    (.*);

  fpu_8097 dut (
      .clk(clk),
      .rst_n(rst_n),
      .csr(csr),
      .mem_if(mem_if)
  );

  fabric_mem_bfm #(
      .MEM_BYTES(4096),
      .RESP_LATENCY(1)
  ) mem_bfm (
      .clk(clk),
      .rst_n(rst_n),
      .bus(mem_if)
  );

  csr_bfm csrdrv (
      .clk(clk),
      .rst_n(rst_n),
      .csr(csr)
  );

  initial begin
    clk = 1'b0;
    forever #5 clk = ~clk;
  end

  task automatic mem_clear();
    int unsigned i;
    begin
      for (i = 0; i < 4096; i++) mem_bfm.mem[i] = 8'h00;
    end
  endtask

  task automatic do_reset();
    begin
      rst_n = 1'b0;
      repeat (5) @(posedge clk);
      rst_n = 1'b1;
      repeat (2) @(posedge clk);
    end
  endtask

  task automatic push_fp64(input logic [63:0] v, output logic fault);
    begin
      csrdrv.csr_write(CARBON_CSR_8097_PUSH_LO, v[31:0], 4'hF, 2'(0), fault);
      if (fault) return;
      csrdrv.csr_write(CARBON_CSR_8097_PUSH_HI, v[63:32], 4'hF, 2'(0), fault);
    end
  endtask

  task automatic pop_fp64(output logic [63:0] v, output logic fault);
    logic [31:0] lo;
    logic [31:0] hi;
    begin
      csrdrv.csr_read(CARBON_CSR_8097_POP_LO, 2'(0), lo, fault);
      if (fault) begin
        v = 64'd0;
        return;
      end
      csrdrv.csr_read(CARBON_CSR_8097_POP_HI, 2'(0), hi, fault);
      v = {hi, lo};
    end
  endtask

  task automatic wait_not_busy();
    logic [31:0] st;
    logic fault;
    int unsigned spins;
    begin
      spins = 0;
      do begin
        csrdrv.csr_read(CARBON_CSR_8097_STATUS, 2'(0), st, fault);
        if (fault) $fatal(1, "CSR_8097_STATUS read fault");
        spins++;
        if (spins > 1000) $fatal(1, "Timeout waiting for 8097 not-busy");
        @(posedge clk);
      end while (st[0]);
    end
  endtask

  initial begin
    logic fault;
    logic [63:0] v;

    rst_n = 1'b0;
    repeat (2) @(posedge clk);

    do_reset();
    mem_clear();

    // ----------------------------------------------------------------------
    // Stack arithmetic: (2.0 + 1.0) = 3.0
    // ----------------------------------------------------------------------
    push_fp64(64'h3FF0_0000_0000_0000, fault); // 1.0
    if (fault) $fatal(1, "push 1.0 fault");
    push_fp64(64'h4000_0000_0000_0000, fault); // 2.0
    if (fault) $fatal(1, "push 2.0 fault");

    csrdrv.csr_write(CARBON_CSR_8097_CMD, 32'(FPU8097_CMD_FADD), 4'hF, 2'(0), fault);
    if (fault) $fatal(1, "CMD FADD fault");
    wait_not_busy();

    pop_fp64(v, fault);
    if (fault) $fatal(1, "pop fault");
    if (v !== 64'h4008_0000_0000_0000) $fatal(1, "FADD result mismatch: %016x", v);

    // ----------------------------------------------------------------------
    // Memory store/load: store 4.0, load back
    // ----------------------------------------------------------------------
    push_fp64(64'h4010_0000_0000_0000, fault); // 4.0
    if (fault) $fatal(1, "push 4.0 fault");

    csrdrv.csr_write(CARBON_CSR_8097_MEM_ADDR_LO, 32'h0000_0100, 4'hF, 2'(0), fault);
    if (fault) $fatal(1, "MEM_ADDR_LO fault");
    csrdrv.csr_write(CARBON_CSR_8097_MEM_ADDR_HI, 32'h0000_0000, 4'hF, 2'(0), fault);
    if (fault) $fatal(1, "MEM_ADDR_HI fault");

    csrdrv.csr_write(CARBON_CSR_8097_CMD, 32'(FPU8097_CMD_FSTP_MEM64), 4'hF, 2'(0), fault);
    if (fault) $fatal(1, "CMD FSTP fault");
    wait_not_busy();

    // Expect bytes at 0x100..0x107 for 0x4010_0000_0000_0000.
    if (mem_bfm.mem[16'h0104] !== 8'h00 ||
        mem_bfm.mem[16'h0105] !== 8'h00 ||
        mem_bfm.mem[16'h0106] !== 8'h10 ||
        mem_bfm.mem[16'h0107] !== 8'h40) begin
      $fatal(1, "FSTP memory image mismatch");
    end

    csrdrv.csr_write(CARBON_CSR_8097_CMD, 32'(FPU8097_CMD_FLD_MEM64), 4'hF, 2'(0), fault);
    if (fault) $fatal(1, "CMD FLD fault");
    wait_not_busy();

    pop_fp64(v, fault);
    if (fault) $fatal(1, "pop after FLD fault");
    if (v !== 64'h4010_0000_0000_0000) $fatal(1, "FLD result mismatch: %016x", v);

    // ----------------------------------------------------------------------
    // P7 regfile mode smoke: F2 = F0 + F1
    // ----------------------------------------------------------------------
    csrdrv.csr_write(CARBON_CSR_8097_MODEFLAGS, 32'h0000_0000, 4'hF, 2'(1), fault);
    if (fault) $fatal(1, "MODEFLAGS write fault");
    csrdrv.csr_write(CARBON_CSR_8097_TIER, 32'(CARBON_X86_DERIVED_TIER_P7_TURBO_UNLIMITED), 4'hF, 2'(1), fault);
    if (fault) $fatal(1, "TIER write fault");

    // F0 = 1.0
    csrdrv.csr_write(CARBON_CSR_8097_RF_INDEX, 32'd0, 4'hF, 2'(1), fault);
    if (fault) $fatal(1, "RF_INDEX fault");
    csrdrv.csr_write(CARBON_CSR_8097_RF_DATA_LO, 32'h0000_0000, 4'hF, 2'(1), fault);
    if (fault) $fatal(1, "RF_DATA_LO fault");
    csrdrv.csr_write(CARBON_CSR_8097_RF_DATA_HI, 32'h3FF0_0000, 4'hF, 2'(1), fault);
    if (fault) $fatal(1, "RF_DATA_HI fault");

    // F1 = 2.0
    csrdrv.csr_write(CARBON_CSR_8097_RF_INDEX, 32'd1, 4'hF, 2'(1), fault);
    if (fault) $fatal(1, "RF_INDEX fault");
    csrdrv.csr_write(CARBON_CSR_8097_RF_DATA_LO, 32'h0000_0000, 4'hF, 2'(1), fault);
    if (fault) $fatal(1, "RF_DATA_LO fault");
    csrdrv.csr_write(CARBON_CSR_8097_RF_DATA_HI, 32'h4000_0000, 4'hF, 2'(1), fault);
    if (fault) $fatal(1, "RF_DATA_HI fault");

    // RF_OP: ADD dst=2, srcA=0, srcB=1 -> 0x00001021
    csrdrv.csr_write(CARBON_CSR_8097_RF_OP, 32'h0000_1021, 4'hF, 2'(1), fault);
    if (fault) $fatal(1, "RF_OP fault");
    wait_not_busy();

    csrdrv.csr_write(CARBON_CSR_8097_RF_INDEX, 32'd2, 4'hF, 2'(1), fault);
    if (fault) $fatal(1, "RF_INDEX fault");
    logic [31:0] lo;
    logic [31:0] hi;
    csrdrv.csr_read(CARBON_CSR_8097_RF_DATA_LO, 2'(1), lo, fault);
    if (fault) $fatal(1, "RF_DATA_LO read fault");
    csrdrv.csr_read(CARBON_CSR_8097_RF_DATA_HI, 2'(1), hi, fault);
    if (fault) $fatal(1, "RF_DATA_HI read fault");
    if ({hi, lo} !== 64'h4008_0000_0000_0000) $fatal(1, "RF ADD result mismatch: %08x%08x", hi, lo);

    $display("tb_8097: PASS");
    $finish;
  end

endmodule

