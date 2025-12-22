`timescale 1ns/1ps

module tb_z480_scaffold;
  import carbon_arch_pkg::*;

  logic clk;
  logic rst_n;

  fabric_if mem_if (.clk(clk), .rst_n(rst_n));
  irq_if    irq    (.clk(clk), .rst_n(rst_n));
  csr_if    csr    (.clk(clk), .rst_n(rst_n));
  dbg_if    dbg    (.clk(clk), .rst_n(rst_n));

  fabric_mem_bfm #(.MEM_BYTES(4096)) u_mem (.clk(clk), .rst_n(rst_n), .bus(mem_if));
  csr_bfm u_csr (.clk(clk), .rst_n(rst_n), .csr(csr));

  z480_core u_dut (
      .clk(clk),
      .rst_n(rst_n),
      .mem_if(mem_if),
      .irq(irq),
      .csr(csr),
      .dbg(dbg)
  );

  // --------------------------------------------------------------------------
  // Clock / reset
  // --------------------------------------------------------------------------
  initial clk = 1'b0;
  always #5 clk = ~clk;

  // --------------------------------------------------------------------------
  // Drive unused sources to known values
  // --------------------------------------------------------------------------
  initial begin
    dbg.halt_req = 1'b0;
    dbg.run_req  = 1'b0;
    dbg.step_req = 1'b0;
    dbg.bp_valid = 1'b0;
    dbg.bp_write = 1'b0;
    dbg.bp_index = '0;
    dbg.bp_addr  = '0;
    dbg.bp_kind  = '0;
    dbg.bp_enable = 1'b0;
    dbg.trace_ready = 1'b1;

    irq.irq_valid   = 1'b0;
    irq.irq_vector  = '0;
    irq.irq_prio    = '0;
    irq.irq_pending = '0;
  end

  // --------------------------------------------------------------------------
  // CPUID helpers (CSR window)
  // --------------------------------------------------------------------------
  task automatic cpuid_read_words(
      input  logic [31:0] leaf,
      input  logic [31:0] subleaf,
      output logic [31:0] w0,
      output logic [31:0] w1,
      output logic [31:0] w2,
      output logic [31:0] w3
  );
    logic fault;
    logic [31:0] rd;
    begin
      u_csr.csr_write(CARBON_CSR_CPUID_LEAF, leaf, 4'hF, 2'd0, fault);
      if (fault) $fatal(1, "cpuid: leaf write fault");
      u_csr.csr_write(CARBON_CSR_CPUID_SUBLEAF, subleaf, 4'hF, 2'd0, fault);
      if (fault) $fatal(1, "cpuid: subleaf write fault");

      u_csr.csr_read(CARBON_CSR_CPUID_DATA0_LO, 2'd0, rd, fault);
      if (fault) $fatal(1, "cpuid: data0 read fault");
      w0 = rd;
      u_csr.csr_read(CARBON_CSR_CPUID_DATA1_LO, 2'd0, rd, fault);
      if (fault) $fatal(1, "cpuid: data1 read fault");
      w1 = rd;
      u_csr.csr_read(CARBON_CSR_CPUID_DATA2_LO, 2'd0, rd, fault);
      if (fault) $fatal(1, "cpuid: data2 read fault");
      w2 = rd;
      u_csr.csr_read(CARBON_CSR_CPUID_DATA3_LO, 2'd0, rd, fault);
      if (fault) $fatal(1, "cpuid: data3 read fault");
      w3 = rd;
    end
  endtask

  // --------------------------------------------------------------------------
  // Test sequence
  // --------------------------------------------------------------------------
  initial begin
    logic fault;
    logic [31:0] rd;
    logic [31:0] w0, w1, w2, w3;
    int unsigned timeout;

    rst_n = 1'b0;
    repeat (10) @(posedge clk);
    rst_n = 1'b1;
    repeat (10) @(posedge clk);

    // Halt via dbg_if.
    dbg.halt_req = 1'b1;
    @(posedge clk);
    dbg.halt_req = 1'b0;
    timeout = 1000;
    while ((timeout != 0) && !dbg.halt_ack) begin
      @(posedge clk);
      timeout--;
    end
    if (!dbg.halt_ack) $fatal(1, "dbg_if halt_ack not asserted");

    // Basic CSR reads.
    u_csr.csr_read(CARBON_CSR_ID, 2'd0, rd, fault);
    if (fault) $fatal(1, "CSR_ID read fault");

    u_csr.csr_read(CARBON_CSR_TIME, 2'd0, w0, fault);
    if (fault) $fatal(1, "CSR_TIME read fault");
    repeat (5) @(posedge clk);
    u_csr.csr_read(CARBON_CSR_TIME, 2'd0, w1, fault);
    if (fault) $fatal(1, "CSR_TIME read fault (2)");
    if (w1 == w0) $fatal(1, "CSR_TIME did not advance");

    // CPUID leaf sanity checks.
    cpuid_read_words(CARBON_CPUID_LEAF_VENDOR, 32'h0, w0, w1, w2, w3);
    if (w0 !== 32'h0001_0030) $fatal(1, "CPUID_VENDOR word0 mismatch");
    if (w1 !== 32'h4252_4143) $fatal(1, "CPUID_VENDOR word1 mismatch");
    if (w2 !== 32'h5A2D_4E4F) $fatal(1, "CPUID_VENDOR word2 mismatch");
    if (w3 !== 32'h2030_3834) $fatal(1, "CPUID_VENDOR word3 mismatch");

    cpuid_read_words(CARBON_CPUID_LEAF_ID, 32'h0, w0, w1, w2, w3);
    if (w0 !== 32'h0107_9000) $fatal(1, "CPUID_ID word0 mismatch");
    if (w1 !== 32'h0000_001F) $fatal(1, "CPUID_ID chip_flags mismatch");
    if (w2 !== 32'h0 || w3 !== 32'h0) $fatal(1, "CPUID_ID reserved words not zero");

    cpuid_read_words(CARBON_CPUID_LEAF_TIERS, 32'h0, w0, w1, w2, w3);
    if (w0 !== 32'h0007_0700) $fatal(1, "CPUID_TIERS word0 mismatch");

    cpuid_read_words(CARBON_CPUID_LEAF_FEATURES0, 32'h0, w0, w1, w2, w3);
    if (w0 !== (CARBON_FEAT_CSR_NAMESPACE_MASK |
                CARBON_FEAT_FABRIC_MASK |
                CARBON_FEAT_CPUID_MASK |
                CARBON_FEAT_IOMMU_HOOKS_MASK)) begin
      $fatal(1, "CPUID_FEATURES0 word0 mismatch");
    end

    cpuid_read_words(CARBON_CPUID_LEAF_TOPOLOGY, 32'h0, w0, w1, w2, w3);
    if (w0 !== 32'h0001_0001) $fatal(1, "CPUID_TOPOLOGY word0 mismatch");
    if (w1 !== 32'h0040_0080) $fatal(1, "CPUID_TOPOLOGY word1 mismatch");

    // Debug single-step via dbg_if.
    dbg.step_req = 1'b1;
    @(posedge clk);
    dbg.step_req = 1'b0;
    timeout = 2000;
    while ((timeout != 0) && !dbg.step_ack) begin
      @(posedge clk);
      timeout--;
    end
    if (!dbg.step_ack) $fatal(1, "dbg_if step_ack not observed");

    timeout = 2000;
    while ((timeout != 0) && !dbg.halt_ack) begin
      @(posedge clk);
      timeout--;
    end
    if (!dbg.halt_ack) $fatal(1, "dbg_if halt_ack not re-asserted after step");

    // Resume via dbg_if.
    dbg.run_req = 1'b1;
    @(posedge clk);
    dbg.run_req = 1'b0;
    repeat (5) @(posedge clk);
    if (dbg.halt_ack) $fatal(1, "dbg_if halt_ack did not deassert on run");

    // Halt/step via CSR mirror (privileged).
    u_csr.csr_write(CARBON_CSR_DBG_CTRL, 32'h0000_0001, 4'hF, 2'd1, fault);
    if (fault) $fatal(1, "CSR_DBG_CTRL halt write fault");
    timeout = 2000;
    while ((timeout != 0) && !dbg.halt_ack) begin
      @(posedge clk);
      timeout--;
    end
    if (!dbg.halt_ack) $fatal(1, "CSR_DBG_CTRL did not halt core");

    u_csr.csr_write(CARBON_CSR_DBG_STEP, 32'h0000_0001, 4'hF, 2'd1, fault);
    if (fault) $fatal(1, "CSR_DBG_STEP write fault");
    timeout = 2000;
    rd = '0;
    while ((timeout != 0) && !rd[1]) begin
      u_csr.csr_read(CARBON_CSR_DBG_STATUS, 2'd1, rd, fault);
      if (fault) $fatal(1, "CSR_DBG_STATUS read fault");
      @(posedge clk);
      timeout--;
    end
    if (!rd[1]) $fatal(1, "CSR_DBG_STATUS did not report step completion");

    u_csr.csr_write(CARBON_CSR_DBG_CTRL, 32'h0000_0000, 4'hF, 2'd1, fault);
    if (fault) $fatal(1, "CSR_DBG_CTRL run write fault");
    repeat (5) @(posedge clk);
    if (dbg.halt_ack) $fatal(1, "CSR_DBG_CTRL did not resume core");

    $display("tb_z480_scaffold: PASS");
    $finish;
  end

endmodule
