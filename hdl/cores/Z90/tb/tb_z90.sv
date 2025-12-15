`timescale 1ns/1ps

module tb_z90;
  import carbon_arch_pkg::*;

  logic clk;
  logic rst_n;

  // --------------------------------------------------------------------------
  // Z85 instance (legacy comparison)
  // --------------------------------------------------------------------------
  fabric_if mem85 (.clk(clk), .rst_n(rst_n));
  fabric_if io85  (.clk(clk), .rst_n(rst_n));
  irq_if    irq85 (.clk(clk), .rst_n(rst_n));
  csr_if    csr85 (.clk(clk), .rst_n(rst_n));
  dbg_if    dbg85 (.clk(clk), .rst_n(rst_n));

  fabric_mem_bfm #(.MEM_BYTES(4096)) u_mem85 (.clk(clk), .rst_n(rst_n), .bus(mem85));
  fabric_mem_bfm #(.MEM_BYTES(256))  u_io85  (.clk(clk), .rst_n(rst_n), .bus(io85));
  csr_bfm u_csr85 (.clk(clk), .rst_n(rst_n), .csr(csr85));

  z85_core u_z85 (
      .clk(clk),
      .rst_n(rst_n),
      .mem_if(mem85),
      .io_if(io85),
      .irq(irq85),
      .csr(csr85),
      .dbg(dbg85)
  );

  // --------------------------------------------------------------------------
  // Z90 instance under test
  // --------------------------------------------------------------------------
  fabric_if mem90 (.clk(clk), .rst_n(rst_n));
  fabric_if io90  (.clk(clk), .rst_n(rst_n));
  irq_if    irq90 (.clk(clk), .rst_n(rst_n));
  csr_if    csr90 (.clk(clk), .rst_n(rst_n));
  dbg_if    dbg90 (.clk(clk), .rst_n(rst_n));
  cai_if    cai90 (.clk(clk), .rst_n(rst_n));

  fabric_mem_bfm #(.MEM_BYTES(4096)) u_mem90 (.clk(clk), .rst_n(rst_n), .bus(mem90));
  fabric_mem_bfm #(.MEM_BYTES(256))  u_io90  (.clk(clk), .rst_n(rst_n), .bus(io90));
  csr_bfm u_csr90 (.clk(clk), .rst_n(rst_n), .csr(csr90));

  z90_core u_z90 (
      .clk(clk),
      .rst_n(rst_n),
      .mem_if(mem90),
      .io_if(io90),
      .irq(irq90),
      .csr(csr90),
      .dbg(dbg90),
      .cai(cai90)
  );

  // --------------------------------------------------------------------------
  // Clock / reset
  // --------------------------------------------------------------------------
  initial clk = 1'b0;
  always #5 clk = ~clk;

  // --------------------------------------------------------------------------
  // Drive unused debug/irq sources to known values
  // --------------------------------------------------------------------------
  initial begin
    dbg85.halt_req = 1'b0;
    dbg85.run_req  = 1'b0;
    dbg85.step_req = 1'b0;
    dbg85.bp_valid = 1'b0;
    dbg85.bp_write = 1'b0;
    dbg85.bp_index = '0;
    dbg85.bp_addr  = '0;
    dbg85.bp_kind  = '0;
    dbg85.bp_enable = 1'b0;
    dbg85.trace_ready = 1'b1;

    dbg90.halt_req = 1'b0;
    dbg90.run_req  = 1'b0;
    dbg90.step_req = 1'b0;
    dbg90.bp_valid = 1'b0;
    dbg90.bp_write = 1'b0;
    dbg90.bp_index = '0;
    dbg90.bp_addr  = '0;
    dbg90.bp_kind  = '0;
    dbg90.bp_enable = 1'b0;
    dbg90.trace_ready = 1'b1;

    irq85.irq_valid   = 1'b0;
    irq85.irq_vector  = '0;
    irq85.irq_prio    = '0;
    irq85.irq_pending = '0;

    irq90.irq_valid   = 1'b0;
    irq90.irq_vector  = '0;
    irq90.irq_prio    = '0;
    irq90.irq_pending = '0;
  end

  // --------------------------------------------------------------------------
  // CAI doorbell monitor
  // --------------------------------------------------------------------------
  logic cai_submit_seen;
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) cai_submit_seen <= 1'b0;
    else if (cai90.submit_doorbell) cai_submit_seen <= 1'b1;
  end

  // --------------------------------------------------------------------------
  // Memory helpers
  // --------------------------------------------------------------------------
  task automatic write_mem85(input int unsigned addr, input logic [7:0] v);
    u_mem85.mem[addr] = v;
  endtask

  task automatic write_mem90(input int unsigned addr, input logic [7:0] v);
    u_mem90.mem[addr] = v;
  endtask

  task automatic load_legacy_program;
    begin
      // Program:
      //   LD A,0x12
      //   LD B,0x34
      //   ADD A,B
      //   HALT
      write_mem85(16'h0000, 8'h3E); write_mem85(16'h0001, 8'h12);
      write_mem85(16'h0002, 8'h06); write_mem85(16'h0003, 8'h34);
      write_mem85(16'h0004, 8'h80);
      write_mem85(16'h0005, 8'h76);

      write_mem90(16'h0000, 8'h3E); write_mem90(16'h0001, 8'h12);
      write_mem90(16'h0002, 8'h06); write_mem90(16'h0003, 8'h34);
      write_mem90(16'h0004, 8'h80);
      write_mem90(16'h0005, 8'h76);
    end
  endtask

  task automatic load_z90_program;
    logic [7:0] op0;
    logic [7:0] op1;
    begin
      // 0x0000: MODEUP(P7, 0x0020)
      op0 = {4'(CARBON_Z90_P0_MAJOR_SYS), 4'h0};
      op1 = {4'(CARBON_Z90_P0_SUB_MODEUP), 4'h0}; // ladder=0 (Z80-derived)
      write_mem90(16'h0000, CARBON_Z90_OPPAGE_P0_PREFIX0);
      write_mem90(16'h0001, CARBON_Z90_OPPAGE_P0_PREFIX1);
      write_mem90(16'h0002, op0);
      write_mem90(16'h0003, op1);
      write_mem90(16'h0004, 8'(CARBON_Z80_DERIVED_TIER_P7_TURBO_UNLIMITED));
      write_mem90(16'h0005, 8'h20);
      write_mem90(16'h0006, 8'h00);
      write_mem90(16'h0007, 8'h76); // HALT (return target after RETMD)

      // 0x0020: LEA X10, [X8 + X9 + 0x10]
      op0 = {4'(CARBON_Z90_P1_OP_LEA), 4'hA};
      op1 = {4'h8, 4'h9}; // base=X8, index=X9
      write_mem90(16'h0020, CARBON_Z90_OPPAGE_P1_PREFIX0);
      write_mem90(16'h0021, CARBON_Z90_OPPAGE_P1_PREFIX1);
      write_mem90(16'h0022, op0);
      write_mem90(16'h0023, op1);
      write_mem90(16'h0024, 8'h10);

      // 0x0025: ST16 [X8 + X0 + 0], X11
      op0 = {4'(CARBON_Z90_P1_OP_ST16), 4'hB};
      op1 = {4'h8, 4'h0};
      write_mem90(16'h0025, CARBON_Z90_OPPAGE_P1_PREFIX0);
      write_mem90(16'h0026, CARBON_Z90_OPPAGE_P1_PREFIX1);
      write_mem90(16'h0027, op0);
      write_mem90(16'h0028, op1);
      write_mem90(16'h0029, 8'h00);

      // 0x002A: LD16 X12, [X8 + X0 + 0]
      op0 = {4'(CARBON_Z90_P1_OP_LD16), 4'hC};
      op1 = {4'h8, 4'h0};
      write_mem90(16'h002A, CARBON_Z90_OPPAGE_P1_PREFIX0);
      write_mem90(16'h002B, CARBON_Z90_OPPAGE_P1_PREFIX1);
      write_mem90(16'h002C, op0);
      write_mem90(16'h002D, op1);
      write_mem90(16'h002E, 8'h00);

      // 0x002F: CAS16 X13(expected), [X8 + 0], X14(desired)
      op0 = {4'(CARBON_Z90_P1_OP_CAS16), 4'hD};
      op1 = {4'h8, 4'hE}; // base=X8, index=X14
      write_mem90(16'h002F, CARBON_Z90_OPPAGE_P1_PREFIX0);
      write_mem90(16'h0030, CARBON_Z90_OPPAGE_P1_PREFIX1);
      write_mem90(16'h0031, op0);
      write_mem90(16'h0032, op1);
      write_mem90(16'h0033, 8'h00);

      // 0x0034: CAI_CFG
      op0 = {4'(CARBON_Z90_P0_MAJOR_SYS), 4'h0};
      op1 = {4'(CARBON_Z90_P0_SUB_CAI_CFG), 4'h0};
      write_mem90(16'h0034, CARBON_Z90_OPPAGE_P0_PREFIX0);
      write_mem90(16'h0035, CARBON_Z90_OPPAGE_P0_PREFIX1);
      write_mem90(16'h0036, op0);
      write_mem90(16'h0037, op1);

      // 0x0038: CAI_SUBMIT
      op1 = {4'(CARBON_Z90_P0_SUB_CAI_SUBMIT), 4'h0};
      write_mem90(16'h0038, CARBON_Z90_OPPAGE_P0_PREFIX0);
      write_mem90(16'h0039, CARBON_Z90_OPPAGE_P0_PREFIX1);
      write_mem90(16'h003A, op0);
      write_mem90(16'h003B, op1);

      // 0x003C: RETMD
      op1 = {4'(CARBON_Z90_P0_SUB_RETMD), 4'h0};
      write_mem90(16'h003C, CARBON_Z90_OPPAGE_P0_PREFIX0);
      write_mem90(16'h003D, CARBON_Z90_OPPAGE_P0_PREFIX1);
      write_mem90(16'h003E, op0);
      write_mem90(16'h003F, op1);
    end
  endtask

  // --------------------------------------------------------------------------
  // Test sequence
  // --------------------------------------------------------------------------
  initial begin
    logic fault;
    logic [31:0] rd;

    // Phase 1: legacy compatibility subset
    rst_n = 1'b0;
    load_legacy_program();
    repeat (10) @(posedge clk);
    rst_n = 1'b1;

    // Wait for both cores to HALT
    wait (u_z85.s_q.halt_latch == 1'b1);
    wait (dbg90.halt_ack == 1'b1);

    if (u_z85.s_q.A !== u_z90.z80_q.A) $fatal(1, "legacy mismatch: A");
    if (u_z85.s_q.F !== u_z90.z80_q.F) $fatal(1, "legacy mismatch: F");
    if (u_z85.s_q.B !== u_z90.z80_q.B) $fatal(1, "legacy mismatch: B");

    // Phase 2: Z90 fast-path + MODEUP/RETMD + CAS16 + CAI
    rst_n = 1'b0;
    dbg90.halt_req = 1'b1;
    load_z90_program();
    repeat (10) @(posedge clk);
    rst_n = 1'b1;

    // Hold halted while configuring via csr_if.
    repeat (2) @(posedge clk);
    dbg90.halt_req = 1'b0;

    // Clear STRICT to allow turbo features once in P7.
    u_csr90.csr_write(CARBON_CSR_MODEFLAGS, 32'h0000_0000, 4'hF, 2'd1, fault);
    if (fault) $fatal(1, "CSR_MODEFLAGS write fault");

    // Preload Z90 registers for the program (no immediate load in scaffolding ISA yet).
    @(posedge clk);
    u_z90.x_q[2]  = 16'h1000; // CAI submit base lo
    u_z90.x_q[3]  = 16'h0000; // CAI submit base hi
    u_z90.x_q[4]  = 16'h2000; // CAI comp base lo
    u_z90.x_q[5]  = 16'h0000; // CAI comp base hi
    u_z90.x_q[6]  = 16'h00FF; // ring mask
    u_z90.x_q[7]  = 16'h0001; // context

    u_z90.x_q[8]  = 16'h0100; // base address for memory ops
    u_z90.x_q[9]  = 16'h0004; // index for LEA
    u_z90.x_q[11] = 16'hBEEF; // store value
    u_z90.x_q[13] = 16'hBEEF; // expected for CAS16
    u_z90.x_q[14] = 16'hCAFE; // desired for CAS16

    // Release debug halt.
    dbg90.run_req = 1'b1;
    @(posedge clk);
    dbg90.run_req = 1'b0;

    // Wait until HALT after RETMD returns to 0x0007.
    wait (dbg90.halt_ack == 1'b1);

    // Validate mode returned to P0.
    u_csr90.csr_read(CARBON_CSR_TIER, 2'd1, rd, fault);
    if (fault) $fatal(1, "CSR_TIER read fault");
    if (rd[7:0] !== 8'(CARBON_Z80_DERIVED_TIER_P0_I8080)) $fatal(1, "tier not restored");

    // Validate LEA result.
    if (u_z90.x_q[10] !== 16'h0114) $fatal(1, "LEA failed");

    // Validate ST16/LD16 and CAS16.
    if (u_z90.x_q[12] !== 16'hBEEF) $fatal(1, "LD16 failed");
    if (u_mem90.mem[16'h0100] !== 8'hFE) $fatal(1, "CAS16 memory low byte mismatch");
    if (u_mem90.mem[16'h0101] !== 8'hCA) $fatal(1, "CAS16 memory high byte mismatch");
    if (u_z90.z90_flags_q[0] !== 1'b1) $fatal(1, "CAS16 did not set Z flag");

    // Validate CAI was configured and doorbell was rung.
    if (!cai_submit_seen) $fatal(1, "CAI submit doorbell not observed");
    if (cai90.submit_ring_mask[15:0] !== 16'h00FF) $fatal(1, "CAI ring mask mismatch");

    $display("tb_z90: PASS");
    $finish;
  end

endmodule

