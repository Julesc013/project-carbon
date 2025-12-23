`timescale 1ns/1ps

module tb_z380_core;
  import carbon_arch_pkg::*;

  logic clk;
  logic rst_n;

  fabric_if mem (.clk(clk), .rst_n(rst_n));
  fabric_if io  (.clk(clk), .rst_n(rst_n));
  irq_if    irq (.clk(clk), .rst_n(rst_n));
  csr_if    csr (.clk(clk), .rst_n(rst_n));
  dbg_if    dbg (.clk(clk), .rst_n(rst_n));

  fabric_mem_bfm #(.MEM_BYTES(131072)) u_mem (.clk(clk), .rst_n(rst_n), .bus(mem));
  fabric_mem_bfm #(.MEM_BYTES(256))    u_io  (.clk(clk), .rst_n(rst_n), .bus(io));
  csr_bfm u_csr (.clk(clk), .rst_n(rst_n), .csr(csr));

  z380_core u_z380 (
      .clk(clk),
      .rst_n(rst_n),
      .mem_if(mem),
      .io_if(io),
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
  // Drive debug/irq defaults
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
  // Memory helpers
  // --------------------------------------------------------------------------
  task automatic clear_mem;
    int unsigned i;
    begin
      for (i = 0; i < 131072; i++) u_mem.mem[i] = 8'h00;
    end
  endtask

  task automatic clear_io;
    int unsigned i;
    begin
      for (i = 0; i < 256; i++) u_io.mem[i] = 8'h00;
    end
  endtask

  task automatic write_mem(input int unsigned addr, input logic [7:0] v);
    u_mem.mem[addr] = v;
  endtask

  task automatic emit_modeup(
      input int unsigned base,
      input logic [7:0] target,
      input logic [15:0] entry
  );
    logic [7:0] op0;
    logic [7:0] op1;
    begin
      op0 = {4'(CARBON_Z90_P0_MAJOR_SYS), 4'h0};
      op1 = {4'(CARBON_Z90_P0_SUB_MODEUP), 4'h0};
      write_mem(base + 0, CARBON_Z90_OPPAGE_P0_PREFIX0);
      write_mem(base + 1, CARBON_Z90_OPPAGE_P0_PREFIX1);
      write_mem(base + 2, op0);
      write_mem(base + 3, op1);
      write_mem(base + 4, target);
      write_mem(base + 5, entry[7:0]);
      write_mem(base + 6, entry[15:8]);
    end
  endtask

  task automatic load_program_p2;
    begin
      clear_mem();
      emit_modeup(16'h0000, 8'(CARBON_Z80_DERIVED_TIER_P2_Z80), 16'h0010);
      write_mem(16'h0007, 8'h76);
      write_mem(16'h0010, 8'h3E); write_mem(16'h0011, 8'h12);
      write_mem(16'h0012, 8'h06); write_mem(16'h0013, 8'h34);
      write_mem(16'h0014, 8'h80);
      write_mem(16'h0015, 8'h76);
    end
  endtask

  task automatic load_program_p6;
    int unsigned base;
    begin
      clear_mem();
      base = 32'h0001_0000;

      // Vector table for vector=2 at base+0x0104 -> handler 0x0200
      write_mem(base + 32'h0104, 8'h00);
      write_mem(base + 32'h0105, 8'h02);

      // Handler at 0x0200: A=0x55; illegal op
      write_mem(base + 32'h0200, 8'h3E);
      write_mem(base + 32'h0201, 8'h55);
      write_mem(base + 32'h0202, 8'hED);
      write_mem(base + 32'h0203, 8'hFE);

      emit_modeup(base + 32'h0000, 8'(CARBON_Z80_DERIVED_TIER_P6_Z380), 16'h0020);
      write_mem(base + 32'h0007, 8'h76);

      // P6 entry
      write_mem(base + 32'h0020, 8'h21); write_mem(base + 32'h0021, 8'h02); write_mem(base + 32'h0022, 8'h00); // HL=2
      write_mem(base + 32'h0023, 8'h11); write_mem(base + 32'h0024, 8'h01); write_mem(base + 32'h0025, 8'h00); // DE=1
      write_mem(base + 32'h0026, 8'h01); write_mem(base + 32'h0027, 8'h03); write_mem(base + 32'h0028, 8'h00); // BC=3
      write_mem(base + 32'h0029, 8'hED); write_mem(base + 32'h002A, 8'hFC); // MUL
      write_mem(base + 32'h002B, 8'h22); write_mem(base + 32'h002C, 8'h44); write_mem(base + 32'h002D, 8'h00); // (0044)=HL
      write_mem(base + 32'h002E, 8'h31); write_mem(base + 32'h002F, 8'h40); write_mem(base + 32'h0030, 8'h00); // SP=0040
      write_mem(base + 32'h0031, 8'h3E); write_mem(base + 32'h0032, 8'hAA); // A=AA
      write_mem(base + 32'h0033, 8'h32); write_mem(base + 32'h0034, 8'h41); write_mem(base + 32'h0035, 8'h00); // (0041)=A
      write_mem(base + 32'h0036, 8'hED); write_mem(base + 32'h0037, 8'hF8); // LD A,(SP+d)
      write_mem(base + 32'h0038, 8'h01); // d=1
      write_mem(base + 32'h0039, 8'h32); write_mem(base + 32'h003A, 8'h42); write_mem(base + 32'h003B, 8'h00); // (0042)=A
      write_mem(base + 32'h003C, 8'hED); write_mem(base + 32'h003D, 8'h5E); // IM 2
      write_mem(base + 32'h003E, 8'hFB); // EI
      write_mem(base + 32'h003F, 8'h76); // HALT
    end
  endtask

  task automatic apply_reset;
    begin
      rst_n = 1'b0;
      repeat (5) @(posedge clk);
      rst_n = 1'b1;
      repeat (2) @(posedge clk);
    end
  endtask

  task automatic wait_for_halt(input int unsigned max_cycles);
    int unsigned i;
    begin
      for (i = 0; i < max_cycles; i++) begin
        @(posedge clk);
        if (u_z380.s_q.halt_latch) return;
      end
      $fatal(1, "timeout waiting for HALT");
    end
  endtask

  // --------------------------------------------------------------------------
  // Test sequence
  // --------------------------------------------------------------------------
  initial begin
    logic fault;
    logic [31:0] rd;
    localparam logic [7:0] Z380_MODE_NATIVE_MASK = 8'h04;
    localparam logic [7:0] Z380_MODE_EXTENDED_MASK = 8'h08;
    localparam logic [7:0] Z380_MODE_LONGWORD_MASK = 8'h10;
    localparam logic [7:0] Z380_MODE_VEC16_MASK = 8'h20;
    localparam logic [7:0] Z380_MODE_ALL =
        Z380_MODE_NATIVE_MASK | Z380_MODE_EXTENDED_MASK |
        Z380_MODE_LONGWORD_MASK | Z380_MODE_VEC16_MASK;
    localparam logic [31:0] Z380_CSR_ADDR_HI = 32'h00a20010;
    localparam logic [31:0] Z380_CSR_VEC_BASE = 32'h00a20014;

    rst_n = 1'b0;
    clear_io();

    // Phase 1: P2 mode accepts Z80 program.
    load_program_p2();
    apply_reset();
    wait_for_halt(4000);
    if (u_z380.s_q.A !== 8'h46) $fatal(1, "P2 program result mismatch");

    // Phase 2: P6 mode with extended/native/longword and IM2 vectoring.
    load_program_p6();
    dbg.halt_req = 1'b1;
    apply_reset();

    u_csr.csr_write(CARBON_CSR_MODEFLAGS, {24'h0, Z380_MODE_ALL}, 4'hF, 2'd1, fault);
    if (fault) $fatal(1, "CSR_MODEFLAGS write fault");
    u_csr.csr_write(Z380_CSR_ADDR_HI, 32'h0000_0001, 4'hF, 2'd1, fault);
    if (fault) $fatal(1, "CSR_ADDR_HI write fault");
    u_csr.csr_write(Z380_CSR_VEC_BASE, 32'h0000_0100, 4'hF, 2'd1, fault);
    if (fault) $fatal(1, "CSR_VEC_BASE write fault");

    dbg.halt_req = 1'b0;
    dbg.run_req = 1'b1;
    @(posedge clk);
    dbg.run_req = 1'b0;

    wait_for_halt(20000);
    irq.irq_vector = 5'd2;
    irq.irq_valid  = 1'b1;
    repeat (3) @(posedge clk);
    irq.irq_valid  = 1'b0;

    repeat (50) @(posedge clk);
    if (u_z380.s_q.A !== 8'h55) $fatal(1, "IM2 handler did not run");
    if (u_z380.csr_cause_q !== 32'h0000_0001) $fatal(1, "illegal opcode trap missing");
    if (u_z380.csr_epc_q !== 32'h0000_0202) $fatal(1, "trap EPC mismatch");
    if (u_mem.mem[32'h0001_0042] !== 8'hAA) $fatal(1, "SP-relative load mismatch");
    if (u_mem.mem[32'h0001_0044] !== 8'h06) $fatal(1, "mul result low byte mismatch");
    if (u_mem.mem[32'h0001_0045] !== 8'h00) $fatal(1, "mul result high byte mismatch");

    $display("tb_z380_core: PASS");
    $finish;
  end

endmodule
