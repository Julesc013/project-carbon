`timescale 1ns/1ps

module tb_z90;
  import carbon_arch_pkg::*;

  logic clk;
  logic rst_n;

  fabric_if mem (.clk(clk), .rst_n(rst_n));
  fabric_if io  (.clk(clk), .rst_n(rst_n));
  irq_if    irq (.clk(clk), .rst_n(rst_n));
  csr_if    csr (.clk(clk), .rst_n(rst_n));
  dbg_if    dbg (.clk(clk), .rst_n(rst_n));
  cai_if    cai (.clk(clk), .rst_n(rst_n));

  fabric_mem_bfm #(.MEM_BYTES(4096)) u_mem (.clk(clk), .rst_n(rst_n), .bus(mem));
  fabric_mem_bfm #(.MEM_BYTES(256))  u_io  (.clk(clk), .rst_n(rst_n), .bus(io));
  csr_bfm u_csr (.clk(clk), .rst_n(rst_n), .csr(csr));

  z90_core u_z90 (
      .clk(clk),
      .rst_n(rst_n),
      .mem_if(mem),
      .io_if(io),
      .irq(irq),
      .csr(csr),
      .dbg(dbg),
      .cai(cai)
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
      for (i = 0; i < 4096; i++) u_mem.mem[i] = 8'h00;
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
      input int unsigned addr,
      input logic [7:0] target,
      input logic [15:0] entry
  );
    logic [7:0] op0;
    logic [7:0] op1;
    begin
      op0 = {4'(CARBON_Z90_P0_MAJOR_SYS), 4'h0};
      op1 = {4'(CARBON_Z90_P0_SUB_MODEUP), 4'h0};
      write_mem(addr + 0, CARBON_Z90_OPPAGE_P0_PREFIX0);
      write_mem(addr + 1, CARBON_Z90_OPPAGE_P0_PREFIX1);
      write_mem(addr + 2, op0);
      write_mem(addr + 3, op1);
      write_mem(addr + 4, target);
      write_mem(addr + 5, entry[7:0]);
      write_mem(addr + 6, entry[15:8]);
    end
  endtask

  task automatic emit_retmd(input int unsigned addr);
    logic [7:0] op0;
    logic [7:0] op1;
    begin
      op0 = {4'(CARBON_Z90_P0_MAJOR_SYS), 4'h0};
      op1 = {4'(CARBON_Z90_P0_SUB_RETMD), 4'h0};
      write_mem(addr + 0, CARBON_Z90_OPPAGE_P0_PREFIX0);
      write_mem(addr + 1, CARBON_Z90_OPPAGE_P0_PREFIX1);
      write_mem(addr + 2, op0);
      write_mem(addr + 3, op1);
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

  task automatic load_program_p3;
    begin
      clear_mem();
      write_mem(16'h0000, 8'h06); write_mem(16'h0001, 8'h03);
      write_mem(16'h0002, 8'h0E); write_mem(16'h0003, 8'h04);
      write_mem(16'h0004, 8'h3E); write_mem(16'h0005, 8'hF0);
      emit_modeup(16'h0006, 8'(CARBON_Z80_DERIVED_TIER_P3_Z180), 16'h0020);
      write_mem(16'h000D, 8'h76);

      write_mem(16'h0020, 8'hED); write_mem(16'h0021, 8'h4C);
      write_mem(16'h0022, 8'hED); write_mem(16'h0023, 8'h64);
      write_mem(16'h0024, 8'h0F);
      emit_retmd(16'h0025);
    end
  endtask

  task automatic load_program_illegal;
    begin
      clear_mem();
      write_mem(16'h0000, 8'h06); write_mem(16'h0001, 8'h02);
      write_mem(16'h0002, 8'h0E); write_mem(16'h0003, 8'h03);
      emit_modeup(16'h0004, 8'(CARBON_Z80_DERIVED_TIER_P2_Z80), 16'h0020);
      write_mem(16'h000B, 8'h76);

      write_mem(16'h0020, 8'hED); write_mem(16'h0021, 8'h4C);
      write_mem(16'h0022, 8'h76);
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
        if (dbg.halt_ack) return;
      end
      $fatal(1, "timeout waiting for halt");
    end
  endtask

  // --------------------------------------------------------------------------
  // Test sequence
  // --------------------------------------------------------------------------
  initial begin
    logic fault;
    logic [31:0] rd;

    rst_n = 1'b0;
    clear_io();

    // Phase 1: P2 mode accepts Z80 program.
    load_program_p2();
    apply_reset();
    wait_for_halt(2000);

    u_csr.csr_read(CARBON_CSR_TIER, 2'd1, rd, fault);
    if (fault) $fatal(1, "CSR_TIER read fault (P2)");
    if (rd[7:0] !== 8'(CARBON_Z80_DERIVED_TIER_P2_Z80)) $fatal(1, "P2 tier mismatch");
    if (u_z90.s_q.A !== 8'h46) $fatal(1, "P2 program result mismatch");

    // Phase 2: P3 mode accepts Z180 additions and returns via RETMD.
    load_program_p3();
    apply_reset();
    wait_for_halt(4000);

    u_csr.csr_read(CARBON_CSR_TIER, 2'd1, rd, fault);
    if (fault) $fatal(1, "CSR_TIER read fault (P3)");
    if (rd[7:0] !== 8'(CARBON_Z80_DERIVED_TIER_P0_I8080)) $fatal(1, "RETMD tier mismatch");
    if (u_z90.s_q.B !== 8'h00 || u_z90.s_q.C !== 8'h0C) $fatal(1, "MLT BC failed");
    if (u_z90.s_q.F !== 8'h54) $fatal(1, "TST n flags mismatch");

    // Phase 3: P2 rejects Z180-only opcodes.
    load_program_illegal();
    apply_reset();
    wait_for_halt(2000);

    u_csr.csr_read(CARBON_CSR_CAUSE, 2'd1, rd, fault);
    if (fault) $fatal(1, "CSR_CAUSE read fault");
    if (rd !== 32'h0000_0001) $fatal(1, "illegal opcode trap missing");
    u_csr.csr_read(CARBON_CSR_TIER, 2'd1, rd, fault);
    if (fault) $fatal(1, "CSR_TIER read fault (illegal)");
    if (rd[7:0] !== 8'(CARBON_Z80_DERIVED_TIER_P2_Z80)) $fatal(1, "tier changed on trap");

    $display("tb_z90: PASS");
    $finish;
  end

endmodule
