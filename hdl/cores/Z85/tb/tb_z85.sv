`timescale 1ns/1ps

module tb_z85 #(
    parameter bit RUN_ZEX = 1'b0
);
  import carbon_arch_pkg::*;
  import z85_regfile_pkg::*;
  import z85_flags_pkg::*;

  logic clk;
  logic rst_n;

  localparam logic [31:0] Z85_CAUSE_ILLEGAL_INSN = 32'h0000_0001;

  bit run_zex;
  string zex_hex_path;
  string zex_bin_path;
  int unsigned zex_entry;
  int unsigned zex_timeout;
  logic zex_done;
  logic [7:0] zex_last_out;

  // Clk
  initial clk = 1'b0;
  always #5 clk = ~clk;

  // Interfaces
  fabric_if mem_bus(.clk(clk), .rst_n(rst_n));
  fabric_if io_bus (.clk(clk), .rst_n(rst_n));
  csr_if    csr_bus(.clk(clk), .rst_n(rst_n));
  dbg_if    dbg_bus(.clk(clk), .rst_n(rst_n));
  irq_if #(.N(512)) irq_bus(.clk(clk), .rst_n(rst_n));

  // BFMs
  fabric_mem_bfm #(.MEM_BYTES(65536), .RESP_LATENCY(1)) u_mem (
      .clk(clk),
      .rst_n(rst_n),
      .bus(mem_bus)
  );

  fabric_mem_bfm #(.MEM_BYTES(65536), .RESP_LATENCY(1)) u_io (
      .clk(clk),
      .rst_n(rst_n),
      .bus(io_bus)
  );

  csr_bfm u_csr_bfm (
      .clk(clk),
      .rst_n(rst_n),
      .csr(csr_bus)
  );

  wire io_fire = io_bus.req_valid && io_bus.req_ready;

  // DUT
  z85_core dut (
      .clk(clk),
      .rst_n(rst_n),
      .mem_if(mem_bus),
      .io_if(io_bus),
      .irq(irq_bus),
      .csr(csr_bus),
      .dbg(dbg_bus)
  );

  // Reference model
  z85_ref_model u_ref();

  task automatic clear_mem();
    int unsigned i;
    begin
      for (i = 0; i < 65536; i++) begin
        u_mem.mem[i] = 8'h00;
        u_io.mem[i] = 8'h00;
      end
    end
  endtask

  task automatic mem_write_byte(input int unsigned addr, input logic [7:0] v);
    begin
      u_mem.mem[addr] = v;
      u_ref.mem[addr[15:0]] = v;
    end
  endtask

  task automatic io_write_byte(input int unsigned port, input logic [7:0] v);
    begin
      u_io.mem[port] = v;
      u_ref.io_mem[port[15:0]] = v;
    end
  endtask

  task automatic write_modeup(
      input logic [15:0] addr,
      input logic [7:0] target,
      input logic [15:0] entry
  );
    begin
      mem_write_byte(addr + 16'd0, CARBON_Z90_OPPAGE_P0_PREFIX0);
      mem_write_byte(addr + 16'd1, CARBON_Z90_OPPAGE_P0_PREFIX1);
      mem_write_byte(addr + 16'd2, {4'(CARBON_Z90_P0_MAJOR_SYS), 4'h0});
      mem_write_byte(addr + 16'd3, {4'(CARBON_Z90_P0_SUB_MODEUP), 4'h0});
      mem_write_byte(addr + 16'd4, target);
      mem_write_byte(addr + 16'd5, entry[7:0]);
      mem_write_byte(addr + 16'd6, entry[15:8]);
    end
  endtask

  task automatic reset_dut_and_ref();
    begin
      rst_n = 1'b0;
      dbg_bus.halt_req  = 1'b1;
      dbg_bus.run_req   = 1'b0;
      dbg_bus.step_req  = 1'b0;
      dbg_bus.bp_valid  = 1'b0;
      dbg_bus.bp_write  = 1'b0;
      dbg_bus.bp_index  = '0;
      dbg_bus.bp_addr   = '0;
      dbg_bus.bp_kind   = '0;
      dbg_bus.bp_enable = 1'b0;
      dbg_bus.trace_ready = 1'b1;

      irq_bus.irq_valid  = 1'b0;
      irq_bus.irq_vector = '0;
      irq_bus.irq_prio   = '0;
      irq_bus.irq_pending = '0;

      u_ref.reset_model();
      clear_mem();

      repeat (5) @(posedge clk);
      rst_n = 1'b1;
      repeat (10) @(posedge clk);
    end
  endtask

  task automatic wait_halted();
    begin
      while (!dbg_bus.halt_ack) @(posedge clk);
    end
  endtask

  task automatic step_one();
    begin
      dbg_bus.step_req <= 1'b1;
      @(posedge clk);
      dbg_bus.step_req <= 1'b0;
      while (!dbg_bus.step_ack) @(posedge clk);
      @(posedge clk);
    end
  endtask

  task automatic step_and_compare(input string tag);
    begin
      step_one();
      u_ref.step(1'b0, 1'b0, 8'h00);
      compare_state(tag);
    end
  endtask

  task automatic compare_state(input string tag);
    begin
      if (dut.s_q !== u_ref.s) begin
        $display("STATE MISMATCH (%s)", tag);
        $display("DUT: PC=%04h SP=%04h A=%02h F=%02h B=%02h C=%02h D=%02h E=%02h H=%02h L=%02h IX=%04h IY=%04h I=%02h R=%02h IM=%0d IFF1=%0d IFF2=%0d",
                 dut.s_q.PC, dut.s_q.SP, dut.s_q.A, dut.s_q.F, dut.s_q.B, dut.s_q.C, dut.s_q.D, dut.s_q.E,
                 dut.s_q.H, dut.s_q.L, dut.s_q.IX, dut.s_q.IY, dut.s_q.I, dut.s_q.R, dut.s_q.IM, dut.s_q.IFF1, dut.s_q.IFF2);
        $display("REF: PC=%04h SP=%04h A=%02h F=%02h B=%02h C=%02h D=%02h E=%02h H=%02h L=%02h IX=%04h IY=%04h I=%02h R=%02h IM=%0d IFF1=%0d IFF2=%0d",
                 u_ref.s.PC, u_ref.s.SP, u_ref.s.A, u_ref.s.F, u_ref.s.B, u_ref.s.C, u_ref.s.D, u_ref.s.E,
                 u_ref.s.H, u_ref.s.L, u_ref.s.IX, u_ref.s.IY, u_ref.s.I, u_ref.s.R, u_ref.s.IM, u_ref.s.IFF1, u_ref.s.IFF2);
        $fatal(1);
      end
    end
  endtask

  task automatic run_stepped(input int unsigned steps, input string tag_prefix);
    int i;
    begin
      for (i = 0; i < steps; i++) begin
        step_one();
        u_ref.step(1'b0, 1'b0, 8'h00);
        compare_state({tag_prefix, " step=", i});
      end
    end
  endtask

  task automatic modeup_to_tier(
      input logic [7:0] target,
      input logic [15:0] entry,
      input string tag
  );
    begin
      write_modeup(16'h0000, target, entry);
      dbg_bus.halt_req = 1'b1;
      wait_halted();
      step_one();
      u_ref.step(1'b0, 1'b0, 8'h00);
      compare_state({tag, " modeup"});
    end
  endtask

  task automatic run_until_halt(input int unsigned max_steps, input string tag);
    int i;
    begin
      for (i = 0; i < int'(max_steps); i++) begin
        step_one();
        u_ref.step(1'b0, 1'b0, 8'h00);
        compare_state({tag, " step=", i});
        if (dut.s_q.halt_latch) return;
      end
      $fatal(1, "Timeout waiting for HALT (%s)", tag);
    end
  endtask

  task automatic run_daa_case(
      input logic [7:0] a_init,
      input logic [7:0] add_val,
      input logic [7:0] expected,
      input logic expected_carry,
      input string tag
  );
    begin
      reset_dut_and_ref();
      mem_write_byte(16'h0000, 8'h3E);
      mem_write_byte(16'h0001, a_init);
      mem_write_byte(16'h0002, 8'hC6);
      mem_write_byte(16'h0003, add_val);
      mem_write_byte(16'h0004, 8'h27);

      dbg_bus.halt_req = 1'b1;
      wait_halted();
      run_stepped(3, tag);
      if (dut.s_q.A !== expected) begin
        $fatal(1, "DAA mismatch (%s): got %02h expected %02h", tag, dut.s_q.A, expected);
      end
      if (((dut.s_q.F & Z85_F_C) != 0) != expected_carry) begin
        $fatal(1, "DAA carry mismatch (%s): got %0d expected %0d", tag, (dut.s_q.F & Z85_F_C) != 0, expected_carry);
      end
    end
  endtask

  task automatic write_zex_boot(input logic [15:0] entry);
    begin
      // 0x0000: JP 0x0040
      mem_write_byte(16'h0000, 8'hC3);
      mem_write_byte(16'h0001, 8'h40);
      mem_write_byte(16'h0002, 8'h00);
      mem_write_byte(16'h0003, 8'h00);
      mem_write_byte(16'h0004, 8'h00);

      // 0x0005: BDOS stub (OUT to port 0, 0xFF signals completion)
      mem_write_byte(16'h0005, 8'hF5);
      mem_write_byte(16'h0006, 8'hC5);
      mem_write_byte(16'h0007, 8'hD5);
      mem_write_byte(16'h0008, 8'hE5);
      mem_write_byte(16'h0009, 8'h79);
      mem_write_byte(16'h000A, 8'hFE);
      mem_write_byte(16'h000B, 8'h02);
      mem_write_byte(16'h000C, 8'h28);
      mem_write_byte(16'h000D, 8'h0A);
      mem_write_byte(16'h000E, 8'hFE);
      mem_write_byte(16'h000F, 8'h09);
      mem_write_byte(16'h0010, 8'h28);
      mem_write_byte(16'h0011, 8'h0B);
      mem_write_byte(16'h0012, 8'hFE);
      mem_write_byte(16'h0013, 8'h00);
      mem_write_byte(16'h0014, 8'h28);
      mem_write_byte(16'h0015, 8'h11);
      mem_write_byte(16'h0016, 8'h18);
      mem_write_byte(16'h0017, 8'h13);
      mem_write_byte(16'h0018, 8'h7B);
      mem_write_byte(16'h0019, 8'hD3);
      mem_write_byte(16'h001A, 8'h00);
      mem_write_byte(16'h001B, 8'h18);
      mem_write_byte(16'h001C, 8'h0E);
      mem_write_byte(16'h001D, 8'h1A);
      mem_write_byte(16'h001E, 8'hFE);
      mem_write_byte(16'h001F, 8'h24);
      mem_write_byte(16'h0020, 8'h28);
      mem_write_byte(16'h0021, 8'h09);
      mem_write_byte(16'h0022, 8'hD3);
      mem_write_byte(16'h0023, 8'h00);
      mem_write_byte(16'h0024, 8'h13);
      mem_write_byte(16'h0025, 8'h18);
      mem_write_byte(16'h0026, 8'hF6);
      mem_write_byte(16'h0027, 8'h3E);
      mem_write_byte(16'h0028, 8'hFF);
      mem_write_byte(16'h0029, 8'hD3);
      mem_write_byte(16'h002A, 8'h00);
      mem_write_byte(16'h002B, 8'hE1);
      mem_write_byte(16'h002C, 8'hD1);
      mem_write_byte(16'h002D, 8'hC1);
      mem_write_byte(16'h002E, 8'hF1);
      mem_write_byte(16'h002F, 8'hC9);

      // 0x0040: MODEUP to P2 and jump to entry.
      write_modeup(16'h0040, 8'(CARBON_Z80_DERIVED_TIER_P2_Z80), entry);
    end
  endtask

  task automatic run_zex_harness(
      input string hex_path,
      input string bin_path,
      input logic [15:0] entry,
      input int unsigned timeout_cycles
  );
    int unsigned cycles;
    begin
      reset_dut_and_ref();
      if ((hex_path == "") && (bin_path == "")) begin
        $display("tb_z85: ZEX skipped (no +zex_hex or +zex_bin).");
        return;
      end

      if (hex_path != "") begin
        u_mem.mem_load_hex(hex_path);
        $readmemh(hex_path, u_ref.mem);
      end else begin
        u_mem.mem_load_bin(bin_path);
        $readmemb(bin_path, u_ref.mem);
      end

      write_zex_boot(entry);

      zex_done = 1'b0;
      dbg_bus.halt_req = 1'b0;
      dbg_bus.run_req  = 1'b1;
      @(posedge clk);
      dbg_bus.run_req  = 1'b0;

      for (cycles = 0; cycles < timeout_cycles; cycles++) begin
        if (zex_done) break;
        @(posedge clk);
      end

      if (!zex_done) begin
        $fatal(1, "ZEX timeout after %0d cycles", timeout_cycles);
      end
    end
  endtask

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      zex_done <= 1'b0;
      zex_last_out <= 8'h00;
    end else if (run_zex && io_fire && (io_bus.req_op == CARBON_FABRIC_XACT_WRITE)) begin
      if (io_bus.req_addr[7:0] == 8'h00) begin
        zex_last_out <= io_bus.req_wdata[7:0];
        if (io_bus.req_wdata[7:0] == 8'hFF) begin
          zex_done <= 1'b1;
        end else begin
          $write("%c", io_bus.req_wdata[7:0]);
        end
      end
    end
  end

  initial begin
    logic [31:0] csr_data;
    logic csr_fault;

    run_zex = RUN_ZEX;
    zex_hex_path = "";
    zex_bin_path = "";
    zex_entry = 16'h0100;
    zex_timeout = 200000;

    if ($value$plusargs("zex_hex=%s", zex_hex_path)) run_zex = 1'b1;
    if ($value$plusargs("zex_bin=%s", zex_bin_path)) run_zex = 1'b1;
    void'($value$plusargs("zex_entry=%h", zex_entry));
    void'($value$plusargs("zex_timeout=%d", zex_timeout));

    if (run_zex) begin
      if ((zex_hex_path == "") && (zex_bin_path == "")) begin
        $display("tb_z85: ZEX SKIP (no binary provided)");
        $finish;
      end
      run_zex_harness(zex_hex_path, zex_bin_path, zex_entry, zex_timeout);
      $display("tb_z85: ZEX PASS");
      $finish;
    end

    // ----------------------------------------------------------------------
    // DAA edge cases
    // ----------------------------------------------------------------------
    run_daa_case(8'h09, 8'h01, 8'h10, 1'b0, "daa_09+01");
    run_daa_case(8'h15, 8'h27, 8'h42, 1'b0, "daa_15+27");
    run_daa_case(8'h99, 8'h99, 8'h98, 1'b1, "daa_99+99");

    // ----------------------------------------------------------------------
    // CB ops (SLL/BIT/RES/SET + XY flags)
    // ----------------------------------------------------------------------
    reset_dut_and_ref();
    mem_write_byte(16'h0100, 8'h06); // LD B,80
    mem_write_byte(16'h0101, 8'h80);
    mem_write_byte(16'h0102, 8'hCB); // SLL B
    mem_write_byte(16'h0103, 8'h30);
    mem_write_byte(16'h0104, 8'hAF); // XOR A
    mem_write_byte(16'h0105, 8'h06); // LD B,28
    mem_write_byte(16'h0106, 8'h28);
    mem_write_byte(16'h0107, 8'hCB); // BIT 0,B
    mem_write_byte(16'h0108, 8'h40);
    mem_write_byte(16'h0109, 8'hCB); // RES 0,B
    mem_write_byte(16'h010A, 8'h80);
    mem_write_byte(16'h010B, 8'hCB); // SET 0,B
    mem_write_byte(16'h010C, 8'hC0);
    mem_write_byte(16'h010D, 8'h76); // HALT

    modeup_to_tier(8'(CARBON_Z80_DERIVED_TIER_P2_Z80), 16'h0100, "cb");
    step_and_compare("cb ld b");
    step_and_compare("cb sll");
    if (dut.s_q.B !== 8'h01) $fatal(1, "SLL B mismatch: got %02h expected 01", dut.s_q.B);
    if ((dut.s_q.F & Z85_F_C) == 0) $fatal(1, "SLL B carry mismatch");
    step_and_compare("cb xor a");
    step_and_compare("cb ld b 28");
    step_and_compare("cb bit");
    if (dut.s_q.F !== 8'h7C) $fatal(1, "BIT XY mismatch: got %02h expected 7C", dut.s_q.F);
    step_and_compare("cb res");
    step_and_compare("cb set");
    if (dut.s_q.B !== 8'h29) $fatal(1, "SET B mismatch: got %02h expected 29", dut.s_q.B);
    step_and_compare("cb halt");

    // ----------------------------------------------------------------------
    // IX DDCB BIT (XY from high byte of EA)
    // ----------------------------------------------------------------------
    reset_dut_and_ref();
    mem_write_byte(16'h0100, 8'hDD); // LD IX,2800
    mem_write_byte(16'h0101, 8'h21);
    mem_write_byte(16'h0102, 8'h00);
    mem_write_byte(16'h0103, 8'h28);
    mem_write_byte(16'h0104, 8'hDD); // LD (IX+5),00
    mem_write_byte(16'h0105, 8'h36);
    mem_write_byte(16'h0106, 8'h05);
    mem_write_byte(16'h0107, 8'h00);
    mem_write_byte(16'h0108, 8'hDD); // BIT 0,(IX+5)
    mem_write_byte(16'h0109, 8'hCB);
    mem_write_byte(16'h010A, 8'h05);
    mem_write_byte(16'h010B, 8'h46);
    mem_write_byte(16'h010C, 8'h76);

    modeup_to_tier(8'(CARBON_Z80_DERIVED_TIER_P2_Z80), 16'h0100, "ddcb");
    step_and_compare("ddcb ld ix");
    step_and_compare("ddcb ld (ix+5)");
    step_and_compare("ddcb bit");
    if (dut.s_q.F !== 8'h7C) $fatal(1, "DDCB BIT XY mismatch: got %02h expected 7C", dut.s_q.F);
    step_and_compare("ddcb halt");

    // ----------------------------------------------------------------------
    // IY DDCB SLL (indexed CB displacement)
    // ----------------------------------------------------------------------
    reset_dut_and_ref();
    mem_write_byte(16'h0120, 8'hFD); // LD IY,3000
    mem_write_byte(16'h0121, 8'h21);
    mem_write_byte(16'h0122, 8'h00);
    mem_write_byte(16'h0123, 8'h30);
    mem_write_byte(16'h0124, 8'hFD); // LD (IY+4),80
    mem_write_byte(16'h0125, 8'h36);
    mem_write_byte(16'h0126, 8'h04);
    mem_write_byte(16'h0127, 8'h80);
    mem_write_byte(16'h0128, 8'hFD); // SLL (IY+4)
    mem_write_byte(16'h0129, 8'hCB);
    mem_write_byte(16'h012A, 8'h04);
    mem_write_byte(16'h012B, 8'h36);
    mem_write_byte(16'h012C, 8'h76);

    modeup_to_tier(8'(CARBON_Z80_DERIVED_TIER_P2_Z80), 16'h0120, "iycb");
    step_and_compare("iycb ld iy");
    step_and_compare("iycb ld (iy+4)");
    step_and_compare("iycb sll");
    if (u_mem.mem[16'h3004] !== 8'h01) $fatal(1, "SLL (IY+4) mem mismatch");
    if ((dut.s_q.F & Z85_F_C) == 0) $fatal(1, "SLL (IY+4) carry mismatch");
    step_and_compare("iycb halt");

    // ----------------------------------------------------------------------
    // LDIR
    // ----------------------------------------------------------------------
    reset_dut_and_ref();
    mem_write_byte(16'h2000, 8'h11);
    mem_write_byte(16'h2001, 8'h22);
    mem_write_byte(16'h2002, 8'h33);
    mem_write_byte(16'h2003, 8'h44);
    mem_write_byte(16'h0140, 8'h21); // LD HL,2000
    mem_write_byte(16'h0141, 8'h00);
    mem_write_byte(16'h0142, 8'h20);
    mem_write_byte(16'h0143, 8'h11); // LD DE,2100
    mem_write_byte(16'h0144, 8'h00);
    mem_write_byte(16'h0145, 8'h21);
    mem_write_byte(16'h0146, 8'h01); // LD BC,0004
    mem_write_byte(16'h0147, 8'h04);
    mem_write_byte(16'h0148, 8'h00);
    mem_write_byte(16'h0149, 8'hED); // LDIR
    mem_write_byte(16'h014A, 8'hB0);
    mem_write_byte(16'h014B, 8'h76); // HALT

    modeup_to_tier(8'(CARBON_Z80_DERIVED_TIER_P2_Z80), 16'h0140, "ldir");
    run_until_halt(40, "ldir");
    if (u_mem.mem[16'h2100] !== 8'h11 || u_mem.mem[16'h2101] !== 8'h22 ||
        u_mem.mem[16'h2102] !== 8'h33 || u_mem.mem[16'h2103] !== 8'h44) begin
      $fatal(1, "LDIR memory mismatch");
    end
    if (pack16(dut.s_q.H, dut.s_q.L) !== 16'h2004 ||
        pack16(dut.s_q.D, dut.s_q.E) !== 16'h2104 ||
        pack16(dut.s_q.B, dut.s_q.C) !== 16'h0000) begin
      $fatal(1, "LDIR register mismatch");
    end

    // ----------------------------------------------------------------------
    // CPIR
    // ----------------------------------------------------------------------
    reset_dut_and_ref();
    mem_write_byte(16'h2400, 8'h11);
    mem_write_byte(16'h2401, 8'h77);
    mem_write_byte(16'h2402, 8'h22);
    mem_write_byte(16'h2403, 8'h33);
    mem_write_byte(16'h0160, 8'h21); // LD HL,2400
    mem_write_byte(16'h0161, 8'h00);
    mem_write_byte(16'h0162, 8'h24);
    mem_write_byte(16'h0163, 8'h01); // LD BC,0004
    mem_write_byte(16'h0164, 8'h04);
    mem_write_byte(16'h0165, 8'h00);
    mem_write_byte(16'h0166, 8'h3E); // LD A,77
    mem_write_byte(16'h0167, 8'h77);
    mem_write_byte(16'h0168, 8'hED); // CPIR
    mem_write_byte(16'h0169, 8'hB1);
    mem_write_byte(16'h016A, 8'h76);

    modeup_to_tier(8'(CARBON_Z80_DERIVED_TIER_P2_Z80), 16'h0160, "cpir");
    run_until_halt(40, "cpir");
    if (pack16(dut.s_q.H, dut.s_q.L) !== 16'h2402 ||
        pack16(dut.s_q.B, dut.s_q.C) !== 16'h0002) begin
      $fatal(1, "CPIR register mismatch");
    end
    if ((dut.s_q.F & Z85_F_Z) == 0) $fatal(1, "CPIR Z flag mismatch");

    // ----------------------------------------------------------------------
    // INIR
    // ----------------------------------------------------------------------
    reset_dut_and_ref();
    io_write_byte(16'h0010, 8'hA5);
    mem_write_byte(16'h0180, 8'h06); // LD B,02
    mem_write_byte(16'h0181, 8'h02);
    mem_write_byte(16'h0182, 8'h0E); // LD C,10
    mem_write_byte(16'h0183, 8'h10);
    mem_write_byte(16'h0184, 8'h21); // LD HL,2200
    mem_write_byte(16'h0185, 8'h00);
    mem_write_byte(16'h0186, 8'h22);
    mem_write_byte(16'h0187, 8'hED); // INIR
    mem_write_byte(16'h0188, 8'hB2);
    mem_write_byte(16'h0189, 8'h76);

    modeup_to_tier(8'(CARBON_Z80_DERIVED_TIER_P2_Z80), 16'h0180, "inir");
    run_until_halt(40, "inir");
    if (u_mem.mem[16'h2200] !== 8'hA5 || u_mem.mem[16'h2201] !== 8'hA5) begin
      $fatal(1, "INIR memory mismatch");
    end
    if (dut.s_q.B != 8'h00) $fatal(1, "INIR B mismatch");

    // ----------------------------------------------------------------------
    // OTIR
    // ----------------------------------------------------------------------
    reset_dut_and_ref();
    mem_write_byte(16'h2300, 8'h11);
    mem_write_byte(16'h2301, 8'h22);
    mem_write_byte(16'h01A0, 8'h06); // LD B,02
    mem_write_byte(16'h01A1, 8'h02);
    mem_write_byte(16'h01A2, 8'h0E); // LD C,12
    mem_write_byte(16'h01A3, 8'h12);
    mem_write_byte(16'h01A4, 8'h21); // LD HL,2300
    mem_write_byte(16'h01A5, 8'h00);
    mem_write_byte(16'h01A6, 8'h23);
    mem_write_byte(16'h01A7, 8'hED); // OTIR
    mem_write_byte(16'h01A8, 8'hB3);
    mem_write_byte(16'h01A9, 8'h76);

    modeup_to_tier(8'(CARBON_Z80_DERIVED_TIER_P2_Z80), 16'h01A0, "otir");
    run_until_halt(40, "otir");
    if (u_io.mem[16'h0012] !== 8'h22) $fatal(1, "OTIR port mismatch");
    if (dut.s_q.B != 8'h00) $fatal(1, "OTIR B mismatch");

    // ----------------------------------------------------------------------
    // IM2 vectoring (free-run)
    // ----------------------------------------------------------------------
    reset_dut_and_ref();
    write_modeup(16'h0000, 8'(CARBON_Z80_DERIVED_TIER_P2_Z80), 16'h01C0);
    mem_write_byte(16'h01C0, 8'h3E);
    mem_write_byte(16'h01C1, 8'h12);
    mem_write_byte(16'h01C2, 8'hED);
    mem_write_byte(16'h01C3, 8'h47);
    mem_write_byte(16'h01C4, 8'hED);
    mem_write_byte(16'h01C5, 8'h5E);
    mem_write_byte(16'h01C6, 8'hFB);
    mem_write_byte(16'h01C7, 8'h76);

    mem_write_byte(16'h1234, 8'h00);
    mem_write_byte(16'h1235, 8'h02);
    mem_write_byte(16'h0200, 8'h00);
    mem_write_byte(16'h0201, 8'h76);

    dbg_bus.halt_req = 1'b0;
    dbg_bus.run_req  = 1'b1;
    repeat (2) @(posedge clk);
    dbg_bus.run_req  = 1'b0;

    while (!dut.s_q.halt_latch) @(posedge clk);

    irq_bus.irq_valid  <= 1'b1;
    irq_bus.irq_vector <= {1'b0, 8'h34};
    while (!irq_bus.irq_ack) @(posedge clk);
    irq_bus.irq_valid  <= 1'b0;

    while (!(dut.s_q.halt_latch && dut.s_q.PC == 16'h0202)) @(posedge clk);

    // ----------------------------------------------------------------------
    // Illegal opcode traps in P0/P1
    // ----------------------------------------------------------------------
    reset_dut_and_ref();
    mem_write_byte(16'h0000, 8'hCB);
    mem_write_byte(16'h0001, 8'h00);
    dbg_bus.halt_req = 1'b1;
    wait_halted();
    step_one();
    u_csr_bfm.csr_read(CARBON_CSR_CAUSE, 2'b00, csr_data, csr_fault);
    if (csr_fault) $fatal(1, "CSR read fault on illegal P0 test");
    if (csr_data !== Z85_CAUSE_ILLEGAL_INSN) $fatal(1, "P0 illegal cause mismatch: %08h", csr_data);

    reset_dut_and_ref();
    mem_write_byte(16'h0100, 8'hDD);
    mem_write_byte(16'h0101, 8'h21);
    mem_write_byte(16'h0102, 8'h00);
    mem_write_byte(16'h0103, 8'h00);
    modeup_to_tier(8'(CARBON_Z80_DERIVED_TIER_P1_I8085), 16'h0100, "p1");
    step_one();
    u_csr_bfm.csr_read(CARBON_CSR_CAUSE, 2'b00, csr_data, csr_fault);
    if (csr_fault) $fatal(1, "CSR read fault on illegal P1 test");
    if (csr_data !== Z85_CAUSE_ILLEGAL_INSN) $fatal(1, "P1 illegal cause mismatch: %08h", csr_data);

    reset_dut_and_ref();
    mem_write_byte(16'h0100, 8'h20); // RIM
    mem_write_byte(16'h0101, 8'h76); // HALT
    modeup_to_tier(8'(CARBON_Z80_DERIVED_TIER_P1_I8085), 16'h0100, "p1_rim");
    step_and_compare("p1 rim");
    if (dut.s_q.A !== 8'h00) $fatal(1, "P1 RIM stub mismatch");
    step_and_compare("p1 rim halt");

    $display("tb_z85: PASS");
    $finish;
  end

endmodule
