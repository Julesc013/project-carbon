`timescale 1ns/1ps

module tb_z480_core_basic;
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
  // Program image (Z480 ISA v1)
  // --------------------------------------------------------------------------
  task automatic write_word(input int unsigned addr, input logic [31:0] data);
    begin
      u_mem.mem[addr + 0] = data[7:0];
      u_mem.mem[addr + 1] = data[15:8];
      u_mem.mem[addr + 2] = data[23:16];
      u_mem.mem[addr + 3] = data[31:24];
    end
  endtask

  initial begin
    // r1 = 0x0040
    write_word(32'h0000_0000, 32'h2001_0040);
    // r2 = 0x1234
    write_word(32'h0000_0004, 32'h2002_1234);
    // STW r2, 0(r1)
    write_word(32'h0000_0008, 32'hAC22_0000);
    // LDW r3, 0(r1)
    write_word(32'h0000_000C, 32'h8C23_0000);
    // ADD r4, r2, r3
    write_word(32'h0000_0010, 32'h0043_2020);
    // r5 = 0x2468
    write_word(32'h0000_0014, 32'h2005_2468);
    // SUB r6, r4, r5
    write_word(32'h0000_0018, 32'h0085_3022);
    // BEQ r6, r0, +3 (to PASS)
    write_word(32'h0000_001C, 32'h10C0_0003);
    // r7 = 0x0BAD (error)
    write_word(32'h0000_0020, 32'h2007_0BAD);
    // STW r7, 4(r1)
    write_word(32'h0000_0024, 32'hAC27_0004);
    // J END
    write_word(32'h0000_0028, 32'h0800_000E);
    // PASS: r7 = 0x0ACE
    write_word(32'h0000_002C, 32'h2007_0ACE);
    // STW r7, 4(r1)
    write_word(32'h0000_0030, 32'hAC27_0004);
    // J END
    write_word(32'h0000_0034, 32'h0800_000E);
    // END: J END
    write_word(32'h0000_0038, 32'h0800_000E);
  end

  // --------------------------------------------------------------------------
  // Test sequence
  // --------------------------------------------------------------------------
  int unsigned cycles;
  logic [31:0] pass_word;

  initial begin
    rst_n = 1'b0;
    repeat (10) @(posedge clk);
    rst_n = 1'b1;

    pass_word = 32'h0000_0ACE;
    cycles = 0;
    while (cycles < 2000) begin
      @(posedge clk);
      if ({u_mem.mem[16'h0047], u_mem.mem[16'h0046],
           u_mem.mem[16'h0045], u_mem.mem[16'h0044]} == pass_word) begin
        $display("tb_z480_core_basic: PASS");
        $finish;
      end
      cycles++;
    end

    $fatal(1, "tb_z480_core_basic: timeout waiting for PASS word");
  end

endmodule
