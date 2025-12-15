`timescale 1ns/1ps

module tb_z85;
  import z85_regfile_pkg::*;

  logic clk;
  logic rst_n;

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

  task automatic mem_write_byte(input int unsigned addr, input logic [7:0] v);
    begin
      u_mem.mem[addr] = v;
      u_ref.mem[addr[15:0]] = v;
    end
  endtask

  task automatic reset_dut_and_ref();
    begin
      rst_n = 1'b0;
      dbg_bus.halt_req  = 1'b0;
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

  initial begin
    reset_dut_and_ref();

    // ----------------------------------------------------------------------
    // Directed test 1: DAA
    // ----------------------------------------------------------------------
    // Program @0x0000:
    //   LD A,09
    //   ADD A,01
    //   DAA
    mem_write_byte(16'h0000, 8'h3E);
    mem_write_byte(16'h0001, 8'h09);
    mem_write_byte(16'h0002, 8'hC6);
    mem_write_byte(16'h0003, 8'h01);
    mem_write_byte(16'h0004, 8'h27);

    dbg_bus.halt_req = 1'b1;
    wait_halted();
    run_stepped(3, "daa");
    if (dut.s_q.A !== 8'h10) $fatal(1, "DAA result mismatch: got %02h expected 10", dut.s_q.A);

    // ----------------------------------------------------------------------
    // Directed test 2: CB ops (SLL/BIT/RES/SET)
    // ----------------------------------------------------------------------
    reset_dut_and_ref();
    mem_write_byte(16'h0000, 8'h06); // LD B,80
    mem_write_byte(16'h0001, 8'h80);
    mem_write_byte(16'h0002, 8'hCB); // SLL B
    mem_write_byte(16'h0003, 8'h30);
    mem_write_byte(16'h0004, 8'hCB); // BIT 0,B
    mem_write_byte(16'h0005, 8'h40);
    mem_write_byte(16'h0006, 8'hCB); // RES 0,B
    mem_write_byte(16'h0007, 8'h80);
    mem_write_byte(16'h0008, 8'hCB); // SET 0,B
    mem_write_byte(16'h0009, 8'hC0);

    dbg_bus.halt_req = 1'b1;
    wait_halted();
    run_stepped(5, "cb");

    // ----------------------------------------------------------------------
    // Directed test 3: IX + DDCB (BIT uses XY from high byte of EA)
    // ----------------------------------------------------------------------
    reset_dut_and_ref();
    mem_write_byte(16'h0000, 8'hDD); // LD IX,2800
    mem_write_byte(16'h0001, 8'h21);
    mem_write_byte(16'h0002, 8'h00);
    mem_write_byte(16'h0003, 8'h28);
    mem_write_byte(16'h0004, 8'hDD); // LD (IX+5),00
    mem_write_byte(16'h0005, 8'h36);
    mem_write_byte(16'h0006, 8'h05);
    mem_write_byte(16'h0007, 8'h00);
    mem_write_byte(16'h0008, 8'hDD); // BIT 0,(IX+5) -> DDCB 05 46
    mem_write_byte(16'h0009, 8'hCB);
    mem_write_byte(16'h000A, 8'h05);
    mem_write_byte(16'h000B, 8'h46);

    dbg_bus.halt_req = 1'b1;
    wait_halted();
    run_stepped(3, "ddcb");
    if (dut.s_q.F !== 8'h7C) $fatal(1, "DDCB BIT XY mismatch: got %02h expected 7C", dut.s_q.F);

    // ----------------------------------------------------------------------
    // Directed test 4: IM2 vectoring (free-run)
    // ----------------------------------------------------------------------
    reset_dut_and_ref();
    // Program:
    //   LD A,12
    //   LD I,A
    //   IM 2
    //   EI
    //   HALT
    mem_write_byte(16'h0000, 8'h3E);
    mem_write_byte(16'h0001, 8'h12);
    mem_write_byte(16'h0002, 8'hED);
    mem_write_byte(16'h0003, 8'h47);
    mem_write_byte(16'h0004, 8'hED);
    mem_write_byte(16'h0005, 8'h5E);
    mem_write_byte(16'h0006, 8'hFB);
    mem_write_byte(16'h0007, 8'h76);

    // IM2 vector table @ 0x1234 -> handler 0x0100 (NOP; HALT)
    mem_write_byte(16'h1234, 8'h00);
    mem_write_byte(16'h1235, 8'h01);
    mem_write_byte(16'h0100, 8'h00);
    mem_write_byte(16'h0101, 8'h76);

    // Run without debug halt until first HALT.
    dbg_bus.halt_req = 1'b0;
    dbg_bus.run_req  = 1'b1;
    repeat (2) @(posedge clk);
    dbg_bus.run_req  = 1'b0;

    while (!dut.s_q.halt_latch) @(posedge clk);

    // Assert INT with vector 0x34 (MSB=0 => maskable INT)
    irq_bus.irq_valid  <= 1'b1;
    irq_bus.irq_vector <= {1'b0, 8'h34};
    while (!irq_bus.irq_ack) @(posedge clk);
    irq_bus.irq_valid  <= 1'b0;

    // Wait until handler halts.
    while (!(dut.s_q.halt_latch && dut.s_q.PC == 16'h0102)) @(posedge clk);

    $display("tb_z85: PASS");
    $finish;
  end

endmodule

