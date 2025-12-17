`timescale 1ns/1ps

module tb_8096;
  import carbon_arch_pkg::*;

  logic clk;
  logic rst_n;

  // Fabric + control interfaces
  fabric_if mem_if (.*);
  fabric_if io_if  (.*);
  irq_if    irq    (.*);
  csr_if    csr    (.*);
  dbg_if    dbg    (.*);

  cpu_8096 dut (
      .clk(clk),
      .rst_n(rst_n),
      .mem_if(mem_if),
      .io_if(io_if),
      .irq(irq),
      .csr(csr),
      .dbg(dbg)
  );

  fabric_mem_bfm #(
      .MEM_BYTES(4096),
      .RESP_LATENCY(1)
  ) mem_bfm (
      .clk(clk),
      .rst_n(rst_n),
      .bus(mem_if)
  );

  // Optional IO memory (CPU v1 keeps io_if idle)
  fabric_mem_bfm #(
      .MEM_BYTES(4096),
      .RESP_LATENCY(1)
  ) io_bfm (
      .clk(clk),
      .rst_n(rst_n),
      .bus(io_if)
  );

  csr_bfm csrdrv (
      .clk(clk),
      .rst_n(rst_n),
      .csr(csr)
  );

  localparam logic [31:0] X96_CAUSE_TURBO_DENIED = 32'h0000_0020;

  initial begin
    clk = 1'b0;
    forever #5 clk = ~clk;
  end

  initial begin
    dbg.halt_req   = 1'b0;
    dbg.run_req    = 1'b0;
    dbg.step_req   = 1'b0;
    dbg.bp_valid   = 1'b0;
    dbg.bp_write   = 1'b0;
    dbg.bp_index   = '0;
    dbg.bp_addr    = '0;
    dbg.bp_kind    = '0;
    dbg.bp_enable  = 1'b0;
    dbg.trace_ready = 1'b1;

    irq.irq_valid   = 1'b0;
    irq.irq_vector  = '0;
    irq.irq_prio    = '0;
    irq.irq_pending = '0;
  end

  task automatic mem_clear();
    int unsigned i;
    begin
      for (i = 0; i < 4096; i++) begin
        mem_bfm.mem[i] = 8'h00;
      end
    end
  endtask

  task automatic mem_load_bytes(input int unsigned base, input byte data[], input int unsigned n);
    int unsigned i;
    begin
      for (i = 0; i < n; i++) begin
        mem_bfm.mem[base + i] = data[i];
      end
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

  initial begin
    logic [31:0] rdata;
    logic fault;

    rst_n = 1'b0;
    repeat (2) @(posedge clk);

    // ----------------------------------------------------------------------
    // Phase 1: Turbo opcode traps in P0
    // ----------------------------------------------------------------------
    do_reset();
    mem_clear();

    byte prog1[] = '{8'h63, 8'h00, 8'h00, 8'h34, 8'h12, 8'hF4};
    mem_load_bytes(0, prog1, prog1.size());

    // Wait for trap halt.
    wait (dbg.halt_ack);
    csrdrv.csr_read(CARBON_CSR_CAUSE, 2'(0), rdata, fault);
    if (fault) $fatal(1, "CSR_CAUSE read fault");
    if (rdata !== X96_CAUSE_TURBO_DENIED) begin
      $fatal(1, "Expected TURBO_DENIED cause, got %08x", rdata);
    end

    // ----------------------------------------------------------------------
    // Phase 2: P0 subset + MODEUP to P7 + turbo exec
    // ----------------------------------------------------------------------
    do_reset();
    mem_clear();

    // Clear STRICT so turbo is permitted once tier is P7.
    csrdrv.csr_write(CARBON_CSR_MODEFLAGS, 32'h0000_0000, 4'hF, 2'(1), fault);
    if (fault) $fatal(1, "CSR_MODEFLAGS write fault");

    byte prog2[] = '{
        // AX = 0xFFFF; DS = AX
        8'hB8, 8'hFF, 8'hFF,
        8'h8E, 8'hD8,
        // AX = 0x1234; [DS:0x0100] = AX (wraps to 0x00F0)
        8'hB8, 8'h34, 8'h12,
        8'h89, 8'h06, 8'h00, 8'h01,
        // AX = 3; BX = 4; AX += BX
        8'hB8, 8'h03, 8'h00,
        8'hBB, 8'h04, 8'h00,
        8'h01, 8'hD8,
        // push/pop AX
        8'h50,
        8'hB8, 8'h00, 8'h00,
        8'h58,
        // branch (ZF=1 -> skip BX=0x1111)
        8'h39, 8'hC0,
        8'h74, 8'h03,
        8'hBB, 8'h11, 8'h11,
        8'hBB, 8'h22, 8'h22,
        // MODEUP to P7, entry_ip=0x0028
        8'h62, 8'h00, 8'h07, 8'h28, 8'h00,
        // P7 code: MOVX R0,0x1234; MOVX AX,R0; HLT
        8'h63, 8'h00, 8'h00, 8'h34, 8'h12,
        8'h63, 8'h02, 8'h00, 8'h00,
        8'hF4
    };
    mem_load_bytes(0, prog2, prog2.size());

    // Wait for HLT.
    wait (dbg.halt_ack);

    // Validate wrap store at physical 0x00F0.
    if (mem_bfm.mem[16'h00F0] !== 8'h34 || mem_bfm.mem[16'h00F1] !== 8'h12) begin
      $fatal(1, "Segmentation wrap store mismatch at 0x00F0");
    end

    // Validate branch and turbo result via hierarchical access.
    if (dut.u_core.gpr_q[0] !== 16'h1234) $fatal(1, "AX mismatch: %04x", dut.u_core.gpr_q[0]);
    if (dut.u_core.gpr_q[3] !== 16'h2222) $fatal(1, "BX mismatch: %04x", dut.u_core.gpr_q[3]);

    $display("tb_8096: PASS");
    $finish;
  end

endmodule

