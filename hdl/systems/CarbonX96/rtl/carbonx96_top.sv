// Project Carbon - Systems
// carbonx96_top: CarbonX96 system (8096 + 8097 with P7 turbo enabled).

module carbonx96_top (
    input logic clk,
    input logic rst_n,
    output logic [31:0] signature,
    output logic        poweroff
);
  import carbon_arch_pkg::*;
  import carbon_memmap_pkg::*;

  localparam int unsigned ADDR_W = 32;
  localparam int unsigned DATA_W = 32;
  localparam int unsigned ID_W   = 4;

  localparam int unsigned M = 3; // 8096 mem, 8096 io, 8097 mem
  localparam int unsigned N = 3; // mmio, rom, ram(default)

  fabric_if #(
      .ADDR_W(ADDR_W),
      .DATA_W(DATA_W),
      .ID_W(ID_W)
  ) m_if[M] (
      .clk(clk),
      .rst_n(rst_n)
  );

  fabric_if #(
      .ADDR_W(ADDR_W),
      .DATA_W(DATA_W),
      .ID_W(ID_W)
  ) s_if[N] (
      .clk(clk),
      .rst_n(rst_n)
  );

  localparam logic [ADDR_W-1:0] SLAVE_BASE [N] = '{
      ADDR_W'(CARBON_SYSX86_MMIO_BASE),
      ADDR_W'(CARBON_SYSX86_ROM_BASE),
      32'hFFFF_FFFF
  };
  localparam logic [ADDR_W-1:0] SLAVE_MASK [N] = '{
      ADDR_W'(CARBON_SYSX86_MMIO_MASK),
      ADDR_W'(CARBON_SYSX86_ROM_MASK),
      32'hFFFF_FFFF
  };

  fabric_arbiter_mxn #(
      .M(M),
      .N(N),
      .ADDR_W(ADDR_W),
      .DATA_W(DATA_W),
      .ID_W(ID_W),
      .HAS_DEFAULT(1'b1),
      .DEFAULT_SLAVE(2),
      .SLAVE_BASE(SLAVE_BASE),
      .SLAVE_MASK(SLAVE_MASK)
  ) u_fabric (
      .clk(clk),
      .rst_n(rst_n),
      .masters(m_if),
      .slaves(s_if)
  );

  // --------------------------------------------------------------------------
  // 8096 CPU + CSR init (clear STRICT so turbo prefix is allowed after MODEUP)
  // --------------------------------------------------------------------------
  csr_if csr_cpu (
      .clk(clk),
      .rst_n(rst_n)
  );
  dbg_if dbg_cpu (
      .clk(clk),
      .rst_n(rst_n)
  );
  irq_if #(.N(32)) irq_cpu (
      .clk(clk),
      .rst_n(rst_n)
  );

  irq_src_tieoff u_irq_cpu_tie (.irq(irq_cpu));

  cpu_8096 u_cpu (
      .clk(clk),
      .rst_n(rst_n),
      .mem_if(m_if[0]),
      .io_if(m_if[1]),
      .irq(irq_cpu),
      .csr(csr_cpu),
      .dbg(dbg_cpu)
  );

  // Hold the core halted until turbo gating is configured (STRICT cleared).
  logic dbg_halt_req_q;
  logic dbg_run_pulse_q;
  logic dbg_released_q;

  assign dbg_cpu.halt_req = dbg_halt_req_q;
  assign dbg_cpu.run_req  = dbg_run_pulse_q;
  assign dbg_cpu.step_req = 1'b0;
  assign dbg_cpu.bp_valid  = 1'b0;
  assign dbg_cpu.bp_write  = 1'b0;
  assign dbg_cpu.bp_index  = '0;
  assign dbg_cpu.bp_addr   = '0;
  assign dbg_cpu.bp_kind   = '0;
  assign dbg_cpu.bp_enable = 1'b0;
  assign dbg_cpu.trace_ready = 1'b1;

  logic cpu_csr_start;
  logic cpu_csr_busy, cpu_csr_done, cpu_csr_fault;
  logic [31:0] cpu_csr_rdata;
  logic cpu_csr_issued_q;
  logic cpu_csr_init_done_q;

  carbon_csr_master_simple u_cpu_csr_init (
      .clk(clk),
      .rst_n(rst_n),
      .start(cpu_csr_start),
      .write(1'b1),
      .addr(32'(CARBON_CSR_MODEFLAGS)),
      .wdata(32'h0000_0000),
      .wstrb(4'hF),
      .priv(2'(1)),
      .busy(cpu_csr_busy),
      .done_pulse(cpu_csr_done),
      .fault(cpu_csr_fault),
      .rdata(cpu_csr_rdata),
      .csr(csr_cpu)
  );

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      cpu_csr_start <= 1'b0;
      cpu_csr_issued_q <= 1'b0;
      cpu_csr_init_done_q <= 1'b0;
    end else begin
      cpu_csr_start <= 1'b0;
      if (cpu_csr_done) cpu_csr_init_done_q <= 1'b1;
      if (!cpu_csr_init_done_q) begin
        if (!cpu_csr_busy && !cpu_csr_issued_q) begin
          cpu_csr_start <= 1'b1;
          cpu_csr_issued_q <= 1'b1;
        end
        if (cpu_csr_done) cpu_csr_issued_q <= 1'b0;
      end
    end
  end

  // --------------------------------------------------------------------------
  // 8097 FPU + CSR init (P7 tier + STRICT cleared)
  // --------------------------------------------------------------------------
  csr_if csr_fpu (
      .clk(clk),
      .rst_n(rst_n)
  );

  fpu_8097 u_fpu (
      .clk(clk),
      .rst_n(rst_n),
      .csr(csr_fpu),
      .mem_if(m_if[2])
  );

  typedef enum logic [1:0] {FPU_INIT_FLAGS, FPU_INIT_TIER, FPU_INIT_DONE} fpu_init_e;
  fpu_init_e fpu_init_q;
  logic fpu_csr_start;
  logic fpu_csr_busy, fpu_csr_done, fpu_csr_fault;
  logic [31:0] fpu_csr_rdata;
  logic [31:0] fpu_csr_addr;
  logic [31:0] fpu_csr_wdata;
  logic fpu_csr_issued_q;

  carbon_csr_master_simple u_fpu_csr_init (
      .clk(clk),
      .rst_n(rst_n),
      .start(fpu_csr_start),
      .write(1'b1),
      .addr(fpu_csr_addr),
      .wdata(fpu_csr_wdata),
      .wstrb(4'hF),
      .priv(2'(1)),
      .busy(fpu_csr_busy),
      .done_pulse(fpu_csr_done),
      .fault(fpu_csr_fault),
      .rdata(fpu_csr_rdata),
      .csr(csr_fpu)
  );

  always_comb begin
    fpu_csr_addr  = 32'h0;
    fpu_csr_wdata = 32'h0;
    unique case (fpu_init_q)
      FPU_INIT_FLAGS: begin
        fpu_csr_addr  = 32'(CARBON_CSR_8097_MODEFLAGS);
        fpu_csr_wdata = 32'h0000_0000;
      end
      FPU_INIT_TIER: begin
        fpu_csr_addr  = 32'(CARBON_CSR_8097_TIER);
        fpu_csr_wdata = {24'h000000, 8'(CARBON_X86_DERIVED_TIER_P7_TURBO_UNLIMITED)};
      end
      default: begin
      end
    endcase
  end

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      fpu_init_q <= FPU_INIT_FLAGS;
      fpu_csr_start <= 1'b0;
      fpu_csr_issued_q <= 1'b0;
    end else begin
      fpu_csr_start <= 1'b0;
      if (fpu_init_q != FPU_INIT_DONE) begin
        if (!fpu_csr_busy && !fpu_csr_issued_q) begin
          fpu_csr_start <= 1'b1;
          fpu_csr_issued_q <= 1'b1;
        end
        if (fpu_csr_done) begin
          fpu_csr_issued_q <= 1'b0;
          if (fpu_init_q == FPU_INIT_TIER) fpu_init_q <= FPU_INIT_DONE;
          else fpu_init_q <= fpu_init_e'(fpu_init_q + 1'b1);
        end
      end
    end
  end

  wire sys_init_done = cpu_csr_init_done_q && (fpu_init_q == FPU_INIT_DONE);
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      dbg_halt_req_q  <= 1'b1;
      dbg_run_pulse_q <= 1'b0;
      dbg_released_q  <= 1'b0;
    end else begin
      dbg_run_pulse_q <= 1'b0;
      if (sys_init_done && !dbg_released_q) begin
        dbg_halt_req_q  <= 1'b0;
        dbg_run_pulse_q <= 1'b1;
        dbg_released_q  <= 1'b1;
      end
    end
  end

  // --------------------------------------------------------------------------
  // ROM/RAM/MMIO
  // --------------------------------------------------------------------------
  localparam int unsigned ROM_BYTES = CARBON_SYSX86_ROM_BYTES;
  localparam int unsigned ROM_USED  = 48;

  // 8096 boot stub (CarbonX96):
  // - set DS = 0xF000 (MMIO window at 0xF0000)
  // - MODEUP to P7 (entry = next instruction)
  // - execute one turbo op (MOVX) to prove gating works
  // - write "X96!" signature and power off
  localparam logic [ROM_BYTES*8-1:0] ROM_IMAGE = {
      {(ROM_BYTES-ROM_USED){8'h00}},
      8'hFF, 8'hFD, 8'hE9,
      8'h00, 8'h04, 8'h06, 8'h88, 8'h01, 8'hB0,
      8'h00, 8'h03, 8'h06, 8'h88, 8'h21, 8'hB0,
      8'h00, 8'h02, 8'h06, 8'h88, 8'h36, 8'hB0,
      8'h00, 8'h01, 8'h06, 8'h88, 8'h39, 8'hB0,
      8'h00, 8'h00, 8'h06, 8'h88, 8'h58, 8'hB0,
      8'hBE, 8'hEF, 8'h00, 8'h00, 8'h63,
      8'h00, 8'h0A, 8'(CARBON_X86_DERIVED_TIER_P7_TURBO_UNLIMITED), 8'h00, 8'h62,
      8'hD8, 8'h8E, 8'hF0, 8'h00, 8'hB8
  };

  carbon_bootrom #(
      .BASE_ADDR(CARBON_SYSX86_ROM_BASE),
      .ROM_BYTES(ROM_BYTES),
      .INIT_IMAGE(ROM_IMAGE),
      .RESP_LATENCY(1)
  ) u_rom (
      .clk(clk),
      .rst_n(rst_n),
      .bus(s_if[1])
  );

  carbon_sram #(
      .BASE_ADDR(32'h0000_0000),
      .MEM_BYTES(CARBON_SYSX86_RAM_BYTES),
      .RESP_LATENCY(1)
  ) u_ram (
      .clk(clk),
      .rst_n(rst_n),
      .bus(s_if[2])
  );

  carbon_mmio_regs #(
      .BASE_ADDR(CARBON_SYSX86_MMIO_BASE),
      .SIGNATURE_RESET(32'h0000_0000),
      .RESP_LATENCY(0)
  ) u_mmio (
      .clk(clk),
      .rst_n(rst_n),
      .bus(s_if[0]),
      .signature(signature),
      .poweroff(poweroff),
      .uart_tx_valid(),
      .uart_tx_byte()
  );

  wire _unused = ^{cpu_csr_fault, cpu_csr_rdata[0], fpu_csr_fault, fpu_csr_rdata[0]};

endmodule : carbonx96_top
