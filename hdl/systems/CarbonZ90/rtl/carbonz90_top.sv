// Project Carbon - Systems
// carbonz90_top: CarbonZ90 system (Z90 + Am9513 in 9513 mode).

module carbonz90_top (
    input logic clk,
    input logic rst_n,
    output logic [31:0] signature,
    output logic        poweroff
);
  import carbon_arch_pkg::*;
  import carbon_memmap_pkg::*;
  import am9513_pkg::*;

  localparam int unsigned ADDR_W = 32;
  localparam int unsigned DATA_W = 32;
  localparam int unsigned ID_W   = 4;

  localparam int unsigned M = 3; // z90 mem, z90 io, am9513 dma
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
      ADDR_W'(CARBON_SYS16_MMIO_BASE),
      ADDR_W'(CARBON_SYS16_ROM_BASE),
      32'hFFFF_FFFF
  };
  localparam logic [ADDR_W-1:0] SLAVE_MASK [N] = '{
      ADDR_W'(CARBON_SYS16_MMIO_MASK),
      ADDR_W'(CARBON_SYS16_ROM_MASK),
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
  // Z90 core + CAI link
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

  cai_if cai_cpu (
      .clk(clk),
      .rst_n(rst_n)
  );
  cai_if cai_dev (
      .clk(clk),
      .rst_n(rst_n)
  );

  // For v1 firmware simplicity: override host config, but pass doorbell from the CPU.
  carbon_cai_router #(
      .OVERRIDE_HOST_CFG(1'b1),
      .OVERRIDE_SUBMIT_DESC_BASE(64'h0000_0000_0000_0400),
      .OVERRIDE_SUBMIT_RING_MASK(32'h0000_0000),
      .OVERRIDE_CONTEXT_SEL(16'h0000)
  ) u_cai (
      .cpu(cai_cpu),
      .dev(cai_dev)
  );

  z90_core u_cpu (
      .clk(clk),
      .rst_n(rst_n),
      .mem_if(m_if[0]),
      .io_if(m_if[1]),
      .irq(irq_cpu),
      .csr(csr_cpu),
      .dbg(dbg_cpu),
      .cai(cai_cpu)
  );

  // Hold the core halted until system CSR init is complete (ensures turbo gating is configured
  // before the boot ROM reaches the CAI_SUBMIT instruction).
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

  // Clear STRICT so Z90 turbo ops (including CAI_SUBMIT) are allowed post-MODEUP.
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
  // Am9513 accelerator (enabled; default mode P7/9513)
  // --------------------------------------------------------------------------
  csr_if csr_fpu (
      .clk(clk),
      .rst_n(rst_n)
  );

  am9513_accel u_am9513 (
      .clk(clk),
      .rst_n(rst_n),
      .csr(csr_fpu),
      .mem_if(m_if[2]),
      .cai(cai_dev)
  );

  typedef enum logic [2:0] {
    FPU_INIT_CTRL,
    FPU_INIT_MODE,
    FPU_INIT_COMP_LO,
    FPU_INIT_COMP_HI,
    FPU_INIT_COMP_MASK,
    FPU_INIT_IRQ,
    FPU_INIT_DONE
  } fpu_init_e;

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
      FPU_INIT_CTRL: begin
        fpu_csr_addr  = 32'(CARBON_CSR_AM9513_CTRL);
        fpu_csr_wdata = 32'h0000_0001; // enable
      end
      FPU_INIT_MODE: begin
        fpu_csr_addr  = 32'(CARBON_CSR_AM9513_MODE);
        fpu_csr_wdata = {24'h000000, 8'(AM9513_P7_TURBO)};
      end
      FPU_INIT_COMP_LO: begin
        fpu_csr_addr  = 32'(CARBON_CSR_AM9513_CAI_COMP_BASE_LO);
        fpu_csr_wdata = 32'h0000_0500;
      end
      FPU_INIT_COMP_HI: begin
        fpu_csr_addr  = 32'(CARBON_CSR_AM9513_CAI_COMP_BASE_HI);
        fpu_csr_wdata = 32'h0000_0000;
      end
      FPU_INIT_COMP_MASK: begin
        fpu_csr_addr  = 32'(CARBON_CSR_AM9513_CAI_COMP_RING_MASK);
        fpu_csr_wdata = 32'h0000_0000;
      end
      FPU_INIT_IRQ: begin
        fpu_csr_addr  = 32'(CARBON_CSR_AM9513_CAI_IRQ_ENABLE);
        fpu_csr_wdata = 32'h0000_0000;
      end
      default: begin
      end
    endcase
  end

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      fpu_init_q <= FPU_INIT_CTRL;
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
          if (fpu_init_q == FPU_INIT_IRQ) fpu_init_q <= FPU_INIT_DONE;
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
  localparam int unsigned ROM_BYTES = CARBON_SYS16_ROM_BYTES;
  localparam int unsigned ROM_USED  = 46;

  // Z90 boot stub:
  // - MODEUP to P7 @0x0010
  // - CAI_SUBMIT (doorbell) at 0x0010 (host config overridden by router)
  // - write "Z90!" signature to MMIO and power off
  localparam logic [ROM_BYTES*8-1:0] ROM_IMAGE = {
      {(ROM_BYTES-ROM_USED){8'h00}},
      8'h76, 8'hF0, 8'h04, 8'h32, 8'h01, 8'h3E,
      8'hF0, 8'h03, 8'h32, 8'h21, 8'h3E,
      8'hF0, 8'h02, 8'h32, 8'h30, 8'h3E,
      8'hF0, 8'h01, 8'h32, 8'h39, 8'h3E,
      8'hF0, 8'h00, 8'h32, 8'h5A, 8'h3E,
      8'h90, 8'hF0, 8'hF0, 8'hED,
      8'h00, 8'h00, 8'h00, 8'h00, 8'h00, 8'h00, 8'h00, 8'h00, 8'h00,
      8'h00, 8'h10, 8'(CARBON_Z80_DERIVED_TIER_P7_TURBO_UNLIMITED), 8'h00, 8'hF0, 8'hF0, 8'hED
  };

  carbon_bootrom #(
      .BASE_ADDR(CARBON_SYS16_ROM_BASE),
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
      .MEM_BYTES(CARBON_SYS16_RAM_BYTES),
      .RESP_LATENCY(1)
  ) u_ram (
      .clk(clk),
      .rst_n(rst_n),
      .bus(s_if[2])
  );

  carbon_mmio_regs #(
      .BASE_ADDR(CARBON_SYS16_MMIO_BASE),
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

endmodule : carbonz90_top
