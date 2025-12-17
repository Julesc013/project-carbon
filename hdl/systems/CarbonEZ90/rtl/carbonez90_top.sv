// Project Carbon - Systems
// carbonez90_top: CarbonEZ90 bring-up system (eZ90 scaffold + Am9513).

module carbonez90_top (
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

  localparam int unsigned M = 3; // ez90 mem (idle), bootmaster, am9513 dma
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

  // Reuse the x86-class 1MiB map for v1 bring-up.
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
  // eZ90 scaffold core (fabric is intentionally idle in v1)
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

  csr_master_tieoff u_csr_cpu_tie (.csr(csr_cpu));
  dbg_hub_tieoff    u_dbg_cpu_tie (.dbg(dbg_cpu));
  irq_src_tieoff    u_irq_cpu_tie (.irq(irq_cpu));

  ez90_core u_cpu (
      .clk(clk),
      .rst_n(rst_n),
      .mem_if(m_if[0]),
      .irq(irq_cpu),
      .csr(csr_cpu),
      .dbg(dbg_cpu)
  );

  // --------------------------------------------------------------------------
  // Am9513 accelerator (enabled; default mode P7/9513); CAI host is tied off.
  // --------------------------------------------------------------------------
  cai_if cai_host (
      .clk(clk),
      .rst_n(rst_n)
  );
  cai_if cai_dev (
      .clk(clk),
      .rst_n(rst_n)
  );

  cai_host_tieoff u_cai_host_tie (.cai(cai_host));

  carbon_cai_router u_cai (
      .cpu(cai_host),
      .dev(cai_dev)
  );

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

  // Minimal CSR init for Am9513 (enable + P7 default mode; completion base in RAM).
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
        fpu_csr_wdata = 32'h0000_0001;
      end
      FPU_INIT_MODE: begin
        fpu_csr_addr  = 32'(CARBON_CSR_AM9513_MODE);
        fpu_csr_wdata = {24'h000000, 8'(AM9513_P7_TURBO)};
      end
      FPU_INIT_COMP_LO: begin
        fpu_csr_addr  = 32'(CARBON_CSR_AM9513_CAI_COMP_BASE_LO);
        fpu_csr_wdata = 32'h0001_0000;
      end
      FPU_INIT_COMP_HI: begin
        fpu_csr_addr  = 32'(CARBON_CSR_AM9513_CAI_COMP_BASE_HI);
        fpu_csr_wdata = 32'h0000_0000;
      end
      FPU_INIT_COMP_MASK: begin
        fpu_csr_addr  = 32'(CARBON_CSR_AM9513_CAI_COMP_RING_MASK);
        fpu_csr_wdata = 32'h0000_00FF;
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

  // --------------------------------------------------------------------------
  // Boot stub master (writes signature + poweroff through MMIO)
  // --------------------------------------------------------------------------
  carbon_fabric_bootmaster #(
      .MMIO_BASE(CARBON_SYSX86_MMIO_BASE),
      .SIGNATURE(32'h3039_5A45), // "EZ90" (little endian bytes)
      .START_DELAY(8)
  ) u_boot (
      .clk(clk),
      .rst_n(rst_n),
      .fab(m_if[1]),
      .done()
  );

  // --------------------------------------------------------------------------
  // ROM/RAM/MMIO
  // --------------------------------------------------------------------------
  localparam int unsigned ROM_BYTES = CARBON_SYSX86_ROM_BYTES;
  localparam int unsigned ROM_USED  = 1;
  localparam logic [ROM_BYTES*8-1:0] ROM_IMAGE = {
      {(ROM_BYTES-ROM_USED){8'h00}},
      8'h00
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

  wire _unused = ^{fpu_csr_fault, fpu_csr_rdata[0]};

endmodule : carbonez90_top

