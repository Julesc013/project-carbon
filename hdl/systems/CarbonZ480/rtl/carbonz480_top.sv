// Project Carbon - Systems
// carbonz480_top: CarbonZ480 bring-up system (Z480 scaffold + Am9513).

module carbonz480_top (
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

  localparam int unsigned M = 4; // z480 mem (idle), bootmaster, am9513 dma, carbondma
  localparam int unsigned N = 5; // mmio, carbonio, carbondma, rom, ram(default)

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
      ADDR_W'(CARBON_SYSX86_CARBONIO_BASE),
      ADDR_W'(CARBON_SYSX86_CARBONDMA_BASE),
      ADDR_W'(CARBON_SYSX86_ROM_BASE),
      32'hFFFF_FFFF
  };
  localparam logic [ADDR_W-1:0] SLAVE_MASK [N] = '{
      ADDR_W'(CARBON_SYSX86_MMIO_MASK),
      ADDR_W'(CARBON_SYSX86_CARBONIO_MASK),
      ADDR_W'(CARBON_SYSX86_CARBONDMA_MASK),
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
      .DEFAULT_SLAVE(4),
      .SLAVE_BASE(SLAVE_BASE),
      .SLAVE_MASK(SLAVE_MASK)
  ) u_fabric (
      .clk(clk),
      .rst_n(rst_n),
      .masters(m_if),
      .slaves(s_if)
  );

  // --------------------------------------------------------------------------
  // Z480 scaffold core (fabric is intentionally idle in v1)
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

  z480_core u_cpu (
      .clk(clk),
      .rst_n(rst_n),
      .mem_if(m_if[0]),
      .irq(irq_cpu),
      .csr(csr_cpu),
      .dbg(dbg_cpu)
  );

  // --------------------------------------------------------------------------
  // Am9513 accelerator (enabled; default mode P7 native); CAI host is tied off.
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
        fpu_csr_wdata = {24'h000000, 8'(AM9513_P7_NATIVE)};
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
  // CarbonIO (UART/PIO/Timers)
  // --------------------------------------------------------------------------
  csr_if csr_carbonio (
      .clk(clk),
      .rst_n(rst_n)
  );
  dbg_if dbg_carbonio (
      .clk(clk),
      .rst_n(rst_n)
  );
  irq_if #(.N(carbonio_pkg::CARBONIO_IRQ_SRC_COUNT)) irq_carbonio (
      .clk(clk),
      .rst_n(rst_n)
  );

  csr_master_tieoff u_csr_carbonio_tie (.csr(csr_carbonio));
  dbg_hub_tieoff    u_dbg_carbonio_tie (.dbg(dbg_carbonio));

  assign irq_carbonio.irq_ack = 1'b0;
  assign irq_carbonio.irq_ack_vector = '0;

  logic carbonio_uart_rx_ready;
  logic carbonio_uart_tx_valid;
  logic [7:0] carbonio_uart_tx_data;
  logic [31:0] carbonio_pio_out;
  logic [31:0] carbonio_pio_dir;

  carbonio #(
      .COMPAT_BASE_ADDR(CARBON_SYSX86_CARBONIO_BASE)
  ) u_carbonio (
      .clk(clk),
      .rst_n(rst_n),
      .compat_if(s_if[1]),
      .csr(csr_carbonio),
      .dbg(dbg_carbonio),
      .irq(irq_carbonio),
      .uart_rx_valid(1'b0),
      .uart_rx_data(8'h00),
      .uart_rx_ready(carbonio_uart_rx_ready),
      .uart_tx_ready(1'b1),
      .uart_tx_valid(carbonio_uart_tx_valid),
      .uart_tx_data(carbonio_uart_tx_data),
      .pio_in('0),
      .pio_out(carbonio_pio_out),
      .pio_dir(carbonio_pio_dir)
  );

  // --------------------------------------------------------------------------
  // CarbonDMA
  // --------------------------------------------------------------------------
  csr_if csr_carbondma (
      .clk(clk),
      .rst_n(rst_n)
  );
  dbg_if dbg_carbondma (
      .clk(clk),
      .rst_n(rst_n)
  );

  csr_master_tieoff u_csr_carbondma_tie (.csr(csr_carbondma));
  dbg_hub_tieoff    u_dbg_carbondma_tie (.dbg(dbg_carbondma));

  carbondma #(
      .COMPAT_BASE_ADDR(CARBON_SYSX86_CARBONDMA_BASE)
  ) u_carbondma (
      .clk(clk),
      .rst_n(rst_n),
      .compat_if(s_if[2]),
      .mem_if(m_if[3]),
      .csr(csr_carbondma),
      .dbg(dbg_carbondma)
  );

  // --------------------------------------------------------------------------
  // Boot stub master (writes signature + poweroff through MMIO)
  // --------------------------------------------------------------------------
  carbon_fabric_bootmaster #(
      .MMIO_BASE(CARBON_SYSX86_MMIO_BASE),
      .SIGNATURE(32'h3038_345A), // "Z480" (little endian bytes)
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
      .bus(s_if[3])
  );

  carbon_sram #(
      .BASE_ADDR(32'h0000_0000),
      .MEM_BYTES(CARBON_SYSX86_RAM_BYTES),
      .RESP_LATENCY(1)
  ) u_ram (
      .clk(clk),
      .rst_n(rst_n),
      .bus(s_if[4])
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

  wire _unused = ^{fpu_csr_fault, fpu_csr_rdata[0], carbonio_uart_rx_ready,
                   carbonio_uart_tx_valid, carbonio_uart_tx_data, carbonio_pio_out,
                   carbonio_pio_dir, irq_carbonio.irq_valid, irq_carbonio.irq_vector,
                   irq_carbonio.irq_prio, irq_carbonio.irq_pending};

endmodule : carbonz480_top
