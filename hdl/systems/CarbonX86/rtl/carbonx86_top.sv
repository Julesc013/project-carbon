// Project Carbon - Systems
// carbonx86_top: CarbonX86 system (8096 in P0 + 8097 in P0).

module carbonx86_top (
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

  localparam int unsigned M = 4; // 8096 mem, 8096 io, 8097 mem, carbondma
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

  localparam logic [N*ADDR_W-1:0] SLAVE_BASE = {
      32'hFFFF_FFFF,
      ADDR_W'(CARBON_SYSX86_ROM_BASE),
      ADDR_W'(CARBON_SYSX86_CARBONDMA_BASE),
      ADDR_W'(CARBON_SYSX86_CARBONIO_BASE),
      ADDR_W'(CARBON_SYSX86_MMIO_BASE)
  };
  localparam logic [N*ADDR_W-1:0] SLAVE_MASK = {
      32'hFFFF_FFFF,
      ADDR_W'(CARBON_SYSX86_ROM_MASK),
      ADDR_W'(CARBON_SYSX86_CARBONDMA_MASK),
      ADDR_W'(CARBON_SYSX86_CARBONIO_MASK),
      ADDR_W'(CARBON_SYSX86_MMIO_MASK)
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
  // 8096 CPU (P0 strict by reset; no turbo use in this system)
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

  cpu_8096 u_cpu (
      .clk(clk),
      .rst_n(rst_n),
      .mem_if(m_if[0]),
      .io_if(m_if[1]),
      .irq(irq_cpu),
      .csr(csr_cpu),
      .dbg(dbg_cpu)
  );

  // --------------------------------------------------------------------------
  // 8097 FPU (CSR-controlled; left idle in this system stub)
  // --------------------------------------------------------------------------
  csr_if csr_fpu (
      .clk(clk),
      .rst_n(rst_n)
  );
  csr_master_tieoff u_csr_fpu_tie (.csr(csr_fpu));

  fpu_8097 u_fpu (
      .clk(clk),
      .rst_n(rst_n),
      .csr(csr_fpu),
      .mem_if(m_if[2])
  );

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
  // ROM/RAM/MMIO
  // --------------------------------------------------------------------------
  localparam int unsigned ROM_BYTES = CARBON_SYSX86_ROM_BYTES;
  localparam int unsigned ROM_USED  = 38;

  // 8096 boot stub:
  // - set DS = 0xF000 (MMIO window at 0xF0000)
  // - write "X86!" signature to MMIO signature register (byte stores)
  // - write 1 to poweroff register
  // - loop forever
  localparam logic [ROM_BYTES*8-1:0] ROM_IMAGE = {
      {(ROM_BYTES-ROM_USED){8'h00}},
      8'hFF, 8'hFD, 8'hE9,
      8'h00, 8'h04, 8'h06, 8'h88, 8'h01, 8'hB0,
      8'h00, 8'h03, 8'h06, 8'h88, 8'h21, 8'hB0,
      8'h00, 8'h02, 8'h06, 8'h88, 8'h36, 8'hB0,
      8'h00, 8'h01, 8'h06, 8'h88, 8'h38, 8'hB0,
      8'h00, 8'h00, 8'h06, 8'h88, 8'h58, 8'hB0,
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

  wire _unused = ^{carbonio_uart_rx_ready, carbonio_uart_tx_valid, carbonio_uart_tx_data,
                   carbonio_pio_out, carbonio_pio_dir, irq_carbonio.irq_valid,
                   irq_carbonio.irq_vector, irq_carbonio.irq_prio, irq_carbonio.irq_pending};

endmodule : carbonx86_top
