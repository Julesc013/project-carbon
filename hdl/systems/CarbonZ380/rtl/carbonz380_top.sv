// Project Carbon - Systems
// carbonz380_top: CarbonZ380 system (Z380 + platform glue).

module carbonz380_top (
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

  localparam int unsigned M = 3; // z380 mem, z380 io, carbondma
  localparam int unsigned N = 5; // mmio, carbonio, carbondma, rom, ram(default)

  localparam logic [7:0] Z380_MODE_NATIVE_MASK = 8'h04;

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
      ADDR_W'(CARBON_SYS16_ROM_BASE),
      ADDR_W'(CARBON_SYS16_CARBONDMA_BASE),
      ADDR_W'(CARBON_SYS16_CARBONIO_BASE),
      ADDR_W'(CARBON_SYS16_MMIO_BASE)
  };
  localparam logic [N*ADDR_W-1:0] SLAVE_MASK = {
      32'hFFFF_FFFF,
      ADDR_W'(CARBON_SYS16_ROM_MASK),
      ADDR_W'(CARBON_SYS16_CARBONDMA_MASK),
      ADDR_W'(CARBON_SYS16_CARBONIO_MASK),
      ADDR_W'(CARBON_SYS16_MMIO_MASK)
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
  // Z380 core
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

  z380_core u_cpu (
      .clk(clk),
      .rst_n(rst_n),
      .mem_if(m_if[0]),
      .io_if(m_if[1]),
      .irq(irq_cpu),
      .csr(csr_cpu),
      .dbg(dbg_cpu)
  );

  // Hold core halted until modeflags are configured.
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
      .wdata({24'h0, Z380_MODE_NATIVE_MASK}),
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

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      dbg_halt_req_q  <= 1'b1;
      dbg_run_pulse_q <= 1'b0;
      dbg_released_q  <= 1'b0;
    end else begin
      dbg_run_pulse_q <= 1'b0;
      if (cpu_csr_init_done_q && !dbg_released_q) begin
        dbg_halt_req_q  <= 1'b0;
        dbg_run_pulse_q <= 1'b1;
        dbg_released_q  <= 1'b1;
      end
    end
  end

  // --------------------------------------------------------------------------
  // Z380 platform glue (chip-selects, waitgen, refresh)
  // --------------------------------------------------------------------------
  csr_if csr_z380_cs (
      .clk(clk),
      .rst_n(rst_n)
  );
  csr_if csr_z380_wait (
      .clk(clk),
      .rst_n(rst_n)
  );
  csr_if csr_z380_refresh (
      .clk(clk),
      .rst_n(rst_n)
  );

  csr_master_tieoff u_cs_tie (.csr(csr_z380_cs));
  csr_master_tieoff u_wait_tie (.csr(csr_z380_wait));
  csr_master_tieoff u_refresh_tie (.csr(csr_z380_refresh));

  logic [3:0] cs_wait_profile;
  logic cs_any;
  logic [3:0] cs_match;
  logic [1:0] cs_index;
  logic wait_req_ready;
  logic wait_active;
  logic wait_done;
  logic refresh_tick;
  logic refresh_active;

  z380_chipselect #(
      .ADDR_W(ADDR_W),
      .RANGE_COUNT(4)
  ) u_chipselect (
      .clk(clk),
      .rst_n(rst_n),
      .addr_valid(m_if[0].req_valid),
      .addr(m_if[0].req_addr),
      .cs_match(cs_match),
      .cs_any(cs_any),
      .cs_wait_profile(cs_wait_profile),
      .cs_index(cs_index),
      .csr(csr_z380_cs)
  );

  z380_waitgen u_waitgen (
      .clk(clk),
      .rst_n(rst_n),
      .req_valid(cs_any && m_if[0].req_valid && wait_req_ready),
      .req_profile(cs_wait_profile[2:0]),
      .req_ready(wait_req_ready),
      .wait_active(wait_active),
      .wait_done(wait_done),
      .csr(csr_z380_wait)
  );

  z380_dram_refresh u_refresh (
      .clk(clk),
      .rst_n(rst_n),
      .refresh_tick(refresh_tick),
      .refresh_active(refresh_active),
      .csr(csr_z380_refresh)
  );

  // --------------------------------------------------------------------------
  // CarbonIO
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
      .COMPAT_BASE_ADDR(CARBON_SYS16_CARBONIO_BASE)
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
      .COMPAT_BASE_ADDR(CARBON_SYS16_CARBONDMA_BASE)
  ) u_carbondma (
      .clk(clk),
      .rst_n(rst_n),
      .compat_if(s_if[2]),
      .mem_if(m_if[2]),
      .csr(csr_carbondma),
      .dbg(dbg_carbondma)
  );

  // --------------------------------------------------------------------------
  // ROM/RAM/MMIO
  // --------------------------------------------------------------------------
  localparam int unsigned ROM_BYTES = CARBON_SYS16_ROM_BYTES;
  localparam int unsigned ROM_USED  = 51;

  // Z380 boot stub:
  // - MODEUP to P6
  // - execute P6 mul
  // - write "Z380" signature, power off, then trap on illegal opcode
  localparam logic [ROM_BYTES*8-1:0] ROM_IMAGE = {
      {(ROM_BYTES-ROM_USED){8'h00}},
      8'hFE, 8'hED, 8'hF0, 8'h04, 8'h32, 8'h01, 8'h3E,
      8'hF0, 8'h03, 8'h32, 8'h30, 8'h3E, 8'hF0, 8'h02,
      8'h32, 8'h38, 8'h3E, 8'hF0, 8'h01, 8'h32, 8'h33,
      8'h3E, 8'hF0, 8'h00, 8'h32, 8'h5A, 8'h3E, 8'hFC,
      8'hED, 8'h00, 8'h04, 8'h11, 8'h00, 8'h03, 8'h21,
      8'h00, 8'h00, 8'h00, 8'h00, 8'h00, 8'h00, 8'h00,
      8'h00, 8'h76, 8'h00, 8'h10, 8'h06, 8'h00, 8'hF0,
      8'hF0, 8'hED
  };

  carbon_bootrom #(
      .BASE_ADDR(CARBON_SYS16_ROM_BASE),
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
      .MEM_BYTES(CARBON_SYS16_RAM_BYTES),
      .RESP_LATENCY(1)
  ) u_ram (
      .clk(clk),
      .rst_n(rst_n),
      .bus(s_if[4])
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

  wire _unused = ^{cpu_csr_fault, cpu_csr_rdata[0], wait_active, wait_done,
                   refresh_tick, refresh_active, cs_match, cs_index,
                   carbonio_uart_rx_ready, carbonio_uart_tx_valid, carbonio_uart_tx_data,
                   carbonio_pio_out, carbonio_pio_dir, irq_carbonio.irq_valid,
                   irq_carbonio.irq_vector, irq_carbonio.irq_prio, irq_carbonio.irq_pending};

endmodule : carbonz380_top
