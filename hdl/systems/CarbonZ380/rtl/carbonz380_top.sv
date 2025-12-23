// Project Carbon - Systems
// carbonz380_top: CarbonZ380 system (Z380 + platform glue).

module carbonz380_top #(
    parameter bit ROM_TIER_TEST = 1'b0
) (
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

  localparam int unsigned M = 4; // z380 mem, z380 io, am9513 dma, carbondma
  localparam int unsigned N = 6; // mmio, carbonio, carbondma, bdt, rom, ram(default)

  localparam int unsigned S_MMIO      = 0;
  localparam int unsigned S_CARBONIO  = 1;
  localparam int unsigned S_CARBONDMA = 2;
  localparam int unsigned S_BDT       = 3;
  localparam int unsigned S_ROM       = 4;
  localparam int unsigned S_RAM       = 5;

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
      ADDR_W'(CARBON_SYS16_BDT_BASE),
      ADDR_W'(CARBON_SYS16_CARBONDMA_BASE),
      ADDR_W'(CARBON_SYS16_CARBONIO_BASE),
      ADDR_W'(CARBON_SYS16_MMIO_BASE)
  };
  localparam logic [N*ADDR_W-1:0] SLAVE_MASK = {
      32'hFFFF_FFFF,
      ADDR_W'(CARBON_SYS16_ROM_MASK),
      ADDR_W'(CARBON_SYS16_BDT_MASK),
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
      .DEFAULT_SLAVE(S_RAM),
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

  // --------------------------------------------------------------------------
  // Am9513 accelerator (enabled; default mode P2/9513)
  // --------------------------------------------------------------------------
  csr_if csr_fpu (
      .clk(clk),
      .rst_n(rst_n)
  );

  cai_if cai_cpu (
      .clk(clk),
      .rst_n(rst_n)
  );
  cai_if cai_dev (
      .clk(clk),
      .rst_n(rst_n)
  );

  carbon_cai_router #(
      .OVERRIDE_HOST_CFG(1'b1),
      .OVERRIDE_SUBMIT_DESC_BASE(64'h0000_0000_0000_0400),
      .OVERRIDE_SUBMIT_RING_MASK(32'h0000_0000),
      .OVERRIDE_CONTEXT_SEL(16'h0000)
  ) u_cai (
      .cpu(cai_cpu),
      .dev(cai_dev)
  );

  always_comb begin
    cai_cpu.submit_desc_base = 64'h0;
    cai_cpu.submit_ring_mask = 32'h0;
    cai_cpu.submit_doorbell = 1'b0;
    cai_cpu.context_sel = 16'h0;
  end

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
        fpu_csr_wdata = {24'h000000, 8'(AM9513_P2_AM9513)};
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
      .compat_if(s_if[S_CARBONIO]),
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
      .compat_if(s_if[S_CARBONDMA]),
      .mem_if(m_if[3]),
      .csr(csr_carbondma),
      .dbg(dbg_carbondma)
  );

  // --------------------------------------------------------------------------
  // ROM/RAM/MMIO
  // --------------------------------------------------------------------------
  `include "bdt_image.svh"

  localparam int unsigned ROM_BYTES = CARBON_SYS16_ROM_BYTES;
  localparam int unsigned ROM_USED  = 51;
  localparam int unsigned BDT_BYTES = BDT_IMAGE_BYTES;

  // Z380 boot stub:
  // - MODEUP to P6
  // - execute P6 mul
  // - write "Z380" signature, power off, then trap on illegal opcode
  localparam logic [ROM_BYTES*8-1:0] ROM_IMAGE_BOOT = {
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

  function automatic logic [ROM_BYTES*8-1:0] build_tier_rom;
    logic [ROM_BYTES*8-1:0] tmp;
    begin
      tmp = '0;
      // P0: MODEUP -> P1..P6 (return), then invalid P7
      tmp[(0*8)+:8] = CARBON_Z90_OPPAGE_P0_PREFIX0;
      tmp[(1*8)+:8] = CARBON_Z90_OPPAGE_P0_PREFIX1;
      tmp[(2*8)+:8] = {4'(CARBON_Z90_P0_MAJOR_SYS), 4'h0};
      tmp[(3*8)+:8] = {4'(CARBON_Z90_P0_SUB_MODEUP), 4'h0};
      tmp[(4*8)+:8] = 8'(CARBON_Z80_DERIVED_TIER_P1_I8085);
      tmp[(5*8)+:8] = 8'h40;
      tmp[(6*8)+:8] = 8'h00;

      tmp[(7*8)+:8] = CARBON_Z90_OPPAGE_P0_PREFIX0;
      tmp[(8*8)+:8] = CARBON_Z90_OPPAGE_P0_PREFIX1;
      tmp[(9*8)+:8] = {4'(CARBON_Z90_P0_MAJOR_SYS), 4'h0};
      tmp[(10*8)+:8] = {4'(CARBON_Z90_P0_SUB_MODEUP), 4'h0};
      tmp[(11*8)+:8] = 8'(CARBON_Z80_DERIVED_TIER_P2_Z80);
      tmp[(12*8)+:8] = 8'h60;
      tmp[(13*8)+:8] = 8'h00;

      tmp[(14*8)+:8] = CARBON_Z90_OPPAGE_P0_PREFIX0;
      tmp[(15*8)+:8] = CARBON_Z90_OPPAGE_P0_PREFIX1;
      tmp[(16*8)+:8] = {4'(CARBON_Z90_P0_MAJOR_SYS), 4'h0};
      tmp[(17*8)+:8] = {4'(CARBON_Z90_P0_SUB_MODEUP), 4'h0};
      tmp[(18*8)+:8] = 8'(CARBON_Z80_DERIVED_TIER_P3_Z180);
      tmp[(19*8)+:8] = 8'h80;
      tmp[(20*8)+:8] = 8'h00;

      tmp[(21*8)+:8] = CARBON_Z90_OPPAGE_P0_PREFIX0;
      tmp[(22*8)+:8] = CARBON_Z90_OPPAGE_P0_PREFIX1;
      tmp[(23*8)+:8] = {4'(CARBON_Z90_P0_MAJOR_SYS), 4'h0};
      tmp[(24*8)+:8] = {4'(CARBON_Z90_P0_SUB_MODEUP), 4'h0};
      tmp[(25*8)+:8] = 8'(CARBON_Z80_DERIVED_TIER_P4_EZ80);
      tmp[(26*8)+:8] = 8'hA0;
      tmp[(27*8)+:8] = 8'h00;

      tmp[(28*8)+:8] = CARBON_Z90_OPPAGE_P0_PREFIX0;
      tmp[(29*8)+:8] = CARBON_Z90_OPPAGE_P0_PREFIX1;
      tmp[(30*8)+:8] = {4'(CARBON_Z90_P0_MAJOR_SYS), 4'h0};
      tmp[(31*8)+:8] = {4'(CARBON_Z90_P0_SUB_MODEUP), 4'h0};
      tmp[(32*8)+:8] = 8'(CARBON_Z80_DERIVED_TIER_P5_Z280);
      tmp[(33*8)+:8] = 8'hC0;
      tmp[(34*8)+:8] = 8'h00;

      tmp[(35*8)+:8] = CARBON_Z90_OPPAGE_P0_PREFIX0;
      tmp[(36*8)+:8] = CARBON_Z90_OPPAGE_P0_PREFIX1;
      tmp[(37*8)+:8] = {4'(CARBON_Z90_P0_MAJOR_SYS), 4'h0};
      tmp[(38*8)+:8] = {4'(CARBON_Z90_P0_SUB_MODEUP), 4'h0};
      tmp[(39*8)+:8] = 8'(CARBON_Z80_DERIVED_TIER_P6_Z380);
      tmp[(40*8)+:8] = 8'hE0;
      tmp[(41*8)+:8] = 8'h00;

      tmp[(42*8)+:8] = CARBON_Z90_OPPAGE_P0_PREFIX0;
      tmp[(43*8)+:8] = CARBON_Z90_OPPAGE_P0_PREFIX1;
      tmp[(44*8)+:8] = {4'(CARBON_Z90_P0_MAJOR_SYS), 4'h0};
      tmp[(45*8)+:8] = {4'(CARBON_Z90_P0_SUB_MODEUP), 4'h0};
      tmp[(46*8)+:8] = 8'(CARBON_Z80_DERIVED_TIER_P7_Z480);
      tmp[(47*8)+:8] = 8'hF0;
      tmp[(48*8)+:8] = 8'h00;
      tmp[(49*8)+:8] = 8'h76; // HALT

      // Tier entries: RETMD at each entry point.
      tmp[(16'h0040*8)+:8] = 8'h00;
      tmp[(16'h0041*8)+:8] = CARBON_Z90_OPPAGE_P0_PREFIX0;
      tmp[(16'h0042*8)+:8] = CARBON_Z90_OPPAGE_P0_PREFIX1;
      tmp[(16'h0043*8)+:8] = {4'(CARBON_Z90_P0_MAJOR_SYS), 4'h0};
      tmp[(16'h0044*8)+:8] = {4'(CARBON_Z90_P0_SUB_RETMD), 4'h0};

      tmp[(16'h0060*8)+:8] = 8'h00;
      tmp[(16'h0061*8)+:8] = CARBON_Z90_OPPAGE_P0_PREFIX0;
      tmp[(16'h0062*8)+:8] = CARBON_Z90_OPPAGE_P0_PREFIX1;
      tmp[(16'h0063*8)+:8] = {4'(CARBON_Z90_P0_MAJOR_SYS), 4'h0};
      tmp[(16'h0064*8)+:8] = {4'(CARBON_Z90_P0_SUB_RETMD), 4'h0};

      tmp[(16'h0080*8)+:8] = 8'h00;
      tmp[(16'h0081*8)+:8] = CARBON_Z90_OPPAGE_P0_PREFIX0;
      tmp[(16'h0082*8)+:8] = CARBON_Z90_OPPAGE_P0_PREFIX1;
      tmp[(16'h0083*8)+:8] = {4'(CARBON_Z90_P0_MAJOR_SYS), 4'h0};
      tmp[(16'h0084*8)+:8] = {4'(CARBON_Z90_P0_SUB_RETMD), 4'h0};

      tmp[(16'h00A0*8)+:8] = 8'h00;
      tmp[(16'h00A1*8)+:8] = CARBON_Z90_OPPAGE_P0_PREFIX0;
      tmp[(16'h00A2*8)+:8] = CARBON_Z90_OPPAGE_P0_PREFIX1;
      tmp[(16'h00A3*8)+:8] = {4'(CARBON_Z90_P0_MAJOR_SYS), 4'h0};
      tmp[(16'h00A4*8)+:8] = {4'(CARBON_Z90_P0_SUB_RETMD), 4'h0};

      tmp[(16'h00C0*8)+:8] = 8'h00;
      tmp[(16'h00C1*8)+:8] = CARBON_Z90_OPPAGE_P0_PREFIX0;
      tmp[(16'h00C2*8)+:8] = CARBON_Z90_OPPAGE_P0_PREFIX1;
      tmp[(16'h00C3*8)+:8] = {4'(CARBON_Z90_P0_MAJOR_SYS), 4'h0};
      tmp[(16'h00C4*8)+:8] = {4'(CARBON_Z90_P0_SUB_RETMD), 4'h0};

      tmp[(16'h00E0*8)+:8] = 8'h00;
      tmp[(16'h00E1*8)+:8] = CARBON_Z90_OPPAGE_P0_PREFIX0;
      tmp[(16'h00E2*8)+:8] = CARBON_Z90_OPPAGE_P0_PREFIX1;
      tmp[(16'h00E3*8)+:8] = {4'(CARBON_Z90_P0_MAJOR_SYS), 4'h0};
      tmp[(16'h00E4*8)+:8] = {4'(CARBON_Z90_P0_SUB_RETMD), 4'h0};

      tmp[(16'h00F0*8)+:8] = 8'h00;
      tmp[(16'h00F1*8)+:8] = CARBON_Z90_OPPAGE_P0_PREFIX0;
      tmp[(16'h00F2*8)+:8] = CARBON_Z90_OPPAGE_P0_PREFIX1;
      tmp[(16'h00F3*8)+:8] = {4'(CARBON_Z90_P0_MAJOR_SYS), 4'h0};
      tmp[(16'h00F4*8)+:8] = {4'(CARBON_Z90_P0_SUB_RETMD), 4'h0};

      build_tier_rom = tmp;
    end
  endfunction

  localparam logic [ROM_BYTES*8-1:0] ROM_IMAGE_TIER = build_tier_rom();
  localparam logic [ROM_BYTES*8-1:0] ROM_IMAGE =
      ROM_TIER_TEST ? ROM_IMAGE_TIER : ROM_IMAGE_BOOT;

  carbon_bootrom #(
      .BASE_ADDR(CARBON_SYS16_ROM_BASE),
      .ROM_BYTES(ROM_BYTES),
      .INIT_IMAGE(ROM_IMAGE),
      .RESP_LATENCY(1)
  ) u_rom (
      .clk(clk),
      .rst_n(rst_n),
      .bus(s_if[S_ROM])
  );

  carbon_bootrom #(
      .BASE_ADDR(CARBON_SYS16_BDT_BASE),
      .ROM_BYTES(BDT_BYTES),
      .INIT_IMAGE(BDT_IMAGE),
      .RESP_LATENCY(1)
  ) u_bdt (
      .clk(clk),
      .rst_n(rst_n),
      .bus(s_if[S_BDT])
  );

  carbon_sram #(
      .BASE_ADDR(32'h0000_0000),
      .MEM_BYTES(CARBON_SYS16_RAM_BYTES),
      .RESP_LATENCY(1)
  ) u_ram (
      .clk(clk),
      .rst_n(rst_n),
      .bus(s_if[S_RAM])
  );

  carbon_mmio_regs #(
      .BASE_ADDR(CARBON_SYS16_MMIO_BASE),
      .SIGNATURE_RESET(32'h0000_0000),
      .RESP_LATENCY(0)
  ) u_mmio (
      .clk(clk),
      .rst_n(rst_n),
      .bus(s_if[S_MMIO]),
      .signature(signature),
      .poweroff(poweroff),
      .uart_tx_valid(),
      .uart_tx_byte()
  );

  wire _unused = ^{cpu_csr_fault, cpu_csr_rdata[0], fpu_csr_fault, fpu_csr_rdata[0],
                   wait_active, wait_done, refresh_tick, refresh_active, cs_match, cs_index,
                   carbonio_uart_rx_ready, carbonio_uart_tx_valid, carbonio_uart_tx_data,
                   carbonio_pio_out, carbonio_pio_dir, irq_carbonio.irq_valid,
                   irq_carbonio.irq_vector, irq_carbonio.irq_prio, irq_carbonio.irq_pending};

endmodule : carbonz380_top
