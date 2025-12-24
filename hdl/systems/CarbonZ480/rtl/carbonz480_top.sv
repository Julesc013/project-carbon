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

  localparam int unsigned M = 9; // z85 mem/io, z90 mem/io, z380 mem/io, z480 mem, am9513 dma, carbondma
  localparam int unsigned N = 8; // mmio, carbonio, carbondma, tier host, discovery, bdt, rom, ram(default)

  localparam int unsigned M_Z85_MEM   = 0;
  localparam int unsigned M_Z85_IO    = 1;
  localparam int unsigned M_Z90_MEM   = 2;
  localparam int unsigned M_Z90_IO    = 3;
  localparam int unsigned M_Z380_MEM  = 4;
  localparam int unsigned M_Z380_IO   = 5;
  localparam int unsigned M_Z480_MEM  = 6;
  localparam int unsigned M_AM9513_DMA = 7;
  localparam int unsigned M_CARBONDMA = 8;

  localparam int unsigned S_MMIO      = 0;
  localparam int unsigned S_CARBONIO  = 1;
  localparam int unsigned S_CARBONDMA = 2;
  localparam int unsigned S_TIER_HOST = 3;
  localparam int unsigned S_DISCOVERY = 4;
  localparam int unsigned S_BDT       = 5;
  localparam int unsigned S_ROM       = 6;
  localparam int unsigned S_RAM       = 7;

  localparam logic [1:0] CORE_Z85  = 2'd0;
  localparam logic [1:0] CORE_Z90  = 2'd1;
  localparam logic [1:0] CORE_Z380 = 2'd2;
  localparam logic [1:0] CORE_Z480 = 2'd3;

  localparam logic [63:0] Z480_RESET_PC = 64'h0000_0040;
  localparam int unsigned DISCOVERY_ROM_BYTES = CARBON_SYS16_DISCOVERY_BYTES;
  localparam int unsigned DISCOVERY_TABLE_BYTES = CARBON_CARBON_DISCOVERY_TABLE_V1_SIZE_BYTES;

  localparam int unsigned DISCOVERY_OFF_TABLE = 0;
  localparam int unsigned DISCOVERY_OFF_LIMITS = 64;
  localparam int unsigned DISCOVERY_OFF_CPU_FEAT = 96;
  localparam int unsigned DISCOVERY_OFF_FPU_FEAT = 112;
  localparam int unsigned DISCOVERY_OFF_PERIPH_FEAT = 128;
  localparam int unsigned DISCOVERY_OFF_TOPOLOGY = 160;

  localparam logic [63:0] DISCOVERY_TABLE_PTR =
      64'(CARBON_SYS16_DISCOVERY_BASE + DISCOVERY_OFF_TABLE);
  localparam logic [63:0] LIMITS_TABLE_PTR =
      64'(CARBON_SYS16_DISCOVERY_BASE + DISCOVERY_OFF_LIMITS);
  localparam logic [63:0] CPU_FEAT_PTR =
      64'(CARBON_SYS16_DISCOVERY_BASE + DISCOVERY_OFF_CPU_FEAT);
  localparam logic [63:0] FPU_FEAT_PTR =
      64'(CARBON_SYS16_DISCOVERY_BASE + DISCOVERY_OFF_FPU_FEAT);
  localparam logic [63:0] PERIPH_FEAT_PTR =
      64'(CARBON_SYS16_DISCOVERY_BASE + DISCOVERY_OFF_PERIPH_FEAT);
  localparam logic [63:0] TOPOLOGY_TABLE_PTR =
      64'(CARBON_SYS16_DISCOVERY_BASE + DISCOVERY_OFF_TOPOLOGY);

  localparam int unsigned TOPOLOGY_ENTRY_COUNT = 1;
  localparam int unsigned TOPOLOGY_TABLE_BYTES =
      CARBON_TOPOLOGY_HEADER_V1_SIZE_BYTES +
      (CARBON_TOPOLOGY_ENTRY_V1_SIZE_BYTES * TOPOLOGY_ENTRY_COUNT);

  localparam int unsigned BDT_ENTRY_COUNT = 8;

  localparam logic [31:0] CPU_FEAT_WORD0 =
      CARBON_FEAT_MODE_SWITCH_MASK |
      CARBON_FEAT_CSR_NAMESPACE_MASK |
      CARBON_FEAT_FABRIC_MASK |
      CARBON_FEAT_CPUID_MASK |
      CARBON_Z480_NATIVE_64_MASK;
  localparam logic [31:0] FPU_FEAT_WORD0 =
      CARBON_AM9513_ASYNC_SCALAR_MASK;
  localparam logic [31:0] PERIPH_FEAT_WORD0 =
      CARBON_FEAT_CAI_MASK |
      CARBON_FEAT_BDT_MASK |
      CARBON_FEAT_DEVICE_MODEL_MASK |
      CARBON_NON_COHERENT_DMA_BASELINE_MASK;

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

  // CarbonZ480 keeps 16-bit decode compatibility by masking to the low 16 bits.
  localparam logic [31:0] SYS16_MASK_L16 = 32'h0000_FF00;
  localparam logic [31:0] SYS16_MASK_L16_BDT = 32'h0000_FE00;

  localparam logic [N*ADDR_W-1:0] SLAVE_BASE = {
      32'hFFFF_FFFF,
      ADDR_W'(CARBON_SYS16_ROM_BASE),
      ADDR_W'(CARBON_SYS16_BDT_BASE),
      ADDR_W'(CARBON_SYS16_DISCOVERY_BASE),
      ADDR_W'(CARBON_SYS16_TIER_HOST_BASE),
      ADDR_W'(CARBON_SYS16_CARBONDMA_BASE),
      ADDR_W'(CARBON_SYS16_CARBONIO_BASE),
      ADDR_W'(CARBON_SYS16_MMIO_BASE)
  };
  localparam logic [N*ADDR_W-1:0] SLAVE_MASK = {
      32'hFFFF_FFFF,
      ADDR_W'(SYS16_MASK_L16),
      ADDR_W'(SYS16_MASK_L16_BDT),
      ADDR_W'(SYS16_MASK_L16),
      ADDR_W'(SYS16_MASK_L16),
      ADDR_W'(SYS16_MASK_L16),
      ADDR_W'(SYS16_MASK_L16),
      ADDR_W'(SYS16_MASK_L16)
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
  // Tier host controller (Option A personality switch)
  // --------------------------------------------------------------------------
  logic [7:0] host_active_tier;
  logic [1:0] host_active_core;
  logic [3:0] host_halt_req;
  logic [3:0] host_run_pulse;

  tier_host_ctrl #(
      .BASE_ADDR(CARBON_SYS16_TIER_HOST_BASE)
  ) u_tier_host (
      .clk(clk),
      .rst_n(rst_n),
      .bus(s_if[S_TIER_HOST]),
      .active_tier(host_active_tier),
      .active_core(host_active_core),
      .core_halt_req(host_halt_req),
      .core_run_pulse(host_run_pulse)
  );

  // --------------------------------------------------------------------------
  // Hosted core cluster (Z85/Z90/Z380/Z480)
  // --------------------------------------------------------------------------
  csr_if csr_z85 (
      .clk(clk),
      .rst_n(rst_n)
  );
  dbg_if dbg_z85 (
      .clk(clk),
      .rst_n(rst_n)
  );
  irq_if #(.N(32)) irq_z85 (
      .clk(clk),
      .rst_n(rst_n)
  );

  csr_if csr_z90 (
      .clk(clk),
      .rst_n(rst_n)
  );
  dbg_if dbg_z90 (
      .clk(clk),
      .rst_n(rst_n)
  );
  irq_if #(.N(32)) irq_z90 (
      .clk(clk),
      .rst_n(rst_n)
  );

  csr_if csr_z380 (
      .clk(clk),
      .rst_n(rst_n)
  );
  dbg_if dbg_z380 (
      .clk(clk),
      .rst_n(rst_n)
  );
  irq_if #(.N(32)) irq_z380 (
      .clk(clk),
      .rst_n(rst_n)
  );

  csr_if csr_z480 (
      .clk(clk),
      .rst_n(rst_n)
  );
  dbg_if dbg_z480 (
      .clk(clk),
      .rst_n(rst_n)
  );
  irq_if #(.N(32)) irq_z480 (
      .clk(clk),
      .rst_n(rst_n)
  );

  csr_master_tieoff u_csr_z85_tie (.csr(csr_z85));
  csr_master_tieoff u_csr_z90_tie (.csr(csr_z90));
  csr_master_tieoff u_csr_z380_tie (.csr(csr_z380));
  csr_master_tieoff u_csr_z480_tie (.csr(csr_z480));

  irq_src_tieoff u_irq_z85_tie (.irq(irq_z85));
  irq_src_tieoff u_irq_z90_tie (.irq(irq_z90));
  irq_src_tieoff u_irq_z380_tie (.irq(irq_z380));
  irq_src_tieoff u_irq_z480_tie (.irq(irq_z480));

  assign dbg_z85.halt_req = host_halt_req[CORE_Z85];
  assign dbg_z85.run_req  = host_run_pulse[CORE_Z85];
  assign dbg_z85.step_req = 1'b0;
  assign dbg_z85.bp_valid  = 1'b0;
  assign dbg_z85.bp_write  = 1'b0;
  assign dbg_z85.bp_index  = '0;
  assign dbg_z85.bp_addr   = '0;
  assign dbg_z85.bp_kind   = '0;
  assign dbg_z85.bp_enable = 1'b0;
  assign dbg_z85.trace_ready = 1'b1;

  assign dbg_z90.halt_req = host_halt_req[CORE_Z90];
  assign dbg_z90.run_req  = host_run_pulse[CORE_Z90];
  assign dbg_z90.step_req = 1'b0;
  assign dbg_z90.bp_valid  = 1'b0;
  assign dbg_z90.bp_write  = 1'b0;
  assign dbg_z90.bp_index  = '0;
  assign dbg_z90.bp_addr   = '0;
  assign dbg_z90.bp_kind   = '0;
  assign dbg_z90.bp_enable = 1'b0;
  assign dbg_z90.trace_ready = 1'b1;

  assign dbg_z380.halt_req = host_halt_req[CORE_Z380];
  assign dbg_z380.run_req  = host_run_pulse[CORE_Z380];
  assign dbg_z380.step_req = 1'b0;
  assign dbg_z380.bp_valid  = 1'b0;
  assign dbg_z380.bp_write  = 1'b0;
  assign dbg_z380.bp_index  = '0;
  assign dbg_z380.bp_addr   = '0;
  assign dbg_z380.bp_kind   = '0;
  assign dbg_z380.bp_enable = 1'b0;
  assign dbg_z380.trace_ready = 1'b1;

  assign dbg_z480.halt_req = host_halt_req[CORE_Z480];
  assign dbg_z480.run_req  = host_run_pulse[CORE_Z480];
  assign dbg_z480.step_req = 1'b0;
  assign dbg_z480.bp_valid  = 1'b0;
  assign dbg_z480.bp_write  = 1'b0;
  assign dbg_z480.bp_index  = '0;
  assign dbg_z480.bp_addr   = '0;
  assign dbg_z480.bp_kind   = '0;
  assign dbg_z480.bp_enable = 1'b0;
  assign dbg_z480.trace_ready = 1'b1;

  cai_if cai_z90 (
      .clk(clk),
      .rst_n(rst_n)
  );
  cai_if cai_dev (
      .clk(clk),
      .rst_n(rst_n)
  );

  carbon_cai_router u_cai (
      .cpu(cai_z90),
      .dev(cai_dev)
  );

  z85_core #(
      .DISCOVERY_PTR(DISCOVERY_TABLE_PTR)
  ) u_z85 (
      .clk(clk),
      .rst_n(rst_n),
      .mem_if(m_if[M_Z85_MEM]),
      .io_if(m_if[M_Z85_IO]),
      .irq(irq_z85),
      .csr(csr_z85),
      .dbg(dbg_z85)
  );

  z90_core #(
      .DISCOVERY_PTR(DISCOVERY_TABLE_PTR)
  ) u_z90 (
      .clk(clk),
      .rst_n(rst_n),
      .mem_if(m_if[M_Z90_MEM]),
      .io_if(m_if[M_Z90_IO]),
      .irq(irq_z90),
      .csr(csr_z90),
      .dbg(dbg_z90),
      .cai(cai_z90)
  );

  z380_core #(
      .DISCOVERY_PTR(DISCOVERY_TABLE_PTR)
  ) u_z380 (
      .clk(clk),
      .rst_n(rst_n),
      .mem_if(m_if[M_Z380_MEM]),
      .io_if(m_if[M_Z380_IO]),
      .irq(irq_z380),
      .csr(csr_z380),
      .dbg(dbg_z380)
  );

  z480_core #(
      .IO_BASE(CARBON_SYS16_MMIO_BASE),
      .IO_MASK(32'h0000_F000),
      .RESET_PC(Z480_RESET_PC),
      .DISCOVERY_PTR(DISCOVERY_TABLE_PTR),
      .BDT_PTR(64'(CARBON_SYS16_BDT_BASE)),
      .BDT_ENTRY_COUNT(BDT_ENTRY_COUNT),
      .TOPOLOGY_PTR(TOPOLOGY_TABLE_PTR),
      .CPU_FEAT_WORD0(CPU_FEAT_WORD0),
      .FPU_FEAT_WORD0(FPU_FEAT_WORD0),
      .PERIPH_FEAT_WORD0(PERIPH_FEAT_WORD0),
      .CORE_COUNT(1),
      .VECTOR_BITS(0)
  ) u_z480 (
      .clk(clk),
      .rst_n(rst_n),
      .mem_if(m_if[M_Z480_MEM]),
      .irq(irq_z480),
      .csr(csr_z480),
      .dbg(dbg_z480)
  );

  // --------------------------------------------------------------------------
  // Am9513 accelerator (enabled; default mode P2/9513)
  // --------------------------------------------------------------------------

  csr_if csr_fpu (
      .clk(clk),
      .rst_n(rst_n)
  );

  am9513_accel u_am9513 (
      .clk(clk),
      .rst_n(rst_n),
      .csr(csr_fpu),
      .mem_if(m_if[M_AM9513_DMA]),
      .cai(cai_dev)
  );

  // Minimal CSR init for Am9513 (enable + P2 default mode; completion base in RAM).
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
        fpu_csr_wdata = {24'h000000, 8'(AM9513_P2_AM9513)};
      end
      FPU_INIT_COMP_LO: begin
        fpu_csr_addr  = 32'(CARBON_CSR_AM9513_CAI_COMP_BASE_LO);
        fpu_csr_wdata = 32'h0000_4000;
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
      .mem_if(m_if[M_CARBONDMA]),
      .csr(csr_carbondma),
      .dbg(dbg_carbondma)
  );

  // --------------------------------------------------------------------------
  // ROM/RAM/MMIO
  // --------------------------------------------------------------------------
  `include "bdt_image.svh"

  localparam int unsigned ROM_BYTES = CARBON_SYS16_ROM_BYTES;
  localparam int unsigned BDT_BYTES = BDT_IMAGE_BYTES;
  localparam int unsigned DISCOVERY_BYTES = DISCOVERY_ROM_BYTES;

  function automatic logic [DISCOVERY_BYTES*8-1:0] build_discovery_rom;
    logic [DISCOVERY_BYTES*8-1:0] tmp;
    begin
      tmp = '0;
      tmp[(DISCOVERY_OFF_TABLE + CARBON_CARBON_DISCOVERY_TABLE_V1_OFF_SIGNATURE)*8 +: 32] = 32'h43534443; // "CDSC"
      tmp[(DISCOVERY_OFF_TABLE + CARBON_CARBON_DISCOVERY_TABLE_V1_OFF_TABLE_VERSION)*8 +: 16] =
          16'(CARBON_CARBON_DISCOVERY_TABLE_V1_VERSION);
      tmp[(DISCOVERY_OFF_TABLE + CARBON_CARBON_DISCOVERY_TABLE_V1_OFF_TABLE_SIZE)*8 +: 16] =
          16'(DISCOVERY_TABLE_BYTES);
      tmp[(DISCOVERY_OFF_TABLE + CARBON_CARBON_DISCOVERY_TABLE_V1_OFF_CPU_LADDER_ID)*8 +: 8] =
          8'(CARBON_TIER_LADDER_Z80);
      tmp[(DISCOVERY_OFF_TABLE + CARBON_CARBON_DISCOVERY_TABLE_V1_OFF_FPU_LADDER_ID)*8 +: 8] =
          8'(CARBON_TIER_LADDER_AM95);
      tmp[(DISCOVERY_OFF_TABLE + CARBON_CARBON_DISCOVERY_TABLE_V1_OFF_PRESENTED_CPU_TIER)*8 +: 8] =
          8'(CARBON_Z80_DERIVED_TIER_P7_Z480);
      tmp[(DISCOVERY_OFF_TABLE + CARBON_CARBON_DISCOVERY_TABLE_V1_OFF_PRESENTED_FPU_TIER)*8 +: 8] =
          8'(CARBON_AM95XX_FPU_TIER_P2_AM9513);
      tmp[(DISCOVERY_OFF_TABLE + CARBON_CARBON_DISCOVERY_TABLE_V1_OFF_PROFILE_ID)*8 +: 8] =
          8'(CARBON_PROFILE_SOC_RETRO);
      tmp[(DISCOVERY_OFF_TABLE + CARBON_CARBON_DISCOVERY_TABLE_V1_OFF_TOPOLOGY_TABLE_PTR)*8 +: 64] =
          TOPOLOGY_TABLE_PTR;
      tmp[(DISCOVERY_OFF_TABLE + CARBON_CARBON_DISCOVERY_TABLE_V1_OFF_BDT_PTR)*8 +: 64] =
          64'(CARBON_SYS16_BDT_BASE);
      tmp[(DISCOVERY_OFF_TABLE + CARBON_CARBON_DISCOVERY_TABLE_V1_OFF_LIMITS_TABLE_PTR)*8 +: 64] =
          LIMITS_TABLE_PTR;
      tmp[(DISCOVERY_OFF_TABLE + CARBON_CARBON_DISCOVERY_TABLE_V1_OFF_CPU_FEATURE_BITMAP_PTR)*8 +: 64] =
          CPU_FEAT_PTR;
      tmp[(DISCOVERY_OFF_TABLE + CARBON_CARBON_DISCOVERY_TABLE_V1_OFF_FPU_FEATURE_BITMAP_PTR)*8 +: 64] =
          FPU_FEAT_PTR;
      tmp[(DISCOVERY_OFF_TABLE + CARBON_CARBON_DISCOVERY_TABLE_V1_OFF_PERIPHERAL_FEATURE_BITMAP_PTR)*8 +: 64] =
          PERIPH_FEAT_PTR;

      tmp[(DISCOVERY_OFF_LIMITS + CARBON_CARBON_LIMITS_TABLE_V1_OFF_QUEUE_SUBMIT_DEPTH)*8 +: 32] = 32'd1;
      tmp[(DISCOVERY_OFF_LIMITS + CARBON_CARBON_LIMITS_TABLE_V1_OFF_QUEUE_COMPLETE_DEPTH)*8 +: 32] = 32'd256;
      tmp[(DISCOVERY_OFF_LIMITS + CARBON_CARBON_LIMITS_TABLE_V1_OFF_CONTEXTS)*8 +: 16] = 16'd64;
      tmp[(DISCOVERY_OFF_LIMITS + CARBON_CARBON_LIMITS_TABLE_V1_OFF_VECTOR_LANES)*8 +: 16] = 16'd0;
      tmp[(DISCOVERY_OFF_LIMITS + CARBON_CARBON_LIMITS_TABLE_V1_OFF_TENSOR_RANK)*8 +: 16] = 16'd0;
      tmp[(DISCOVERY_OFF_LIMITS + CARBON_CARBON_LIMITS_TABLE_V1_OFF_MAX_CORES)*8 +: 16] = 16'd1;
      tmp[(DISCOVERY_OFF_LIMITS + CARBON_CARBON_LIMITS_TABLE_V1_OFF_MAX_THREADS)*8 +: 16] = 16'd1;

      tmp[(DISCOVERY_OFF_CPU_FEAT)*8 +: 32] = CPU_FEAT_WORD0;
      tmp[(DISCOVERY_OFF_FPU_FEAT)*8 +: 32] = FPU_FEAT_WORD0;
      tmp[(DISCOVERY_OFF_PERIPH_FEAT)*8 +: 32] = PERIPH_FEAT_WORD0;

      tmp[(DISCOVERY_OFF_TOPOLOGY + CARBON_TOPOLOGY_HEADER_V1_OFF_SIGNATURE)*8 +: 32] = 32'h504F_5443; // "CTOP"
      tmp[(DISCOVERY_OFF_TOPOLOGY + CARBON_TOPOLOGY_HEADER_V1_OFF_HEADER_VERSION)*8 +: 16] =
          16'(CARBON_TOPOLOGY_HEADER_V1_VERSION);
      tmp[(DISCOVERY_OFF_TOPOLOGY + CARBON_TOPOLOGY_HEADER_V1_OFF_HEADER_SIZE)*8 +: 16] =
          16'(CARBON_TOPOLOGY_HEADER_V1_SIZE_BYTES);
      tmp[(DISCOVERY_OFF_TOPOLOGY + CARBON_TOPOLOGY_HEADER_V1_OFF_ENTRY_SIZE)*8 +: 16] =
          16'(CARBON_TOPOLOGY_ENTRY_V1_SIZE_BYTES);
      tmp[(DISCOVERY_OFF_TOPOLOGY + CARBON_TOPOLOGY_HEADER_V1_OFF_ENTRY_COUNT)*8 +: 16] =
          16'(TOPOLOGY_ENTRY_COUNT);
      tmp[(DISCOVERY_OFF_TOPOLOGY + CARBON_TOPOLOGY_HEADER_V1_OFF_TOTAL_SIZE)*8 +: 32] =
          32'(TOPOLOGY_TABLE_BYTES);

      build_discovery_rom = tmp;
    end
  endfunction

  function automatic logic [ROM_BYTES*8-1:0] build_rom_image;
    logic [ROM_BYTES*8-1:0] tmp;
    begin
      tmp = '0;
      // Z85 boot stub @ 0x0000: LD A,0x07; LD (0xF300),A; HALT
      tmp[(0*8)+:8] = 8'h3E;
      tmp[(1*8)+:8] = 8'h07;
      tmp[(2*8)+:8] = 8'h32;
      tmp[(3*8)+:8] = 8'h00;
      tmp[(4*8)+:8] = 8'hF3;
      tmp[(5*8)+:8] = 8'h76;

      // Z480 monitor stub @ 0x0040 (Z480_RESET_PC): signature + UART poll
      tmp[(64*8)+:8] = 8'h00;
      tmp[(65*8)+:8] = 8'hF0;
      tmp[(66*8)+:8] = 8'h01;
      tmp[(67*8)+:8] = 8'h20;
      tmp[(68*8)+:8] = 8'h5A;
      tmp[(69*8)+:8] = 8'h34;
      tmp[(70*8)+:8] = 8'h02;
      tmp[(71*8)+:8] = 8'h20;
      tmp[(72*8)+:8] = 8'h00;
      tmp[(73*8)+:8] = 8'h00;
      tmp[(74*8)+:8] = 8'h22;
      tmp[(75*8)+:8] = 8'hA4;
      tmp[(76*8)+:8] = 8'h38;
      tmp[(77*8)+:8] = 8'h30;
      tmp[(78*8)+:8] = 8'h02;
      tmp[(79*8)+:8] = 8'h20;
      tmp[(80*8)+:8] = 8'h02;
      tmp[(81*8)+:8] = 8'h00;
      tmp[(82*8)+:8] = 8'h22;
      tmp[(83*8)+:8] = 8'hA4;
      tmp[(84*8)+:8] = 8'h00;
      tmp[(85*8)+:8] = 8'h01;
      tmp[(86*8)+:8] = 8'h03;
      tmp[(87*8)+:8] = 8'h20;
      tmp[(88*8)+:8] = 8'h20;
      tmp[(89*8)+:8] = 8'h20;
      tmp[(90*8)+:8] = 8'h23;
      tmp[(91*8)+:8] = 8'h00;
      tmp[(92*8)+:8] = 8'h02;
      tmp[(93*8)+:8] = 8'h00;
      tmp[(94*8)+:8] = 8'h05;
      tmp[(95*8)+:8] = 8'h20;
      tmp[(96*8)+:8] = 8'h04;
      tmp[(97*8)+:8] = 8'h00;
      tmp[(98*8)+:8] = 8'h86;
      tmp[(99*8)+:8] = 8'h8C;
      tmp[(100*8)+:8] = 8'h24;
      tmp[(101*8)+:8] = 8'h30;
      tmp[(102*8)+:8] = 8'hC5;
      tmp[(103*8)+:8] = 8'h00;
      tmp[(104*8)+:8] = 8'hFD;
      tmp[(105*8)+:8] = 8'hFF;
      tmp[(106*8)+:8] = 8'hC0;
      tmp[(107*8)+:8] = 8'h10;
      tmp[(108*8)+:8] = 8'h01;
      tmp[(109*8)+:8] = 8'h00;
      tmp[(110*8)+:8] = 8'h02;
      tmp[(111*8)+:8] = 8'h20;
      tmp[(112*8)+:8] = 8'h04;
      tmp[(113*8)+:8] = 8'h00;
      tmp[(114*8)+:8] = 8'h22;
      tmp[(115*8)+:8] = 8'hAC;
      tmp[(116*8)+:8] = 8'h10;
      tmp[(117*8)+:8] = 8'h00;
      tmp[(118*8)+:8] = 8'h00;
      tmp[(119*8)+:8] = 8'h08;

      build_rom_image = tmp;
    end
  endfunction

  localparam logic [ROM_BYTES*8-1:0] ROM_IMAGE = build_rom_image();
  localparam logic [DISCOVERY_BYTES*8-1:0] DISCOVERY_IMAGE = build_discovery_rom();

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
      .BASE_ADDR(CARBON_SYS16_DISCOVERY_BASE),
      .ROM_BYTES(DISCOVERY_BYTES),
      .INIT_IMAGE(DISCOVERY_IMAGE),
      .RESP_LATENCY(1)
  ) u_discovery (
      .clk(clk),
      .rst_n(rst_n),
      .bus(s_if[S_DISCOVERY])
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

  wire _unused = ^{fpu_csr_fault, fpu_csr_rdata[0], carbonio_uart_rx_ready,
                   carbonio_uart_tx_valid, carbonio_uart_tx_data, carbonio_pio_out,
                   carbonio_pio_dir, irq_carbonio.irq_valid, irq_carbonio.irq_vector,
                   irq_carbonio.irq_prio, irq_carbonio.irq_pending,
                   host_active_tier, host_active_core};

endmodule : carbonz480_top
