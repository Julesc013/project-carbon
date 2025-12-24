`define CARBON_ENABLE_SVA
`timescale 1ns/1ps

module tb_discovery_contract;
  import carbon_arch_pkg::*;

  localparam logic [31:0] DISC_BASE = 32'h0000_1000;
  localparam logic [31:0] TOPO_BASE = 32'h0000_2000;
  localparam logic [31:0] BDT_BASE  = 32'h0000_3000;

  localparam logic [63:0] TOPO_PTR = 64'h0000_0000_0000_2000;
  localparam logic [63:0] BDT_PTR  = 64'h0000_0000_0000_3000;

  localparam logic [7:0] PRESENTED_CPU = CARBON_Z80_DERIVED_TIER_P2_Z80;
  localparam logic [7:0] PRESENTED_FPU = CARBON_AM95XX_FPU_TIER_P0_AM9511;
  localparam logic [7:0] PROFILE_ID    = CARBON_PROFILE_SOC_RETRO;

  localparam logic [15:0] TOPO_SOCKET_ID = 16'h0001;
  localparam logic [15:0] TOPO_CLUSTER_ID = 16'h0002;
  localparam logic [15:0] TOPO_CORE_ID = 16'h0003;
  localparam logic [15:0] TOPO_THREAD_ID = 16'h0000;
  localparam logic [15:0] TOPO_L1_ID = 16'h0010;
  localparam logic [15:0] TOPO_L2_ID = 16'h0020;
  localparam logic [15:0] TOPO_L3_ID = 16'h0030;
  localparam logic [15:0] TOPO_COH_ID = 16'h0001;
  localparam logic [15:0] TOPO_NUMA_ID = 16'h0000;

  localparam int unsigned BDT_HEADER_BYTES = CARBON_BDT_HEADER_V1_SIZE_BYTES;
  localparam int unsigned BDT_ENTRY_BYTES = CARBON_BDT_ENTRY_V1_SIZE_BYTES;
  localparam int unsigned BDT_IRQ_BASE = BDT_HEADER_BYTES + BDT_ENTRY_BYTES;

  logic clk;
  logic rst_n;

  clock_reset_bfm #(
      .CLK_PERIOD(10ns),
      .RESET_CYCLES(4)
  ) clk_rst (
      .clk(clk),
      .rst_n(rst_n)
  );

  initial begin
    clk_rst.apply_reset();
  end

  csr_if csr_disc (.clk(clk), .rst_n(rst_n));
  csr_if csr_topo (.clk(clk), .rst_n(rst_n));
  csr_if csr_bdt  (.clk(clk), .rst_n(rst_n));

  csr_bfm bfm_disc (.clk(clk), .rst_n(rst_n), .csr(csr_disc));
  csr_bfm bfm_topo (.clk(clk), .rst_n(rst_n), .csr(csr_topo));
  csr_bfm bfm_bdt  (.clk(clk), .rst_n(rst_n), .csr(csr_bdt));

  caprom_table #(
      .BASE_ADDR(DISC_BASE),
      .PRESENTED_CPU_TIER(PRESENTED_CPU),
      .PRESENTED_FPU_TIER(PRESENTED_FPU),
      .PROFILE_ID(PROFILE_ID),
      .TOPOLOGY_PTR(TOPO_PTR),
      .BDT_PTR(BDT_PTR)
  ) u_disc (
      .clk(clk),
      .rst_n(rst_n),
      .csr(csr_disc)
  );

  topology_rom #(
      .BASE_ADDR(TOPO_BASE),
      .ENTRY_COUNT(1),
      .SOCKET_ID('{TOPO_SOCKET_ID}),
      .CLUSTER_ID('{TOPO_CLUSTER_ID}),
      .CORE_ID('{TOPO_CORE_ID}),
      .THREAD_ID('{TOPO_THREAD_ID}),
      .CACHE_L1_ID('{TOPO_L1_ID}),
      .CACHE_L2_ID('{TOPO_L2_ID}),
      .CACHE_L3_ID('{TOPO_L3_ID}),
      .COHERENCE_DOMAIN_ID('{TOPO_COH_ID}),
      .NUMA_NODE_ID('{TOPO_NUMA_ID})
  ) u_topo (
      .clk(clk),
      .rst_n(rst_n),
      .csr(csr_topo)
  );

  bdt_rom #(
      .BASE_ADDR(BDT_BASE),
      .ENTRY_COUNT(1),
      .IRQ_ROUTE_TABLE_COUNT(1),
      .CLASS_ID('{16'(CARBON_DEVCLASS_UART)}),
      .SUBCLASS_ID('{16'h0000}),
      .INSTANCE_ID('{16'h0000}),
      .DEVICE_VERSION('{16'h0001}),
      .CAPS0('{32'h0000_0001}),
      .CAPS1('{32'h0000_0000}),
      .IRQ_ROUTE_OFFSET('{16'(BDT_IRQ_BASE)}),
      .IRQ_ROUTE_COUNT_PER_DEV('{16'h0001}),
      .MMIO_BASE('{64'h0000_0000_0000_0000}),
      .MMIO_SIZE('{32'h0000_0000}),
      .IO_PORT_BASE('{32'h0000_00F0}),
      .IO_PORT_SIZE('{16'h0008}),
      .BLOCK_SECTOR_SIZE('{16'd512}),
      .CAI_QUEUE_COUNT('{16'h0000}),
      .CAI_DOORBELL_OFFSET('{16'h0000}),
      .IRQ_ROUTE_DOMAIN_ID('{16'h0000}),
      .IRQ_ROUTE_LINE('{16'h0005}),
      .IRQ_ROUTE_FLAGS('{16'h0000})
  ) u_bdt (
      .clk(clk),
      .rst_n(rst_n),
      .csr(csr_bdt)
  );

  initial begin
    logic [31:0] rdata;
    logic fault;

    logic [31:0] exp_word;
    logic [31:0] lo;
    logic [31:0] hi;

    wait (rst_n);

    // Discovery table header
    bfm_disc.csr_read(DISC_BASE + 0, 2'b01, rdata, fault);
    if (fault) $fatal(1, "discovery signature fault");
    if (rdata != 32'h4353_4443) $fatal(1, "discovery signature mismatch");

    exp_word = {16'(CARBON_CARBON_DISCOVERY_TABLE_V1_SIZE_BYTES),
                16'(CARBON_CARBON_DISCOVERY_TABLE_V1_VERSION)};
    bfm_disc.csr_read(DISC_BASE + 4, 2'b01, rdata, fault);
    if (fault) $fatal(1, "discovery version fault");
    if (rdata != exp_word) $fatal(1, "discovery version mismatch");

    exp_word = {PRESENTED_FPU, PRESENTED_CPU, 8'(CARBON_TIER_LADDER_AM95), 8'(CARBON_TIER_LADDER_Z80)};
    bfm_disc.csr_read(DISC_BASE + 8, 2'b01, rdata, fault);
    if (fault) $fatal(1, "discovery tiers fault");
    if (rdata != exp_word) $fatal(1, "discovery tiers mismatch");

    exp_word = {24'h0, PROFILE_ID};
    bfm_disc.csr_read(DISC_BASE + 12, 2'b01, rdata, fault);
    if (fault) $fatal(1, "discovery profile fault");
    if (rdata != exp_word) $fatal(1, "discovery profile mismatch");

    bfm_disc.csr_read(DISC_BASE + 16, 2'b01, lo, fault);
    if (fault) $fatal(1, "discovery topo ptr lo fault");
    bfm_disc.csr_read(DISC_BASE + 20, 2'b01, hi, fault);
    if (fault) $fatal(1, "discovery topo ptr hi fault");
    if ({hi, lo} != TOPO_PTR) $fatal(1, "discovery topo ptr mismatch");

    bfm_disc.csr_read(DISC_BASE + 24, 2'b01, lo, fault);
    if (fault) $fatal(1, "discovery bdt ptr lo fault");
    bfm_disc.csr_read(DISC_BASE + 28, 2'b01, hi, fault);
    if (fault) $fatal(1, "discovery bdt ptr hi fault");
    if ({hi, lo} != BDT_PTR) $fatal(1, "discovery bdt ptr mismatch");

    // Topology table header
    bfm_topo.csr_read(TOPO_BASE + 0, 2'b01, rdata, fault);
    if (fault) $fatal(1, "topology signature fault");
    if (rdata != 32'h4354_4F50) $fatal(1, "topology signature mismatch");

    exp_word = {16'(CARBON_TOPOLOGY_HEADER_V1_SIZE_BYTES),
                16'(CARBON_TOPOLOGY_HEADER_V1_VERSION)};
    bfm_topo.csr_read(TOPO_BASE + 4, 2'b01, rdata, fault);
    if (fault) $fatal(1, "topology version fault");
    if (rdata != exp_word) $fatal(1, "topology version mismatch");

    exp_word = {16'(1), 16'(CARBON_TOPOLOGY_ENTRY_V1_SIZE_BYTES)};
    bfm_topo.csr_read(TOPO_BASE + 8, 2'b01, rdata, fault);
    if (fault) $fatal(1, "topology entry size fault");
    if (rdata != exp_word) $fatal(1, "topology entry size mismatch");

    exp_word = 32'(CARBON_TOPOLOGY_HEADER_V1_SIZE_BYTES + CARBON_TOPOLOGY_ENTRY_V1_SIZE_BYTES);
    bfm_topo.csr_read(TOPO_BASE + 12, 2'b01, rdata, fault);
    if (fault) $fatal(1, "topology total size fault");
    if (rdata != exp_word) $fatal(1, "topology total size mismatch");

    exp_word = {TOPO_CLUSTER_ID, TOPO_SOCKET_ID};
    bfm_topo.csr_read(TOPO_BASE + CARBON_TOPOLOGY_HEADER_V1_SIZE_BYTES + 0, 2'b01, rdata, fault);
    if (fault) $fatal(1, "topology entry0 fault");
    if (rdata != exp_word) $fatal(1, "topology entry0 mismatch");

    exp_word = {TOPO_THREAD_ID, TOPO_CORE_ID};
    bfm_topo.csr_read(TOPO_BASE + CARBON_TOPOLOGY_HEADER_V1_SIZE_BYTES + 4, 2'b01, rdata, fault);
    if (fault) $fatal(1, "topology entry1 fault");
    if (rdata != exp_word) $fatal(1, "topology entry1 mismatch");

    // BDT header
    bfm_bdt.csr_read(BDT_BASE + 0, 2'b01, rdata, fault);
    if (fault) $fatal(1, "bdt signature fault");
    if (rdata != 32'h5444_4243) $fatal(1, "bdt signature mismatch");

    exp_word = {16'(CARBON_BDT_HEADER_V1_SIZE_BYTES),
                16'(CARBON_BDT_HEADER_V1_VERSION)};
    bfm_bdt.csr_read(BDT_BASE + 4, 2'b01, rdata, fault);
    if (fault) $fatal(1, "bdt version fault");
    if (rdata != exp_word) $fatal(1, "bdt version mismatch");

    exp_word = {16'(1), 16'(CARBON_BDT_ENTRY_V1_SIZE_BYTES)};
    bfm_bdt.csr_read(BDT_BASE + 8, 2'b01, rdata, fault);
    if (fault) $fatal(1, "bdt entry size fault");
    if (rdata != exp_word) $fatal(1, "bdt entry size mismatch");

    exp_word = 32'(BDT_HEADER_BYTES + BDT_ENTRY_BYTES + CARBON_BDT_IRQ_ROUTE_V1_ENTRY_SIZE_BYTES);
    bfm_bdt.csr_read(BDT_BASE + 12, 2'b01, rdata, fault);
    if (fault) $fatal(1, "bdt total size fault");
    if (rdata != exp_word) $fatal(1, "bdt total size mismatch");

    exp_word = {16'(CARBON_BDT_ENTRY_V1_SIZE_BYTES), 16'(CARBON_BDT_ENTRY_V1_VERSION)};
    bfm_bdt.csr_read(BDT_BASE + BDT_HEADER_BYTES + 0, 2'b01, rdata, fault);
    if (fault) $fatal(1, "bdt entry desc fault");
    if (rdata != exp_word) $fatal(1, "bdt entry desc mismatch");

    exp_word = {16'h0000, 16'(CARBON_DEVCLASS_UART)};
    bfm_bdt.csr_read(BDT_BASE + BDT_HEADER_BYTES + 4, 2'b01, rdata, fault);
    if (fault) $fatal(1, "bdt class fault");
    if (rdata != exp_word) $fatal(1, "bdt class mismatch");

    exp_word = {16'h0001, 16'h0000};
    bfm_bdt.csr_read(BDT_BASE + BDT_HEADER_BYTES + 8, 2'b01, rdata, fault);
    if (fault) $fatal(1, "bdt instance fault");
    if (rdata != exp_word) $fatal(1, "bdt instance mismatch");

    bfm_bdt.csr_read(BDT_BASE + BDT_HEADER_BYTES + 12, 2'b01, rdata, fault);
    if (fault) $fatal(1, "bdt caps0 fault");
    if (rdata != 32'h0000_0001) $fatal(1, "bdt caps0 mismatch");

    exp_word = {16'h0001, 16'(BDT_IRQ_BASE)};
    bfm_bdt.csr_read(BDT_BASE + BDT_HEADER_BYTES + 20, 2'b01, rdata, fault);
    if (fault) $fatal(1, "bdt irq offset fault");
    if (rdata != exp_word) $fatal(1, "bdt irq offset mismatch");

    exp_word = {16'd512, 16'h0008};
    bfm_bdt.csr_read(BDT_BASE + BDT_HEADER_BYTES + 40, 2'b01, rdata, fault);
    if (fault) $fatal(1, "bdt io/sector fault");
    if (rdata != exp_word) $fatal(1, "bdt io/sector mismatch");

    exp_word = {16'h0000, 16'h0000};
    bfm_bdt.csr_read(BDT_BASE + BDT_HEADER_BYTES + 44, 2'b01, rdata, fault);
    if (fault) $fatal(1, "bdt cai fault");
    if (rdata != exp_word) $fatal(1, "bdt cai mismatch");

    exp_word = {16'h0005, 16'h0000};
    bfm_bdt.csr_read(BDT_BASE + BDT_IRQ_BASE + 0, 2'b01, rdata, fault);
    if (fault) $fatal(1, "bdt irq entry fault");
    if (rdata != exp_word) $fatal(1, "bdt irq entry mismatch");

    bfm_bdt.csr_read(BDT_BASE + BDT_IRQ_BASE + 4, 2'b01, rdata, fault);
    if (fault) $fatal(1, "bdt irq flags fault");
    if (rdata != 32'h0000_0000) $fatal(1, "bdt irq flags mismatch");

    $display("tb_discovery_contract: PASS");
    $finish;
  end

endmodule
