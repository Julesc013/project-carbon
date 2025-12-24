// Project Carbon - Common Infrastructure
// caprom_table: CSR-visible ROM view of the discovery table (v1).

module caprom_table #(
    parameter int unsigned ADDR_W = 32,
    parameter int unsigned DATA_W = 32,
    parameter logic [ADDR_W-1:0] BASE_ADDR = '0,

    parameter logic [7:0] CPU_LADDER_ID = carbon_arch_pkg::CARBON_TIER_LADDER_Z80,
    parameter logic [7:0] FPU_LADDER_ID = carbon_arch_pkg::CARBON_TIER_LADDER_AM95,
    parameter logic [7:0] PRESENTED_CPU_TIER = carbon_arch_pkg::CARBON_Z80_DERIVED_TIER_P0_I8080,
    parameter logic [7:0] PRESENTED_FPU_TIER = carbon_arch_pkg::CARBON_AM95XX_FPU_TIER_P0_AM9511,
    parameter logic [7:0] PROFILE_ID = carbon_arch_pkg::CARBON_PROFILE_CPU_ONLY,

    parameter logic [63:0] TOPOLOGY_PTR = 64'h0,
    parameter logic [63:0] BDT_PTR = 64'h0,
    parameter logic [63:0] LIMITS_PTR = 64'h0,
    parameter logic [63:0] CPU_FEAT_PTR = 64'h0,
    parameter logic [63:0] FPU_FEAT_PTR = 64'h0,
    parameter logic [63:0] PERIPH_FEAT_PTR = 64'h0
) (
    input logic clk,
    input logic rst_n,
    csr_if.slave csr
);
  import carbon_arch_pkg::*;

  localparam int unsigned TABLE_BYTES = CARBON_CARBON_DISCOVERY_TABLE_V1_SIZE_BYTES;
  localparam int unsigned DATA_BYTES = DATA_W / 8;
  localparam logic [31:0] DISCOVERY_SIGNATURE = 32'h43534443; // "CDSC"

  logic [TABLE_BYTES*8-1:0] rom_flat;

  always_comb begin
    rom_flat = '0;
    rom_flat[CARBON_CARBON_DISCOVERY_TABLE_V1_OFF_SIGNATURE*8 +: 32] = DISCOVERY_SIGNATURE;
    rom_flat[CARBON_CARBON_DISCOVERY_TABLE_V1_OFF_TABLE_VERSION*8 +: 16] = logic [15:0]'(CARBON_CARBON_DISCOVERY_TABLE_V1_VERSION);
    rom_flat[CARBON_CARBON_DISCOVERY_TABLE_V1_OFF_TABLE_SIZE*8 +: 16] = logic [15:0]'(TABLE_BYTES);
    rom_flat[CARBON_CARBON_DISCOVERY_TABLE_V1_OFF_CPU_LADDER_ID*8 +: 8] = CPU_LADDER_ID;
    rom_flat[CARBON_CARBON_DISCOVERY_TABLE_V1_OFF_FPU_LADDER_ID*8 +: 8] = FPU_LADDER_ID;
    rom_flat[CARBON_CARBON_DISCOVERY_TABLE_V1_OFF_PRESENTED_CPU_TIER*8 +: 8] = PRESENTED_CPU_TIER;
    rom_flat[CARBON_CARBON_DISCOVERY_TABLE_V1_OFF_PRESENTED_FPU_TIER*8 +: 8] = PRESENTED_FPU_TIER;
    rom_flat[CARBON_CARBON_DISCOVERY_TABLE_V1_OFF_PROFILE_ID*8 +: 8] = PROFILE_ID;
    rom_flat[CARBON_CARBON_DISCOVERY_TABLE_V1_OFF_TOPOLOGY_TABLE_PTR*8 +: 64] = TOPOLOGY_PTR;
    rom_flat[CARBON_CARBON_DISCOVERY_TABLE_V1_OFF_BDT_PTR*8 +: 64] = BDT_PTR;
    rom_flat[CARBON_CARBON_DISCOVERY_TABLE_V1_OFF_LIMITS_TABLE_PTR*8 +: 64] = LIMITS_PTR;
    rom_flat[CARBON_CARBON_DISCOVERY_TABLE_V1_OFF_CPU_FEATURE_BITMAP_PTR*8 +: 64] = CPU_FEAT_PTR;
    rom_flat[CARBON_CARBON_DISCOVERY_TABLE_V1_OFF_FPU_FEATURE_BITMAP_PTR*8 +: 64] = FPU_FEAT_PTR;
    rom_flat[CARBON_CARBON_DISCOVERY_TABLE_V1_OFF_PERIPHERAL_FEATURE_BITMAP_PTR*8 +: 64] = PERIPH_FEAT_PTR;
  end

  function automatic logic [DATA_W-1:0] read_word_at(input int unsigned offset);
    int unsigned b;
    begin
      read_word_at = '0;
      for (b = 0; b < DATA_BYTES; b++) begin
        if ((offset + b) < TABLE_BYTES) begin
          read_word_at[b*8 +: 8] = rom_flat[(offset + b)*8 +: 8];
        end
      end
    end
  endfunction

  // CSR response registers (single outstanding transaction).
  logic                  rsp_valid_q;
  logic [DATA_W-1:0]      rsp_rdata_q;
  logic                  rsp_fault_q;
  logic                  rsp_side_q;

  assign csr.req_ready       = !rsp_valid_q;
  assign csr.rsp_valid       = rsp_valid_q;
  assign csr.rsp_rdata       = rsp_rdata_q;
  assign csr.rsp_fault       = rsp_fault_q;
  assign csr.rsp_side_effect = rsp_side_q;

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      rsp_valid_q <= 1'b0;
      rsp_rdata_q <= '0;
      rsp_fault_q <= 1'b0;
      rsp_side_q  <= 1'b0;
    end else begin
      if (rsp_valid_q && csr.rsp_ready) begin
        rsp_valid_q <= 1'b0;
      end

      if (csr.req_valid && csr.req_ready) begin
        int unsigned addr_off;
        rsp_valid_q <= 1'b1;
        rsp_fault_q <= 1'b0;
        rsp_side_q  <= csr.req_write;
        rsp_rdata_q <= '0;

        if (csr.req_write) begin
          rsp_fault_q <= 1'b1;
        end else if (csr.req_addr < BASE_ADDR) begin
          rsp_fault_q <= 1'b1;
        end else begin
          addr_off = int'(csr.req_addr - BASE_ADDR);
          if ((addr_off + DATA_BYTES) > TABLE_BYTES) begin
            rsp_fault_q <= 1'b1;
          end else begin
            rsp_rdata_q <= read_word_at(addr_off);
          end
        end
      end
    end
  end

endmodule : caprom_table
