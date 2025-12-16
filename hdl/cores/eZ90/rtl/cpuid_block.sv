// Project Carbon - eZ90 P7 core scaffold
// cpuid_block: Minimal CPUID leaf model (CSR-window transport for v1 scaffold).

module cpuid_block #(
    parameter int unsigned CORE_COUNT  = 1,
    parameter int unsigned VECTOR_BITS = 128
) (
    input  logic [31:0] leaf,
    input  logic [31:0] subleaf,
    output logic [63:0] data0,
    output logic [63:0] data1,
    output logic [63:0] data2,
    output logic [63:0] data3
);
  import carbon_arch_pkg::*;

  // Returns 4x32-bit words, widened to 64-bit lanes for the CSR window.
  logic [31:0] w0, w1, w2, w3;

  // "CARBON-eZ90 " (12 bytes, packed little-endian into 3x32-bit words)
  localparam logic [31:0] EZ90_VENDOR_STR_W1 = 32'h4252_4143;  // "CARB"
  localparam logic [31:0] EZ90_VENDOR_STR_W2 = 32'h652D_4E4F;  // "ON-e"
  localparam logic [31:0] EZ90_VENDOR_STR_W3 = 32'h2030_395A;  // "Z90 "

  // CPUID_LEAF_ID.word1 chip_flags (implementation-defined for eZ90 v1 scaffold)
  localparam int unsigned EZ90_CHIP_HAS_PRIV_U_BIT      = 0;
  localparam int unsigned EZ90_CHIP_HAS_PRIV_S_BIT      = 1;
  localparam int unsigned EZ90_CHIP_HAS_PRIV_H_BIT      = 2;
  localparam int unsigned EZ90_CHIP_HAS_OOO_SKELETON_BIT = 3;
  localparam int unsigned EZ90_CHIP_HAS_MMU_SCAFFOLD_BIT = 4;

  localparam logic [31:0] EZ90_CHIP_FLAGS =
      (32'h1 << EZ90_CHIP_HAS_PRIV_U_BIT) |
      (32'h1 << EZ90_CHIP_HAS_PRIV_S_BIT) |
      (32'h1 << EZ90_CHIP_HAS_PRIV_H_BIT) |
      (32'h1 << EZ90_CHIP_HAS_OOO_SKELETON_BIT) |
      (32'h1 << EZ90_CHIP_HAS_MMU_SCAFFOLD_BIT);

  always_comb begin
    w0 = '0;
    w1 = '0;
    w2 = '0;
    w3 = '0;

    unique case (leaf)
      CARBON_CPUID_LEAF_VENDOR: begin
        // word0: max_standard_leaf (15:0) | discovery_format_version (31:16)
        w0[15:0]  = 16'(CARBON_CPUID_LEAF_ERRATA0[15:0]);
        w0[31:16] = 16'd1;
        w1 = EZ90_VENDOR_STR_W1;
        w2 = EZ90_VENDOR_STR_W2;
        w3 = EZ90_VENDOR_STR_W3;
      end
      CARBON_CPUID_LEAF_ID: begin
        // word0: vendor/family/model/stepping (8-bit fields)
        w0 = {8'h01, 8'h07, 8'h90, 8'h00};  // stepping=1, model=7, family=0x90, vendor=0
        w1 = EZ90_CHIP_FLAGS;
      end
      CARBON_CPUID_LEAF_TIERS: begin
        w0[7:0]   = 8'(CARBON_TIER_LADDER_Z80);
        w0[15:8]  = 8'(CARBON_Z80_DERIVED_TIER_P7_TURBO_UNLIMITED);
        w0[23:16] = 8'(CARBON_Z80_DERIVED_TIER_P7_TURBO_UNLIMITED);
        w1        = 32'h0000_0000;
      end
      CARBON_CPUID_LEAF_FEATURES0: begin
        w0 = CARBON_FEAT_CSR_NAMESPACE_MASK |
            CARBON_FEAT_FABRIC_MASK |
            CARBON_FEAT_CPUID_MASK |
            CARBON_FEAT_IOMMU_HOOKS_MASK;
      end
      CARBON_CPUID_LEAF_TOPOLOGY: begin
        // word0: [15:0]=core_count, [31:16]=threads_per_core (v1 fixed 1)
        w0[15:0]  = 16'(CORE_COUNT[15:0]);
        w0[31:16] = 16'd1;
        // word1: [15:0]=vector_bits, [31:16]=arch_bits
        w1[15:0]  = 16'(VECTOR_BITS[15:0]);
        w1[31:16] = 16'd64;
      end
      default: begin
        // Unknown leaves return zeros (per discovery spec).
      end
    endcase

    data0 = {32'h0, w0};
    data1 = {32'h0, w1};
    data2 = {32'h0, w2};
    data3 = {32'h0, w3};
  end

  wire _unused = ^subleaf;

endmodule : cpuid_block

