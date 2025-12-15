// Project Carbon - Common Infrastructure
// caprom_reader: Read-only capability/discovery ROM exposed via a CSR window.
//
// This is an implementation helper for SoCs:
// - Data is provided by a parameterized leaf table (CPUID/CAPS-compatible leaf IDs).
// - Unknown leaf IDs return zeros (matches discovery.yaml unknown_leaf_behavior).
//
// TODO: integrate auto-generation from `hdl/spec/discovery.yaml`.

module caprom_reader #(
    parameter int unsigned ADDR_W = 32,
    parameter int unsigned DATA_W = 32,

    parameter int unsigned LEAF_COUNT = 6,
    parameter logic [31:0] LEAF_ID [LEAF_COUNT] = '{
        carbon_arch_pkg::CARBON_CPUID_LEAF_VENDOR,
        carbon_arch_pkg::CARBON_CPUID_LEAF_ID,
        carbon_arch_pkg::CARBON_CPUID_LEAF_TIERS,
        carbon_arch_pkg::CARBON_CPUID_LEAF_FEATURES0,
        carbon_arch_pkg::CARBON_CPUID_LEAF_ACCEL0,
        carbon_arch_pkg::CARBON_CPUID_LEAF_ERRATA0
    },
    parameter logic [31:0] LEAF_W0 [LEAF_COUNT] = '{default: 32'h0},
    parameter logic [31:0] LEAF_W1 [LEAF_COUNT] = '{default: 32'h0},
    parameter logic [31:0] LEAF_W2 [LEAF_COUNT] = '{default: 32'h0},
    parameter logic [31:0] LEAF_W3 [LEAF_COUNT] = '{default: 32'h0}
) (
    input logic clk,
    input logic rst_n,
    csr_if.slave csr
);
  import carbon_arch_pkg::*;

  // CSR window registers (platform-defined offsets).
  localparam logic [ADDR_W-1:0] REG_INDEX = '0;
  localparam logic [ADDR_W-1:0] REG_DATA0 = ADDR_W'(1);
  localparam logic [ADDR_W-1:0] REG_DATA1 = ADDR_W'(2);
  localparam logic [ADDR_W-1:0] REG_DATA2 = ADDR_W'(3);
  localparam logic [ADDR_W-1:0] REG_DATA3 = ADDR_W'(4);

  logic [31:0] index_q;

  logic              rsp_valid_q;
  logic [DATA_W-1:0] rsp_rdata_q;
  logic              rsp_fault_q;
  logic              rsp_side_q;

  assign csr.req_ready       = !rsp_valid_q;
  assign csr.rsp_valid       = rsp_valid_q;
  assign csr.rsp_rdata       = rsp_rdata_q;
  assign csr.rsp_fault       = rsp_fault_q;
  assign csr.rsp_side_effect = rsp_side_q;

  function automatic logic [31:0] leaf_lookup_word(input logic [31:0] leaf, input int unsigned word_sel);
    int unsigned i;
    begin
      leaf_lookup_word = 32'h0;
      for (i = 0; i < LEAF_COUNT; i++) begin
        if (LEAF_ID[i] == leaf) begin
          unique case (word_sel)
            0: leaf_lookup_word = LEAF_W0[i];
            1: leaf_lookup_word = LEAF_W1[i];
            2: leaf_lookup_word = LEAF_W2[i];
            3: leaf_lookup_word = LEAF_W3[i];
            default: leaf_lookup_word = 32'h0;
          endcase
        end
      end
    end
  endfunction

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      index_q     <= 32'h0;
      rsp_valid_q <= 1'b0;
      rsp_rdata_q <= '0;
      rsp_fault_q <= 1'b0;
      rsp_side_q  <= 1'b0;
    end else begin
      if (rsp_valid_q && csr.rsp_ready) begin
        rsp_valid_q <= 1'b0;
      end

      if (csr.req_valid && csr.req_ready) begin
        rsp_valid_q <= 1'b1;
        rsp_fault_q <= 1'b0;
        rsp_side_q  <= csr.req_write;
        rsp_rdata_q <= '0;

        unique case (csr.req_addr)
          REG_INDEX: begin
            if (csr.req_write) begin
              index_q <= csr.req_wdata;
            end else begin
              rsp_rdata_q <= index_q;
            end
          end
          REG_DATA0: begin
            if (!csr.req_write) rsp_rdata_q <= leaf_lookup_word(index_q, 0);
            else rsp_fault_q <= 1'b1;
          end
          REG_DATA1: begin
            if (!csr.req_write) rsp_rdata_q <= leaf_lookup_word(index_q, 1);
            else rsp_fault_q <= 1'b1;
          end
          REG_DATA2: begin
            if (!csr.req_write) rsp_rdata_q <= leaf_lookup_word(index_q, 2);
            else rsp_fault_q <= 1'b1;
          end
          REG_DATA3: begin
            if (!csr.req_write) rsp_rdata_q <= leaf_lookup_word(index_q, 3);
            else rsp_fault_q <= 1'b1;
          end
          default: begin
            rsp_fault_q <= 1'b1;
          end
        endcase
      end
    end
  end

endmodule : caprom_reader

