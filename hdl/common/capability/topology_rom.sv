// Project Carbon - Common Infrastructure
// topology_rom: CSR-visible ROM view of the topology table (v1).

module topology_rom #(
    parameter int unsigned ADDR_W = 32,
    parameter int unsigned DATA_W = 32,
    parameter logic [ADDR_W-1:0] BASE_ADDR = '0,

    parameter int unsigned ENTRY_COUNT = 1,
    parameter logic [15:0] SOCKET_ID [0:ENTRY_COUNT-1] = '{default: 16'h0},
    parameter logic [15:0] CLUSTER_ID [0:ENTRY_COUNT-1] = '{default: 16'h0},
    parameter logic [15:0] CORE_ID [0:ENTRY_COUNT-1] = '{default: 16'h0},
    parameter logic [15:0] THREAD_ID [0:ENTRY_COUNT-1] = '{default: 16'h0},
    parameter logic [15:0] CACHE_L1_ID [0:ENTRY_COUNT-1] = '{default: 16'h0},
    parameter logic [15:0] CACHE_L2_ID [0:ENTRY_COUNT-1] = '{default: 16'h0},
    parameter logic [15:0] CACHE_L3_ID [0:ENTRY_COUNT-1] = '{default: 16'h0},
    parameter logic [15:0] COHERENCE_DOMAIN_ID [0:ENTRY_COUNT-1] = '{default: 16'h0},
    parameter logic [15:0] NUMA_NODE_ID [0:ENTRY_COUNT-1] = '{default: 16'h0}
) (
    input logic clk,
    input logic rst_n,
    csr_if.slave csr
);
  import carbon_arch_pkg::*;

  localparam int unsigned HEADER_BYTES = CARBON_TOPOLOGY_HEADER_V1_SIZE_BYTES;
  localparam int unsigned ENTRY_BYTES = CARBON_TOPOLOGY_ENTRY_V1_SIZE_BYTES;
  localparam int unsigned TABLE_BYTES = HEADER_BYTES + (ENTRY_COUNT * ENTRY_BYTES);
  localparam int unsigned DATA_BYTES = DATA_W / 8;
  localparam logic [31:0] TOPO_SIGNATURE = 32'h504f5443; // "CTOP"

  logic [TABLE_BYTES*8-1:0] rom_flat;

  integer i;
  always_comb begin
    rom_flat = '0;
    rom_flat[CARBON_TOPOLOGY_HEADER_V1_OFF_SIGNATURE*8 +: 32] = TOPO_SIGNATURE;
    rom_flat[CARBON_TOPOLOGY_HEADER_V1_OFF_HEADER_VERSION*8 +: 16] = logic [15:0]'(CARBON_TOPOLOGY_HEADER_V1_VERSION);
    rom_flat[CARBON_TOPOLOGY_HEADER_V1_OFF_HEADER_SIZE*8 +: 16] = logic [15:0]'(HEADER_BYTES);
    rom_flat[CARBON_TOPOLOGY_HEADER_V1_OFF_ENTRY_SIZE*8 +: 16] = logic [15:0]'(ENTRY_BYTES);
    rom_flat[CARBON_TOPOLOGY_HEADER_V1_OFF_ENTRY_COUNT*8 +: 16] = logic [15:0]'(ENTRY_COUNT);
    rom_flat[CARBON_TOPOLOGY_HEADER_V1_OFF_TOTAL_SIZE*8 +: 32] = logic [31:0]'(TABLE_BYTES);

    for (i = 0; i < int'(ENTRY_COUNT); i++) begin
      int unsigned base;
      base = HEADER_BYTES + (i * ENTRY_BYTES);
      rom_flat[(base + CARBON_TOPOLOGY_ENTRY_V1_OFF_SOCKET_ID)*8 +: 16] = SOCKET_ID[i];
      rom_flat[(base + CARBON_TOPOLOGY_ENTRY_V1_OFF_CLUSTER_ID)*8 +: 16] = CLUSTER_ID[i];
      rom_flat[(base + CARBON_TOPOLOGY_ENTRY_V1_OFF_CORE_ID)*8 +: 16] = CORE_ID[i];
      rom_flat[(base + CARBON_TOPOLOGY_ENTRY_V1_OFF_THREAD_ID)*8 +: 16] = THREAD_ID[i];
      rom_flat[(base + CARBON_TOPOLOGY_ENTRY_V1_OFF_CACHE_L1_ID)*8 +: 16] = CACHE_L1_ID[i];
      rom_flat[(base + CARBON_TOPOLOGY_ENTRY_V1_OFF_CACHE_L2_ID)*8 +: 16] = CACHE_L2_ID[i];
      rom_flat[(base + CARBON_TOPOLOGY_ENTRY_V1_OFF_CACHE_L3_ID)*8 +: 16] = CACHE_L3_ID[i];
      rom_flat[(base + CARBON_TOPOLOGY_ENTRY_V1_OFF_COHERENCE_DOMAIN_ID)*8 +: 16] = COHERENCE_DOMAIN_ID[i];
      rom_flat[(base + CARBON_TOPOLOGY_ENTRY_V1_OFF_NUMA_NODE_ID)*8 +: 16] = NUMA_NODE_ID[i];
    end
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

endmodule : topology_rom
