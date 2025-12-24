// Project Carbon - Common Infrastructure
// bdt_rom: CSR-visible ROM view of the BIOS Device Table (v1).

module bdt_rom #(
    parameter int unsigned ADDR_W = 32,
    parameter int unsigned DATA_W = 32,
    parameter logic [ADDR_W-1:0] BASE_ADDR = '0,

    parameter int unsigned ENTRY_COUNT = 1,
    parameter int unsigned IRQ_ROUTE_TABLE_COUNT = 1,

    parameter logic [15:0] CLASS_ID [0:ENTRY_COUNT-1] = '{default: 16'h0},
    parameter logic [15:0] SUBCLASS_ID [0:ENTRY_COUNT-1] = '{default: 16'h0},
    parameter logic [15:0] INSTANCE_ID [0:ENTRY_COUNT-1] = '{default: 16'h0},
    parameter logic [15:0] DEVICE_VERSION [0:ENTRY_COUNT-1] = '{default: 16'h0},
    parameter logic [31:0] CAPS0 [0:ENTRY_COUNT-1] = '{default: 32'h0},
    parameter logic [31:0] CAPS1 [0:ENTRY_COUNT-1] = '{default: 32'h0},
    parameter logic [15:0] IRQ_ROUTE_OFFSET [0:ENTRY_COUNT-1] = '{default: 16'h0},
    parameter logic [15:0] IRQ_ROUTE_COUNT_PER_DEV [0:ENTRY_COUNT-1] = '{default: 16'h0},
    parameter logic [63:0] MMIO_BASE [0:ENTRY_COUNT-1] = '{default: 64'h0},
    parameter logic [31:0] MMIO_SIZE [0:ENTRY_COUNT-1] = '{default: 32'h0},
    parameter logic [31:0] IO_PORT_BASE [0:ENTRY_COUNT-1] = '{default: 32'h0},
    parameter logic [15:0] IO_PORT_SIZE [0:ENTRY_COUNT-1] = '{default: 16'h0},
    parameter logic [15:0] BLOCK_SECTOR_SIZE [0:ENTRY_COUNT-1] = '{default: 16'h0},
    parameter logic [15:0] CAI_QUEUE_COUNT [0:ENTRY_COUNT-1] = '{default: 16'h0},
    parameter logic [15:0] CAI_DOORBELL_OFFSET [0:ENTRY_COUNT-1] = '{default: 16'h0},

    parameter logic [15:0] IRQ_ROUTE_DOMAIN_ID [0:IRQ_ROUTE_TABLE_COUNT-1] = '{default: 16'h0},
    parameter logic [15:0] IRQ_ROUTE_LINE [0:IRQ_ROUTE_TABLE_COUNT-1] = '{default: 16'h0},
    parameter logic [15:0] IRQ_ROUTE_FLAGS [0:IRQ_ROUTE_TABLE_COUNT-1] = '{default: 16'h0}
) (
    input logic clk,
    input logic rst_n,
    csr_if.slave csr
);
  import carbon_arch_pkg::*;

  localparam int unsigned HEADER_BYTES = CARBON_BDT_HEADER_V1_SIZE_BYTES;
  localparam int unsigned ENTRY_BYTES = CARBON_BDT_ENTRY_V1_SIZE_BYTES;
  localparam int unsigned IRQ_ENTRY_BYTES = CARBON_BDT_IRQ_ROUTE_V1_ENTRY_SIZE_BYTES;
  localparam int unsigned IRQ_BASE = HEADER_BYTES + (ENTRY_COUNT * ENTRY_BYTES);
  localparam int unsigned TABLE_BYTES = IRQ_BASE + (IRQ_ROUTE_TABLE_COUNT * IRQ_ENTRY_BYTES);
  localparam int unsigned DATA_BYTES = DATA_W / 8;
  localparam logic [31:0] BDT_SIGNATURE = 32'h54444243; // "CBDT"

  logic [TABLE_BYTES*8-1:0] rom_flat;

  integer i;
  always_comb begin
    rom_flat = '0;
    rom_flat[CARBON_BDT_HEADER_V1_OFF_SIGNATURE*8 +: 32] = BDT_SIGNATURE;
    rom_flat[CARBON_BDT_HEADER_V1_OFF_HEADER_VERSION*8 +: 16] = logic [15:0]'(CARBON_BDT_HEADER_V1_VERSION);
    rom_flat[CARBON_BDT_HEADER_V1_OFF_HEADER_SIZE*8 +: 16] = logic [15:0]'(HEADER_BYTES);
    rom_flat[CARBON_BDT_HEADER_V1_OFF_ENTRY_SIZE*8 +: 16] = logic [15:0]'(ENTRY_BYTES);
    rom_flat[CARBON_BDT_HEADER_V1_OFF_ENTRY_COUNT*8 +: 16] = logic [15:0]'(ENTRY_COUNT);
    rom_flat[CARBON_BDT_HEADER_V1_OFF_TOTAL_SIZE*8 +: 32] = logic [31:0]'(TABLE_BYTES);

    for (i = 0; i < int'(ENTRY_COUNT); i++) begin
      int unsigned base;
      base = HEADER_BYTES + (i * ENTRY_BYTES);
      rom_flat[(base + CARBON_BDT_ENTRY_V1_OFF_DESC_VERSION)*8 +: 16] = logic [15:0]'(CARBON_BDT_ENTRY_V1_VERSION);
      rom_flat[(base + CARBON_BDT_ENTRY_V1_OFF_DESC_SIZE_BYTES)*8 +: 16] = logic [15:0]'(ENTRY_BYTES);
      rom_flat[(base + CARBON_BDT_ENTRY_V1_OFF_CLASS_ID)*8 +: 16] = CLASS_ID[i];
      rom_flat[(base + CARBON_BDT_ENTRY_V1_OFF_SUBCLASS_ID)*8 +: 16] = SUBCLASS_ID[i];
      rom_flat[(base + CARBON_BDT_ENTRY_V1_OFF_INSTANCE_ID)*8 +: 16] = INSTANCE_ID[i];
      rom_flat[(base + CARBON_BDT_ENTRY_V1_OFF_DEVICE_VERSION)*8 +: 16] = DEVICE_VERSION[i];
      rom_flat[(base + CARBON_BDT_ENTRY_V1_OFF_CAPS0)*8 +: 32] = CAPS0[i];
      rom_flat[(base + CARBON_BDT_ENTRY_V1_OFF_CAPS1)*8 +: 32] = CAPS1[i];
      rom_flat[(base + CARBON_BDT_ENTRY_V1_OFF_IRQ_ROUTE_OFFSET)*8 +: 16] = IRQ_ROUTE_OFFSET[i];
      rom_flat[(base + CARBON_BDT_ENTRY_V1_OFF_IRQ_ROUTE_COUNT)*8 +: 16] = IRQ_ROUTE_COUNT_PER_DEV[i];
      rom_flat[(base + CARBON_BDT_ENTRY_V1_OFF_MMIO_BASE)*8 +: 64] = MMIO_BASE[i];
      rom_flat[(base + CARBON_BDT_ENTRY_V1_OFF_MMIO_SIZE)*8 +: 32] = MMIO_SIZE[i];
      rom_flat[(base + CARBON_BDT_ENTRY_V1_OFF_IO_PORT_BASE)*8 +: 32] = IO_PORT_BASE[i];
      rom_flat[(base + CARBON_BDT_ENTRY_V1_OFF_IO_PORT_SIZE)*8 +: 16] = IO_PORT_SIZE[i];
      rom_flat[(base + CARBON_BDT_ENTRY_V1_OFF_BLOCK_SECTOR_SIZE)*8 +: 16] = BLOCK_SECTOR_SIZE[i];
      rom_flat[(base + CARBON_BDT_ENTRY_V1_OFF_CAI_QUEUE_COUNT)*8 +: 16] = CAI_QUEUE_COUNT[i];
      rom_flat[(base + CARBON_BDT_ENTRY_V1_OFF_CAI_DOORBELL_OFFSET)*8 +: 16] = CAI_DOORBELL_OFFSET[i];
    end

    for (i = 0; i < int'(IRQ_ROUTE_TABLE_COUNT); i++) begin
      int unsigned base;
      base = IRQ_BASE + (i * IRQ_ENTRY_BYTES);
      rom_flat[(base + CARBON_BDT_IRQ_ROUTE_V1_OFF_DOMAIN_ID)*8 +: 16] = IRQ_ROUTE_DOMAIN_ID[i];
      rom_flat[(base + CARBON_BDT_IRQ_ROUTE_V1_OFF_IRQ_LINE)*8 +: 16] = IRQ_ROUTE_LINE[i];
      rom_flat[(base + CARBON_BDT_IRQ_ROUTE_V1_OFF_FLAGS)*8 +: 16] = IRQ_ROUTE_FLAGS[i];
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

endmodule : bdt_rom
