// Project Carbon - Systems
// carbon_memmap_pkg: Common address map constants for Carbon system tops.

package carbon_memmap_pkg;
  import carbon_arch_pkg::*;

  // --------------------------------------------------------------------------
  // Common MMIO register offsets (byte offsets within the MMIO block)
  // --------------------------------------------------------------------------
  localparam logic [31:0] CARBON_MMIO_SIGNATURE_OFF = 32'h0000_0000;
  localparam logic [31:0] CARBON_MMIO_POWEROFF_OFF  = 32'h0000_0004;
  localparam logic [31:0] CARBON_MMIO_UART_TX_OFF   = 32'h0000_0008;

  // --------------------------------------------------------------------------
  // 16-bit class systems (Z80/Z90): 64 KiB address space
  //
  // ROM is kept small so RAM can occupy most of the low 64 KiB. The ROM window
  // is implemented by address decode priority (ROM hits override RAM default).
  // --------------------------------------------------------------------------
  localparam logic [31:0] CARBON_SYS16_ROM_BASE  = 32'h0000_0000;
  localparam logic [31:0] CARBON_SYS16_ROM_MASK  = 32'hFFFF_FF00; // 256 B window
  localparam int unsigned CARBON_SYS16_ROM_BYTES = 256;

  localparam logic [31:0] CARBON_SYS16_MMIO_BASE = 32'h0000_F000;
  localparam logic [31:0] CARBON_SYS16_MMIO_MASK = 32'hFFFF_FF00; // 256 B window

  localparam logic [31:0] CARBON_SYS16_CARBONIO_BASE = 32'h0000_F100;
  localparam logic [31:0] CARBON_SYS16_CARBONIO_MASK = 32'hFFFF_FF00; // 256 B window

  localparam logic [31:0] CARBON_SYS16_CARBONDMA_BASE = 32'h0000_F200;
  localparam logic [31:0] CARBON_SYS16_CARBONDMA_MASK = 32'hFFFF_FF00; // 256 B window

  localparam logic [31:0] CARBON_SYS16_FAST_SRAM_BASE = 32'h0000_8000;
  localparam logic [31:0] CARBON_SYS16_FAST_SRAM_MASK = 32'hFFFF_C000; // 16 KiB placeholder window

  localparam int unsigned CARBON_SYS16_RAM_BYTES = 65536;

  // --------------------------------------------------------------------------
  // x86 real-mode class systems (8086/8096): 20-bit address space (1 MiB)
  // --------------------------------------------------------------------------
  localparam logic [31:0] CARBON_SYSX86_ROM_BASE  = 32'h0000_0000;
  localparam logic [31:0] CARBON_SYSX86_ROM_MASK  = 32'hFFFF_F000; // 4 KiB window
  localparam int unsigned CARBON_SYSX86_ROM_BYTES = 4096;

  localparam logic [31:0] CARBON_SYSX86_MMIO_BASE = 32'h000F_0000;
  localparam logic [31:0] CARBON_SYSX86_MMIO_MASK = 32'hFFFF_F000; // 4 KiB window

  localparam logic [31:0] CARBON_SYSX86_CARBONIO_BASE = 32'h000F_1000;
  localparam logic [31:0] CARBON_SYSX86_CARBONIO_MASK = 32'hFFFF_F000; // 4 KiB window

  localparam logic [31:0] CARBON_SYSX86_CARBONDMA_BASE = 32'h000F_2000;
  localparam logic [31:0] CARBON_SYSX86_CARBONDMA_MASK = 32'hFFFF_F000; // 4 KiB window

  localparam logic [31:0] CARBON_SYSX86_FAST_SRAM_BASE = 32'h0008_0000;
  localparam logic [31:0] CARBON_SYSX86_FAST_SRAM_MASK = 32'hFFFF_0000; // 64 KiB placeholder window

  localparam int unsigned CARBON_SYSX86_RAM_BYTES = 1048576;

endpackage : carbon_memmap_pkg
