// Project Carbon - CarbonIO peripheral
// carbonio_pkg: Local constants for CarbonIO register maps and IRQ sources.

package carbonio_pkg;
  import carbon_arch_pkg::*;

  localparam int unsigned CARBONIO_UART_RX_DEPTH_DEFAULT = 64;
  localparam int unsigned CARBONIO_UART_TX_DEPTH_DEFAULT = 64;
  localparam int unsigned CARBONIO_PIO_WIDTH_DEFAULT = 32;
  localparam int unsigned CARBONIO_EDGE_FIFO_DEPTH_DEFAULT = 16;
  localparam int unsigned CARBONIO_TIMER_COUNT_DEFAULT = 2;

  // IRQ source indices.
  localparam int unsigned CARBONIO_IRQ_SRC_UART_RX = 0;
  localparam int unsigned CARBONIO_IRQ_SRC_UART_TX = 1;
  localparam int unsigned CARBONIO_IRQ_SRC_PIO_EDGE = 2;
  localparam int unsigned CARBONIO_IRQ_SRC_PIO_MATCH = 3;
  localparam int unsigned CARBONIO_IRQ_SRC_TIMER0 = 4;
  localparam int unsigned CARBONIO_IRQ_SRC_TIMER1 = 5;
  localparam int unsigned CARBONIO_IRQ_SRC_COUNT = 6;

  // Compatibility register offsets (byte offsets from COMPAT_BASE_ADDR).
  localparam logic [31:0] CARBONIO_COMPAT_UART_DATA_OFF = 32'h0000_0000;
  localparam logic [31:0] CARBONIO_COMPAT_UART_STATUS_OFF = 32'h0000_0004;
  localparam logic [31:0] CARBONIO_COMPAT_UART_CTRL_OFF = 32'h0000_0008;
  localparam logic [31:0] CARBONIO_COMPAT_UART_RX_COUNT_OFF = 32'h0000_000C;
  localparam logic [31:0] CARBONIO_COMPAT_UART_TX_COUNT_OFF = 32'h0000_0010;
  localparam logic [31:0] CARBONIO_COMPAT_UART_TS_LO_OFF = 32'h0000_0014;
  localparam logic [31:0] CARBONIO_COMPAT_UART_TS_HI_OFF = 32'h0000_0018;
  localparam logic [31:0] CARBONIO_COMPAT_UART_WATERMARKS_OFF = 32'h0000_001C;

  localparam logic [31:0] CARBONIO_COMPAT_PIO_IN_OFF = 32'h0000_0020;
  localparam logic [31:0] CARBONIO_COMPAT_PIO_OUT_OFF = 32'h0000_0024;
  localparam logic [31:0] CARBONIO_COMPAT_PIO_DIR_OFF = 32'h0000_0028;
  localparam logic [31:0] CARBONIO_COMPAT_PIO_EDGE_RDATA_OFF = 32'h0000_002C;
  localparam logic [31:0] CARBONIO_COMPAT_PIO_EDGE_COUNT_OFF = 32'h0000_0030;
  localparam logic [31:0] CARBONIO_COMPAT_PIO_FILTER_CFG_OFF = 32'h0000_0034;
  localparam logic [31:0] CARBONIO_COMPAT_PIO_MATCH_CFG_OFF = 32'h0000_0038;

  localparam logic [31:0] CARBONIO_COMPAT_TICK_LO_OFF = 32'h0000_0040;
  localparam logic [31:0] CARBONIO_COMPAT_TICK_HI_OFF = 32'h0000_0044;
  localparam logic [31:0] CARBONIO_COMPAT_TIMER0_LOAD_OFF = 32'h0000_0048;
  localparam logic [31:0] CARBONIO_COMPAT_TIMER0_VALUE_OFF = 32'h0000_004C;
  localparam logic [31:0] CARBONIO_COMPAT_TIMER0_CTRL_OFF = 32'h0000_0050;
  localparam logic [31:0] CARBONIO_COMPAT_TIMER0_STATUS_OFF = 32'h0000_0054;
  localparam logic [31:0] CARBONIO_COMPAT_TIMER1_LOAD_OFF = 32'h0000_0058;
  localparam logic [31:0] CARBONIO_COMPAT_TIMER1_VALUE_OFF = 32'h0000_005C;
  localparam logic [31:0] CARBONIO_COMPAT_TIMER1_CTRL_OFF = 32'h0000_0060;
  localparam logic [31:0] CARBONIO_COMPAT_TIMER1_STATUS_OFF = 32'h0000_0064;

  localparam logic [31:0] CARBONIO_COMPAT_IRQ_ENABLE_OFF = 32'h0000_0070;
  localparam logic [31:0] CARBONIO_COMPAT_IRQ_PENDING_OFF = 32'h0000_0074;
  localparam logic [31:0] CARBONIO_COMPAT_IRQ_MASK_OFF = 32'h0000_0078;

  // UART status bits for compatibility window.
  localparam int unsigned CARBONIO_UART_STATUS_RX_AVAIL_BIT = 0;
  localparam int unsigned CARBONIO_UART_STATUS_TX_SPACE_BIT = 1;
  localparam int unsigned CARBONIO_UART_STATUS_RX_OVF_BIT   = 2;
  localparam int unsigned CARBONIO_UART_STATUS_TX_OVF_BIT   = 3;

  // UART control bits (compat/CSR).
  localparam int unsigned CARBONIO_UART_CTRL_ENABLE_BIT     = 0;
  localparam int unsigned CARBONIO_UART_CTRL_RX_IRQ_EN_BIT  = 1;
  localparam int unsigned CARBONIO_UART_CTRL_TX_IRQ_EN_BIT  = 2;
  localparam int unsigned CARBONIO_UART_CTRL_TS_EN_BIT      = 3;
  localparam int unsigned CARBONIO_UART_CTRL_CLR_ERR_BIT    = 4;

endpackage : carbonio_pkg
