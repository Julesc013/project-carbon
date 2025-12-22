// Project Carbon - CarbonDMA peripheral
// carbondma_pkg: Local constants for CarbonDMA register maps and DMA descriptors.

package carbondma_pkg;
  import carbon_arch_pkg::*;

  localparam int unsigned CARBONDMA_CHANNELS_DEFAULT = 4;

  // Compatibility register offsets (byte offsets from COMPAT_BASE_ADDR).
  localparam logic [31:0] CARBONDMA_COMPAT_ID_OFF         = 32'h0000_0000;
  localparam logic [31:0] CARBONDMA_COMPAT_STATUS_OFF     = 32'h0000_0004;
  localparam logic [31:0] CARBONDMA_COMPAT_CTRL_OFF       = 32'h0000_0008;
  localparam logic [31:0] CARBONDMA_COMPAT_CH_SEL_OFF     = 32'h0000_000C;
  localparam logic [31:0] CARBONDMA_COMPAT_CH_SRC_LO_OFF  = 32'h0000_0010;
  localparam logic [31:0] CARBONDMA_COMPAT_CH_SRC_HI_OFF  = 32'h0000_0014;
  localparam logic [31:0] CARBONDMA_COMPAT_CH_DST_LO_OFF  = 32'h0000_0018;
  localparam logic [31:0] CARBONDMA_COMPAT_CH_DST_HI_OFF  = 32'h0000_001C;
  localparam logic [31:0] CARBONDMA_COMPAT_CH_LEN_OFF     = 32'h0000_0020;
  localparam logic [31:0] CARBONDMA_COMPAT_CH_CTRL_OFF    = 32'h0000_0024;
  localparam logic [31:0] CARBONDMA_COMPAT_CH_STATUS_OFF  = 32'h0000_0028;
  localparam logic [31:0] CARBONDMA_COMPAT_CH_ATTR_OFF    = 32'h0000_002C;
  localparam logic [31:0] CARBONDMA_COMPAT_CH_FILL_OFF    = 32'h0000_0030;

  // Global control/status bits.
  localparam int unsigned CARBONDMA_CTRL_ENABLE_BIT   = 0;
  localparam int unsigned CARBONDMA_CTRL_CLR_ERR_BIT  = 1;

  localparam int unsigned CARBONDMA_STATUS_BUSY_BIT   = 0;
  localparam int unsigned CARBONDMA_STATUS_ERR_BIT    = 1;

  // Channel control/status bits.
  localparam int unsigned CARBONDMA_CH_CTRL_START_BIT = 0;
  localparam int unsigned CARBONDMA_CH_CTRL_FILL_BIT  = 1;

  localparam int unsigned CARBONDMA_CH_STATUS_BUSY_BIT = 0;
  localparam int unsigned CARBONDMA_CH_STATUS_DONE_BIT = 1;
  localparam int unsigned CARBONDMA_CH_STATUS_ERR_BIT  = 2;

  // Turbo queue opcodes.
  localparam int unsigned CARBONDMA_OP_COPY = 0;
  localparam int unsigned CARBONDMA_OP_FILL = 1;

  // Turbo status codes (TURBO_COMP_REC_V1).
  localparam int unsigned CARBONDMA_TURBO_STATUS_OK          = 0;
  localparam int unsigned CARBONDMA_TURBO_STATUS_INVALID     = 1;
  localparam int unsigned CARBONDMA_TURBO_STATUS_FAULT       = 2;
  localparam int unsigned CARBONDMA_TURBO_STATUS_BUSY        = 3;
  localparam int unsigned CARBONDMA_TURBO_STATUS_UNSUPPORTED = 4;

  // DMA scatter/gather descriptor (payload pointed to by turbo submit).
  localparam int unsigned CARBONDMA_DESC_V1_SIZE_BYTES = 32;
  localparam int unsigned CARBONDMA_DESC_V1_OFF_SRC_LO = 0;
  localparam int unsigned CARBONDMA_DESC_V1_OFF_SRC_HI = 4;
  localparam int unsigned CARBONDMA_DESC_V1_OFF_DST_LO = 8;
  localparam int unsigned CARBONDMA_DESC_V1_OFF_DST_HI = 12;
  localparam int unsigned CARBONDMA_DESC_V1_OFF_LEN    = 16;
  localparam int unsigned CARBONDMA_DESC_V1_OFF_FLAGS  = 20;
  localparam int unsigned CARBONDMA_DESC_V1_OFF_FILL   = 24;
  localparam int unsigned CARBONDMA_DESC_V1_OFF_ATTR   = 28;

  localparam int unsigned CARBONDMA_DESC_FLAG_FILL_BIT = 0;

endpackage : carbondma_pkg
