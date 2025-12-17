// Project Carbon - 8097 FPU (x87-like, v1.0)
// fpu_8097_pkg: Local encodings for CSR-driven command interface.

package fpu_8097_pkg;

  // CSR_8097_CMD opcodes (v1 CSR command window)
  localparam logic [7:0] FPU8097_CMD_NOP        = 8'h00;
  localparam logic [7:0] FPU8097_CMD_FADD       = 8'h01;
  localparam logic [7:0] FPU8097_CMD_FSUB       = 8'h02;
  localparam logic [7:0] FPU8097_CMD_FMUL       = 8'h03;
  localparam logic [7:0] FPU8097_CMD_FDIV       = 8'h04;
  localparam logic [7:0] FPU8097_CMD_FSQRT      = 8'h05;
  localparam logic [7:0] FPU8097_CMD_FCOM       = 8'h06;
  localparam logic [7:0] FPU8097_CMD_FCOMP      = 8'h07;
  localparam logic [7:0] FPU8097_CMD_FLD_MEM64  = 8'h08;
  localparam logic [7:0] FPU8097_CMD_FSTP_MEM64 = 8'h09;

  // CSR_8097_RF_OP encodings (P7 regfile mode)
  localparam logic [3:0] FPU8097_RFOP_MOV  = 4'h0;
  localparam logic [3:0] FPU8097_RFOP_ADD  = 4'h1;
  localparam logic [3:0] FPU8097_RFOP_MUL  = 4'h2;
  localparam logic [3:0] FPU8097_RFOP_DIV  = 4'h3;
  localparam logic [3:0] FPU8097_RFOP_SQRT = 4'h4;

  // Fault codes (implementation-defined, v1)
  localparam logic [7:0] FPU8097_FAULT_NONE            = 8'h00;
  localparam logic [7:0] FPU8097_FAULT_BAD_TIER        = 8'h01;
  localparam logic [7:0] FPU8097_FAULT_BUSY            = 8'h02;
  localparam logic [7:0] FPU8097_FAULT_STACK_UNDERFLOW = 8'h10;
  localparam logic [7:0] FPU8097_FAULT_STACK_OVERFLOW  = 8'h11;
  localparam logic [7:0] FPU8097_FAULT_ILLEGAL_CMD     = 8'h12;
  localparam logic [7:0] FPU8097_FAULT_TURBO_DENIED    = 8'h20;
  localparam logic [7:0] FPU8097_FAULT_MEM             = 8'h30;

  // x87-style status word bit positions (subset)
  localparam int unsigned FPU8097_SW_IE       = 0;   // invalid operation
  localparam int unsigned FPU8097_SW_ZE       = 2;   // divide by zero
  localparam int unsigned FPU8097_SW_OE       = 3;   // overflow
  localparam int unsigned FPU8097_SW_UE       = 4;   // underflow
  localparam int unsigned FPU8097_SW_PE       = 5;   // precision (inexact)
  localparam int unsigned FPU8097_SW_SF       = 6;   // stack fault
  localparam int unsigned FPU8097_SW_ES       = 7;   // exception summary
  localparam int unsigned FPU8097_SW_C0       = 8;
  localparam int unsigned FPU8097_SW_C1       = 9;
  localparam int unsigned FPU8097_SW_C2       = 10;
  localparam int unsigned FPU8097_SW_TOP_LSB  = 11;  // 13:11
  localparam int unsigned FPU8097_SW_C3       = 14;

endpackage : fpu_8097_pkg

