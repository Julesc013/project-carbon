// Project Carbon - Am9512 compatibility tier (v1.0)
// am9512_compat: IEEE-focused scalar subset for P1 behavior.

module am9512_compat (
    input  logic [7:0]  func,
    input  logic [7:0]  fmt,
    input  logic [31:0] flags,
    input  logic [63:0] op0,
    input  logic [63:0] op1,
    input  logic [63:0] op2,
    input  logic [1:0]  rm,
    output am9513_math_pkg::am9513_exec_result_t result
);
  import carbon_arch_pkg::*;
  import am9513_pkg::*;
  import am9513_math_pkg::*;

  logic fmt_ok;
  logic src_ok;
  logic [7:0] src_fmt;

  always_comb begin
    result = '0;
    result.cai_status = 16'(CARBON_CAI_STATUS_OK);
    src_fmt = flags[AM9513_SUBMIT_FLAG_CONV_SRC_FMT_LSB +: AM9513_SUBMIT_FLAG_CONV_SRC_FMT_WIDTH];

    fmt_ok = (fmt == 8'(CARBON_FMT_BINARY32)) || (fmt == 8'(CARBON_FMT_BINARY64));
    src_ok = (src_fmt == 8'(CARBON_FMT_BINARY32)) || (src_fmt == 8'(CARBON_FMT_BINARY64));

    if (!fmt_ok) begin
      result.cai_status = 16'(CARBON_CAI_STATUS_INVALID_OP);
    end else if ((func == AM9513_FUNC_CONV) && !src_ok) begin
      result.cai_status = 16'(CARBON_CAI_STATUS_INVALID_OP);
    end else begin
      result = am9513_execute(func, fmt, flags, op0, op1, op2, rm);
    end
  end

endmodule : am9512_compat
