// Project Carbon - Am9513 scalar tier (v1.0)
// am9513_scalar: Full P2 scalar execution wrapper.

module am9513_scalar (
    input  logic [7:0]  func,
    input  logic [7:0]  fmt,
    input  logic [31:0] flags,
    input  logic [63:0] op0,
    input  logic [63:0] op1,
    input  logic [63:0] op2,
    input  logic [1:0]  rm,
    output am9513_math_pkg::am9513_exec_result_t result
);
  import am9513_math_pkg::*;

  always_comb begin
    result = am9513_execute(func, fmt, flags, op0, op1, op2, rm);
  end

endmodule : am9513_scalar
