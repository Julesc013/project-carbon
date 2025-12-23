// Project Carbon - Am9511 compatibility tier (v1.0)
// am9511_compat: Restricted scalar subset for P0 behavior.

module am9511_compat (
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

  always_comb begin
    result = '0;
    result.cai_status = 16'(CARBON_CAI_STATUS_OK);

    if (fmt != 8'(CARBON_FMT_BINARY32)) begin
      result.cai_status = 16'(CARBON_CAI_STATUS_INVALID_OP);
    end else begin
      unique case (func)
        AM9513_FUNC_ADD,
        AM9513_FUNC_SUB,
        AM9513_FUNC_MUL,
        AM9513_FUNC_DIV,
        AM9513_FUNC_SQRT,
        AM9513_FUNC_FMA,
        AM9513_FUNC_SIN: begin
          result = am9513_execute(func, fmt, flags, op0, op1, op2, rm);
        end
        default: begin
          result.cai_status = 16'(CARBON_CAI_STATUS_INVALID_OP);
        end
      endcase
    end
  end

endmodule : am9511_compat
