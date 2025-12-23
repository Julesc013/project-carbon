// Project Carbon - Am9515 tensor tier (v1.0)
// am9515_tensor: Combinational scalar MAC/reduction helper for tensor ops.

module am9515_tensor (
    input  logic [7:0]  func,
    input  logic [7:0]  fmt,
    input  logic [63:0] a,
    input  logic [63:0] b,
    input  logic [63:0] acc,
    input  logic [1:0]  rm,
    output logic [63:0] result,
    output logic [4:0]  exc_flags,
    output logic [15:0] status
);
  import carbon_arch_pkg::*;
  import am9513_pkg::*;
  import am9513_math_pkg::*;

  always_comb begin
    am9513_fp32_t a32;
    am9513_fp32_t b32;
    am9513_fp32_t acc32;
    am9513_fp32_t mul32;
    am9513_fp32_t sum32;

    result = acc;
    exc_flags = '0;
    status = 16'(CARBON_CAI_STATUS_OK);

    if ((fmt != 8'(CARBON_FMT_BINARY16)) &&
        (fmt != 8'(CARBON_FMT_BFLOAT16)) &&
        (fmt != 8'(CARBON_FMT_BINARY32))) begin
      status = 16'(CARBON_CAI_STATUS_INVALID_OP);
    end else begin
      // Convert inputs to fp32 for accumulation.
      acc32.v = acc[31:0];
      acc32.flags = '0;
      if (fmt == 8'(CARBON_FMT_BINARY32)) begin
        a32.v = a[31:0]; a32.flags = '0;
        b32.v = b[31:0]; b32.flags = '0;
      end else if (fmt == 8'(CARBON_FMT_BINARY16)) begin
        a32 = fp16_to_fp32(a[15:0]);
        b32 = fp16_to_fp32(b[15:0]);
      end else begin
        a32 = bf16_to_fp32(a[15:0]);
        b32 = bf16_to_fp32(b[15:0]);
      end

      exc_flags |= a32.flags | b32.flags;

      unique case (func)
        AM9515_TENSOR_GEMM,
        AM9515_TENSOR_DOT: begin
          mul32 = fp32_mul(a32.v, b32.v, rm);
          sum32 = fp32_add(acc32.v, mul32.v, rm);
          exc_flags |= mul32.flags | sum32.flags;
          result = {32'h0, sum32.v};
        end

        AM9515_TENSOR_SUM: begin
          sum32 = fp32_add(acc32.v, a32.v, rm);
          exc_flags |= sum32.flags;
          result = {32'h0, sum32.v};
        end

        default: begin
          status = 16'(CARBON_CAI_STATUS_INVALID_OP);
        end
      endcase
    end
  end

endmodule : am9515_tensor
