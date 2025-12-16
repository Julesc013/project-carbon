// Project Carbon - Am9513 accelerator (v1.0)
// am9513_legacy_shell: CSR-driven legacy 9511/9512 stack/command compatibility shell.

module am9513_legacy_shell (
    parameter int unsigned LEGACY_STACK_DEPTH = 16,
    input logic clk,
    input logic rst_n,

    input logic        start,
    input logic [7:0]  legacy_op,
    input logic [31:0] legacy_ctrl,

    input logic [1:0]  rm,

    input  logic [$clog2(LEGACY_STACK_DEPTH+1)-1:0] stack_depth,
    input  logic        stack_empty,
    input  logic        stack_full,
    input  logic [63:0] stack_top,

    output logic        stack_pop_we,
    output logic        stack_push_we,
    output logic [63:0] stack_push_data,

    output logic        flags_or_we,
    output logic [4:0]  flags_or_mask,

    output logic        busy,
    output logic [7:0]  last_status
);
  import carbon_arch_pkg::*;
  import am9513_pkg::*;
  import am9513_math_pkg::*;

  typedef enum logic [2:0] {
    ST_IDLE,
    ST_POP0,
    ST_POP1,
    ST_POP2,
    ST_EXEC,
    ST_PUSH
  } st_e;

  st_e st_q;

  logic [7:0] op_q;
  logic [7:0] fmt_q;

  logic [63:0] a_q;
  logic [63:0] b_q;
  logic [63:0] c_q;
  logic [63:0] res_q;
  logic [4:0]  exc_q;

  logic [7:0] status_q;

  function automatic int unsigned need_operands(input logic [7:0] op);
    unique case (op)
      AM9513_LEG_OP_SQRT: need_operands = 1;
      AM9513_LEG_OP_FMA:  need_operands = 3;
      default:            need_operands = 2;
    endcase
  endfunction

  function automatic logic [7:0] decode_fmt(input logic [31:0] ctrl);
    logic mode_p1;
    logic [3:0] fmt_field;
    begin
      mode_p1 = ctrl[0];
      fmt_field = ctrl[7:4];
      if (!mode_p1) begin
        decode_fmt = 8'(CARBON_FMT_BINARY32);
      end else begin
        // Default to fp64 when not explicitly set.
        if (fmt_field == 4'(CARBON_FMT_BINARY32)) decode_fmt = 8'(CARBON_FMT_BINARY32);
        else decode_fmt = 8'(CARBON_FMT_BINARY64);
      end
    end
  endfunction

  // Outputs
  always_comb begin
    stack_pop_we   = 1'b0;
    stack_push_we  = 1'b0;
    stack_push_data = res_q;

    flags_or_we    = 1'b0;
    flags_or_mask  = exc_q;

    busy = (st_q != ST_IDLE);
    last_status = status_q;

    unique case (st_q)
      ST_POP0: stack_pop_we = 1'b1;
      ST_POP1: stack_pop_we = 1'b1;
      ST_POP2: stack_pop_we = 1'b1;
      ST_EXEC: flags_or_we  = 1'b1;
      ST_PUSH: stack_push_we = 1'b1;
      default: begin
      end
    endcase
  end

  always_ff @(posedge clk or negedge rst_n) begin
    am9513_exec_result_t ex;
    if (!rst_n) begin
      st_q <= ST_IDLE;
      op_q <= '0;
      fmt_q <= 8'(CARBON_FMT_BINARY32);
      a_q <= '0;
      b_q <= '0;
      c_q <= '0;
      res_q <= '0;
      exc_q <= '0;
      status_q <= 8'h00;
    end else begin
      if (st_q == ST_IDLE) begin
        exc_q <= '0;
        status_q <= 8'h00;
        if (start) begin
          op_q <= legacy_op;
          fmt_q <= decode_fmt(legacy_ctrl);

          if (int'(stack_depth) < int'(need_operands(legacy_op))) begin
            status_q <= 8'h01; // underflow
            st_q <= ST_IDLE;
          end else begin
            st_q <= ST_POP0;
          end
        end
      end else begin
        unique case (st_q)
          ST_POP0: begin
            a_q <= stack_top;
            if (need_operands(op_q) == 1) st_q <= ST_EXEC;
            else st_q <= ST_POP1;
          end

          ST_POP1: begin
            b_q <= stack_top;
            if (need_operands(op_q) == 2) st_q <= ST_EXEC;
            else st_q <= ST_POP2;
          end

          ST_POP2: begin
            c_q <= stack_top;
            st_q <= ST_EXEC;
          end

          ST_EXEC: begin
            unique case (op_q)
              AM9513_LEG_OP_ADD: ex = am9513_execute(AM9513_FUNC_ADD, fmt_q, 32'h0, b_q, a_q, c_q, rm);
              AM9513_LEG_OP_MUL: ex = am9513_execute(AM9513_FUNC_MUL, fmt_q, 32'h0, b_q, a_q, c_q, rm);
              AM9513_LEG_OP_DIV: ex = am9513_execute(AM9513_FUNC_DIV, fmt_q, 32'h0, b_q, a_q, c_q, rm);
              AM9513_LEG_OP_SQRT: ex = am9513_execute(AM9513_FUNC_SQRT, fmt_q, 32'h0, a_q, b_q, c_q, rm);
              AM9513_LEG_OP_FMA: ex = am9513_execute(AM9513_FUNC_FMA, fmt_q, 32'h0, c_q, b_q, a_q, rm);
              default: ex = '{default: '0, cai_status: 16'(CARBON_CAI_STATUS_INVALID_OP)};
            endcase

            res_q <= ex.res0;
            exc_q <= ex.exc_flags;
            if (ex.cai_status != 16'(CARBON_CAI_STATUS_OK)) status_q <= 8'h02;
            st_q <= ST_PUSH;
          end

          ST_PUSH: begin
            st_q <= ST_IDLE;
          end

          default: begin
            st_q <= ST_IDLE;
          end
        endcase
      end
    end
  end

endmodule : am9513_legacy_shell
