// Project Carbon - Am9514 vector tier (v1.0)
// am9514_vector: Combinational vector execution for a single 128-bit vector element.

module am9514_vector (
    input  logic [7:0]   func,
    input  logic [7:0]   fmt,
    input  logic [7:0]   fmt_aux,
    input  logic [7:0]   fmt_flags,
    input  logic [127:0] op0,
    input  logic [127:0] op1,
    input  logic [127:0] op2,
    input  logic [15:0]  mask_bits,
    input  logic [1:0]   rm,
    output logic [127:0] result,
    output logic [4:0]   exc_flags,
    output logic [15:0]  status
);
  import carbon_arch_pkg::*;
  import am9513_pkg::*;
  import am9513_math_pkg::*;

  function automatic int unsigned lane_count(input logic [7:0] f);
    begin
      unique case (f)
        8'(CARBON_FMT_BINARY16): lane_count = 8;
        8'(CARBON_FMT_BFLOAT16): lane_count = 8;
        8'(CARBON_FMT_BINARY32): lane_count = 4;
        default: lane_count = 0;
      endcase
    end
  endfunction

  function automatic am9513_fp32_t lane_to_fp32(input logic [31:0] lane, input logic [7:0] f);
    am9513_fp32_t o;
    begin
      unique case (f)
        8'(CARBON_FMT_BINARY16): o = fp16_to_fp32(lane[15:0]);
        8'(CARBON_FMT_BFLOAT16): o = bf16_to_fp32(lane[15:0]);
        8'(CARBON_FMT_BINARY32): begin o.v = lane; o.flags = '0; end
        default: begin o.v = FP32_QNAN; o.flags = AM9513_F_NV; end
      endcase
      lane_to_fp32 = o;
    end
  endfunction

  function automatic logic [31:0] fp32_to_lane(
      input am9513_fp32_t v,
      input logic [7:0] f,
      input logic [1:0] rm_in,
      output logic [4:0] flags_out
  );
    am9513_fp32_t tmp;
    begin
      flags_out = v.flags;
      unique case (f)
        8'(CARBON_FMT_BINARY16): begin
          tmp = fp32_to_fp16(v.v, rm_in);
          flags_out |= tmp.flags;
          fp32_to_lane = {16'h0, tmp.v[15:0]};
        end
        8'(CARBON_FMT_BFLOAT16): begin
          tmp = fp32_to_bf16(v.v, rm_in);
          flags_out |= tmp.flags;
          fp32_to_lane = {16'h0, tmp.v[15:0]};
        end
        8'(CARBON_FMT_BINARY32): begin
          fp32_to_lane = v.v;
        end
        default: begin
          flags_out |= AM9513_F_NV;
          fp32_to_lane = 32'h0000_0000;
        end
      endcase
    end
  endfunction

  logic mask_en;
  assign mask_en = fmt_flags[0];

  always_comb begin
    int unsigned lanes;
    int unsigned lane;
    logic [127:0] res;
    logic [4:0] flags;
    logic [15:0] st;

    res = '0;
    flags = '0;
    st = 16'(CARBON_CAI_STATUS_OK);
    lanes = lane_count(fmt);

    if (lanes == 0) begin
      st = 16'(CARBON_CAI_STATUS_INVALID_OP);
    end else if ((func == AM9514_VEC_CONV) && (lane_count(fmt_aux) == 0)) begin
      st = 16'(CARBON_CAI_STATUS_INVALID_OP);
    end else begin
      for (lane = 0; lane < lanes; lane++) begin
        logic [4:0] lane_flags;
        logic [31:0] a_lane;
        logic [31:0] b_lane;
        logic [31:0] c_lane;
        logic [31:0] out_lane;
        am9513_fp32_t a32;
        am9513_fp32_t b32;
        am9513_fp32_t c32;
        am9513_fp32_t r32;
        am9513_fp32_t t32;
        int signed cmp;
        logic apply_mask;

        lane_flags = '0;
        out_lane = 32'h0;

        if (fmt == 8'(CARBON_FMT_BINARY32)) begin
          a_lane = op0[(lane*32) +: 32];
          b_lane = op1[(lane*32) +: 32];
          c_lane = op2[(lane*32) +: 32];
        end else begin
          a_lane = {16'h0, op0[(lane*16) +: 16]};
          b_lane = {16'h0, op1[(lane*16) +: 16]};
          c_lane = {16'h0, op2[(lane*16) +: 16]};
        end

        apply_mask = mask_en && (mask_bits[lane] == 1'b0);
        if (apply_mask) begin
          out_lane = a_lane;
        end else begin
          unique case (func)
            AM9514_VEC_SHUF_SWAP: begin
              int unsigned src;
              src = lane ^ 1;
              if (fmt == 8'(CARBON_FMT_BINARY32)) begin
                out_lane = op0[(src*32) +: 32];
              end else begin
                out_lane = {16'h0, op0[(src*16) +: 16]};
              end
            end

            AM9514_VEC_SHUF_BCAST: begin
              if (fmt == 8'(CARBON_FMT_BINARY32)) begin
                out_lane = op0[0 +: 32];
              end else begin
                out_lane = {16'h0, op0[0 +: 16]};
              end
            end

            AM9514_VEC_CONV: begin
              a32 = lane_to_fp32(a_lane, fmt_aux);
              lane_flags |= a32.flags;
              out_lane = fp32_to_lane(a32, fmt, rm, lane_flags);
            end

            default: begin
              a32 = lane_to_fp32(a_lane, fmt);
              b32 = lane_to_fp32(b_lane, fmt);
              c32 = lane_to_fp32(c_lane, fmt);
              lane_flags |= a32.flags | b32.flags | c32.flags;

              unique case (func)
                AM9514_VEC_ADD: r32 = fp32_add(a32.v, b32.v, rm);
                AM9514_VEC_SUB: r32 = fp32_sub(a32.v, b32.v, rm);
                AM9514_VEC_MUL: r32 = fp32_mul(a32.v, b32.v, rm);
                AM9514_VEC_FMA: r32 = fp32_fma(a32.v, b32.v, c32.v, rm);
                AM9514_VEC_MIN: begin
                  r32.v = ($signed(a32.v) < $signed(b32.v)) ? a32.v : b32.v;
                  r32.flags = '0;
                end
                AM9514_VEC_MAX: begin
                  r32.v = ($signed(a32.v) > $signed(b32.v)) ? a32.v : b32.v;
                  r32.flags = '0;
                end
                AM9514_VEC_CMP: begin
                  if (((a32.v[30:23] == 8'hFF) && (a32.v[22:0] != 0)) ||
                      ((b32.v[30:23] == 8'hFF) && (b32.v[22:0] != 0))) begin
                    lane_flags |= AM9513_F_NV;
                    cmp = 0;
                  end else if (a32.v == b32.v) begin
                    cmp = 0;
                  end else if ($signed(a32.v) < $signed(b32.v)) begin
                    cmp = -1;
                  end else begin
                    cmp = 1;
                  end
                  if (cmp == 0) out_lane = 32'hFFFF_FFFF;
                  else out_lane = 32'h0000_0000;
                  r32.v = out_lane;
                  r32.flags = '0;
                end
                default: begin
                  r32.v = 32'h0;
                  r32.flags = '0;
                  st = 16'(CARBON_CAI_STATUS_INVALID_OP);
                end
              endcase

              if ((func != AM9514_VEC_CMP) && (st == 16'(CARBON_CAI_STATUS_OK))) begin
                lane_flags |= r32.flags;
                out_lane = fp32_to_lane(r32, fmt, rm, lane_flags);
              end
            end
          endcase
        end

        flags |= lane_flags;
        if (fmt == 8'(CARBON_FMT_BINARY32)) begin
          res[(lane*32) +: 32] = out_lane;
        end else begin
          res[(lane*16) +: 16] = out_lane[15:0];
        end
      end
    end

    result = res;
    exc_flags = flags;
    status = st;
  end

endmodule : am9514_vector
