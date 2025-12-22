// Project Carbon - Z85 core (strict Z80 engine)
// z85_flags: Centralized flag and ALU helper functions.
//
// Notes:
// - This package targets "real Z80" style flags including undocumented X/Y bits.
// - For complex undocumented flag behaviors in some block ops, this package
//   provides primitives; instruction-level glue lives in the executor/core.

package z85_flags_pkg;
  import z85_regfile_pkg::*;

  typedef struct packed {
    logic [7:0] res;
    logic [7:0] f;
  } z85_alu8_t;

  typedef struct packed {
    logic [15:0] res;
    logic [7:0]  f;
  } z85_alu16_t;

  function automatic logic parity_even(input logic [7:0] v);
    return ~^v;
  endfunction

  function automatic logic [7:0] xy_from8(input logic [7:0] v);
    return v & (Z85_F_X | Z85_F_Y);
  endfunction

  function automatic logic [7:0] flags_sz_xy(input logic [7:0] v);
    logic [7:0] f;
    begin
      f = 8'h00;
      if (v[7]) f |= Z85_F_S;
      if (v == 8'h00) f |= Z85_F_Z;
      f |= xy_from8(v);
      flags_sz_xy = f;
    end
  endfunction

  function automatic logic [7:0] flags_szp_xy(input logic [7:0] v);
    logic [7:0] f;
    begin
      f = 8'h00;
      if (v[7]) f |= Z85_F_S;
      if (v == 8'h00) f |= Z85_F_Z;
      if (parity_even(v)) f |= Z85_F_PV;
      f |= xy_from8(v);
      flags_szp_xy = f;
    end
  endfunction

  function automatic logic [7:0] flags_szp_xy16_hi(input logic [15:0] v);
    return flags_szp_xy(v[15:8]) & (Z85_F_S | Z85_F_Z | Z85_F_PV | Z85_F_X | Z85_F_Y);
  endfunction

  function automatic logic ov_add8(input logic [7:0] a, input logic [7:0] b, input logic [7:0] r);
    return (((~(a ^ b)) & (a ^ r)) & 8'h80) != 0;
  endfunction

  function automatic logic ov_sub8(input logic [7:0] a, input logic [7:0] b, input logic [7:0] r);
    return (((a ^ b) & (a ^ r)) & 8'h80) != 0;
  endfunction

  function automatic logic ov_add16(input logic [15:0] a, input logic [15:0] b, input logic [15:0] r);
    return (((~(a ^ b)) & (a ^ r)) & 16'h8000) != 0;
  endfunction

  function automatic logic ov_sub16(input logic [15:0] a, input logic [15:0] b, input logic [15:0] r);
    return (((a ^ b) & (a ^ r)) & 16'h8000) != 0;
  endfunction

  function automatic z85_alu8_t alu_add8(input logic [7:0] a, input logic [7:0] b);
    logic [8:0] sum;
    z85_alu8_t o;
    begin
      sum = {1'b0, a} + {1'b0, b};
      o.res = sum[7:0];
      o.f   = flags_sz_xy(o.res);
      if ((((a & 8'h0F) + (b & 8'h0F)) & 8'h10) != 0) o.f |= Z85_F_H;
      if (ov_add8(a, b, o.res)) o.f |= Z85_F_PV;
      if (sum[8]) o.f |= Z85_F_C;
      // N=0
      alu_add8 = o;
    end
  endfunction

  function automatic z85_alu8_t alu_adc8(input logic [7:0] a, input logic [7:0] b, input logic cin);
    logic [8:0] sum;
    z85_alu8_t o;
    logic [7:0] b2;
    begin
      b2  = b;
      sum = {1'b0, a} + {1'b0, b2} + {8'h00, cin};
      o.res = sum[7:0];
      o.f   = flags_sz_xy(o.res);
      if (((a[3:0] + b2[3:0] + cin) & 5'h10) != 0) o.f |= Z85_F_H;
      if (ov_add8(a, b2, o.res)) o.f |= Z85_F_PV;
      if (sum[8]) o.f |= Z85_F_C;
      alu_adc8 = o;
    end
  endfunction

  function automatic z85_alu8_t alu_sub8(input logic [7:0] a, input logic [7:0] b);
    logic [8:0] diff;
    z85_alu8_t o;
    begin
      diff = {1'b0, a} - {1'b0, b};
      o.res = diff[7:0];
      o.f   = flags_sz_xy(o.res);
      if ((a[3:0] < b[3:0])) o.f |= Z85_F_H;
      if (ov_sub8(a, b, o.res)) o.f |= Z85_F_PV;
      o.f |= Z85_F_N;
      if (diff[8]) o.f |= Z85_F_C;
      alu_sub8 = o;
    end
  endfunction

  function automatic z85_alu8_t alu_sbc8(input logic [7:0] a, input logic [7:0] b, input logic cin);
    logic [8:0] diff;
    z85_alu8_t o;
    logic [8:0] bcin;
    begin
      bcin = {1'b0, b} + {8'h00, cin};
      diff = {1'b0, a} - bcin;
      o.res = diff[7:0];
      o.f   = flags_sz_xy(o.res);
      if ({1'b0, a[3:0]} < {1'b0, b[3:0]} + cin) o.f |= Z85_F_H;
      if (ov_sub8(a, b[7:0] + {7'h00, cin}, o.res)) o.f |= Z85_F_PV;
      o.f |= Z85_F_N;
      if (diff[8]) o.f |= Z85_F_C;
      alu_sbc8 = o;
    end
  endfunction

  function automatic z85_alu8_t alu_and8(input logic [7:0] a, input logic [7:0] b);
    z85_alu8_t o;
    begin
      o.res = a & b;
      o.f   = flags_szp_xy(o.res);
      o.f  |= Z85_F_H;
      // N=0, C=0
      alu_and8 = o;
    end
  endfunction

  function automatic z85_alu8_t alu_xor8(input logic [7:0] a, input logic [7:0] b);
    z85_alu8_t o;
    begin
      o.res = a ^ b;
      o.f   = flags_szp_xy(o.res);
      alu_xor8 = o;
    end
  endfunction

  function automatic z85_alu8_t alu_or8(input logic [7:0] a, input logic [7:0] b);
    z85_alu8_t o;
    begin
      o.res = a | b;
      o.f   = flags_szp_xy(o.res);
      alu_or8 = o;
    end
  endfunction

  function automatic z85_alu8_t alu_cp8(input logic [7:0] a, input logic [7:0] b, input logic [7:0] f_in);
    z85_alu8_t o;
    z85_alu8_t sub;
    begin
      sub = alu_sub8(a, b);
      o.res = sub.res;
      o.f   = (sub.f & ~xy_from8(sub.res)) | xy_from8(sub.res);
      // CP preserves result only for flags; carry/half/overflow from subtract.
      // Carry already in sub.f; match Z80: bits 3/5 from result of (A-B).
      alu_cp8 = o;
    end
  endfunction

  function automatic z85_alu8_t alu_inc8(input logic [7:0] v, input logic [7:0] f_in);
    z85_alu8_t o;
    begin
      o.res = v + 8'd1;
      o.f   = (f_in & Z85_F_C);
      o.f  |= (flags_sz_xy(o.res) & (Z85_F_S | Z85_F_Z | Z85_F_X | Z85_F_Y));
      if ((v[3:0] == 4'hF)) o.f |= Z85_F_H;
      if (v == 8'h7F) o.f |= Z85_F_PV;
      // N=0
      alu_inc8 = o;
    end
  endfunction

  function automatic z85_alu8_t alu_dec8(input logic [7:0] v, input logic [7:0] f_in);
    z85_alu8_t o;
    begin
      o.res = v - 8'd1;
      o.f   = (f_in & Z85_F_C);
      o.f  |= (flags_sz_xy(o.res) & (Z85_F_S | Z85_F_Z | Z85_F_X | Z85_F_Y));
      if ((v[3:0] == 4'h0)) o.f |= Z85_F_H;
      if (v == 8'h80) o.f |= Z85_F_PV;
      o.f |= Z85_F_N;
      alu_dec8 = o;
    end
  endfunction

  function automatic z85_alu8_t alu_daa(input logic [7:0] a, input logic [7:0] f_in);
    z85_alu8_t o;
    logic n, c, h;
    logic [7:0] adj;
    logic c_out;
    logic [7:0] a_out;
    begin
      n = (f_in & Z85_F_N) != 0;
      c = (f_in & Z85_F_C) != 0;
      h = (f_in & Z85_F_H) != 0;
      adj = 8'h00;
      c_out = c;

      if (!n) begin
        if (h || ((a & 8'h0F) > 8'h09)) adj |= 8'h06;
        if (c || (a > 8'h99)) begin
          adj |= 8'h60;
          c_out = 1'b1;
        end
        a_out = a + adj;
      end else begin
        if (h) adj |= 8'h06;
        if (c) adj |= 8'h60;
        a_out = a - adj;
      end

      o.res = a_out;
      o.f   = 8'h00;
      o.f  |= flags_szp_xy(o.res) & (Z85_F_S | Z85_F_Z | Z85_F_PV | Z85_F_X | Z85_F_Y);
      if (n) o.f |= Z85_F_N;
      if ((((a ^ o.res) & 8'h10) != 0)) o.f |= Z85_F_H;
      if (c_out) o.f |= Z85_F_C;
      alu_daa = o;
    end
  endfunction

  function automatic logic [7:0] flags_rlca_rrca_rla_rra(
      input logic [7:0] f_in,
      input logic [7:0] a_new,
      input logic c_new
  );
    logic [7:0] f;
    begin
      f = f_in & (Z85_F_S | Z85_F_Z | Z85_F_PV);
      f |= xy_from8(a_new);
      if (c_new) f |= Z85_F_C;
      // H=0, N=0
      flags_rlca_rrca_rla_rra = f;
    end
  endfunction

  function automatic logic [7:0] flags_scf(input logic [7:0] f_in, input logic [7:0] a);
    logic [7:0] f;
    begin
      f = f_in & (Z85_F_S | Z85_F_Z | Z85_F_PV);
      f |= xy_from8(a);
      f |= Z85_F_C;
      flags_scf = f;
    end
  endfunction

  function automatic logic [7:0] flags_ccf(input logic [7:0] f_in, input logic [7:0] a);
    logic [7:0] f;
    logic c;
    begin
      c = (f_in & Z85_F_C) != 0;
      f = f_in & (Z85_F_S | Z85_F_Z | Z85_F_PV);
      f |= xy_from8(a);
      if (!c) f |= Z85_F_C;
      if (c) f |= Z85_F_H; // H = old C
      flags_ccf = f;
    end
  endfunction

  function automatic logic [7:0] flags_cpl(input logic [7:0] f_in, input logic [7:0] a_new);
    logic [7:0] f;
    begin
      f = f_in & (Z85_F_S | Z85_F_Z | Z85_F_PV | Z85_F_C);
      f |= xy_from8(a_new);
      f |= (Z85_F_H | Z85_F_N);
      flags_cpl = f;
    end
  endfunction

  function automatic z85_alu8_t alu_in8_flags(input logic [7:0] in_v, input logic [7:0] f_in);
    z85_alu8_t o;
    begin
      o.res = in_v;
      o.f   = (f_in & Z85_F_C);
      o.f  |= flags_szp_xy(in_v) & (Z85_F_S | Z85_F_Z | Z85_F_PV | Z85_F_X | Z85_F_Y);
      // H=0, N=0
      alu_in8_flags = o;
    end
  endfunction

  function automatic z85_alu8_t alu_neg(input logic [7:0] a, input logic [7:0] f_in);
    z85_alu8_t o;
    begin
      o = alu_sub8(8'h00, a);
      // NEG sets N, and uses normal SUB flags; carry set if a != 0.
      alu_neg = o;
    end
  endfunction

  function automatic z85_alu16_t alu_add16_hl(input logic [15:0] hl, input logic [15:0] rr, input logic [7:0] f_in);
    logic [16:0] sum;
    z85_alu16_t o;
    logic [15:0] r;
    begin
      sum  = {1'b0, hl} + {1'b0, rr};
      r    = sum[15:0];
      o.res = r;
      o.f   = f_in & (Z85_F_S | Z85_F_Z | Z85_F_PV);
      o.f  |= xy_from8(r[15:8]);
      if (((hl[11:0] + rr[11:0]) & 12'h1000) != 0) o.f |= Z85_F_H;
      if (sum[16]) o.f |= Z85_F_C;
      // N=0
      alu_add16_hl = o;
    end
  endfunction

  function automatic z85_alu16_t alu_adc16_hl(input logic [15:0] hl, input logic [15:0] rr, input logic cin);
    logic [16:0] sum;
    z85_alu16_t o;
    logic [15:0] r;
    begin
      sum  = {1'b0, hl} + {1'b0, rr} + {16'h0000, cin};
      r    = sum[15:0];
      o.res = r;
      o.f   = 8'h00;
      if (r[15]) o.f |= Z85_F_S;
      if (r == 16'h0000) o.f |= Z85_F_Z;
      if (ov_add16(hl, rr, r)) o.f |= Z85_F_PV;
      o.f |= xy_from8(r[15:8]);
      if (((hl[11:0] + rr[11:0] + cin) & 13'h1000) != 0) o.f |= Z85_F_H;
      if (sum[16]) o.f |= Z85_F_C;
      // N=0
      alu_adc16_hl = o;
    end
  endfunction

  function automatic z85_alu16_t alu_sbc16_hl(input logic [15:0] hl, input logic [15:0] rr, input logic cin);
    logic [16:0] diff;
    z85_alu16_t o;
    logic [15:0] r;
    begin
      diff = {1'b0, hl} - ({1'b0, rr} + {16'h0000, cin});
      r    = diff[15:0];
      o.res = r;
      o.f   = 8'h00;
      if (r[15]) o.f |= Z85_F_S;
      if (r == 16'h0000) o.f |= Z85_F_Z;
      if (ov_sub16(hl, rr, r)) o.f |= Z85_F_PV;
      o.f |= xy_from8(r[15:8]);
      if ({1'b0, hl[11:0]} < {1'b0, rr[11:0]} + cin) o.f |= Z85_F_H;
      o.f |= Z85_F_N;
      if (diff[16]) o.f |= Z85_F_C;
      alu_sbc16_hl = o;
    end
  endfunction

  function automatic z85_alu8_t alu_rotshift(input logic [2:0] op, input logic [7:0] v, input logic [7:0] f_in);
    z85_alu8_t o;
    logic c_in;
    logic c_out;
    begin
      c_in = (f_in & Z85_F_C) != 0;
      c_out = 1'b0;
      o.res = v;
      unique case (op)
        3'd0: begin // RLC
          c_out = v[7];
          o.res = {v[6:0], v[7]};
        end
        3'd1: begin // RRC
          c_out = v[0];
          o.res = {v[0], v[7:1]};
        end
        3'd2: begin // RL
          c_out = v[7];
          o.res = {v[6:0], c_in};
        end
        3'd3: begin // RR
          c_out = v[0];
          o.res = {c_in, v[7:1]};
        end
        3'd4: begin // SLA
          c_out = v[7];
          o.res = {v[6:0], 1'b0};
        end
        3'd5: begin // SRA
          c_out = v[0];
          o.res = {v[7], v[7:1]};
        end
        3'd6: begin // SLL (undocumented): shift left, bit0 set
          c_out = v[7];
          o.res = {v[6:0], 1'b1};
        end
        default: begin // SRL
          c_out = v[0];
          o.res = {1'b0, v[7:1]};
        end
      endcase

      o.f = flags_szp_xy(o.res);
      if (c_out) o.f |= Z85_F_C;
      // H=0, N=0
      alu_rotshift = o;
    end
  endfunction

  function automatic logic [7:0] flags_bitop(
      input int unsigned bit_index,
      input logic [7:0] operand,
      input logic [7:0] f_in,
      input logic [7:0] xy_src
  );
    logic bit_set;
    logic [7:0] f;
    begin
      bit_set = operand[bit_index[2:0]];
      f = (f_in & Z85_F_C); // preserve carry
      f |= Z85_F_H;
      // N=0
      if (!bit_set) begin
        f |= Z85_F_Z;
        f |= Z85_F_PV;
      end else begin
        if (bit_index == 7) f |= Z85_F_S;
      end
      f |= (xy_src & (Z85_F_X | Z85_F_Y));
      flags_bitop = f;
    end
  endfunction

  function automatic logic [7:0] flags_ld_block(
      input logic [7:0] f_in,
      input logic [7:0] a,
      input logic [7:0] v,
      input logic [15:0] bc_after
  );
    logic [7:0] f;
    logic [7:0] sum;
    begin
      sum = a + v;
      f = f_in & (Z85_F_S | Z85_F_Z | Z85_F_C);
      f |= sum & (Z85_F_X | Z85_F_Y);
      if (bc_after != 0) f |= Z85_F_PV;
      // H=0, N=0
      flags_ld_block = f;
    end
  endfunction

  function automatic logic [7:0] flags_cp_block(
      input logic [7:0] f_in,
      input logic [7:0] a,
      input logic [7:0] v,
      input logic [15:0] bc_after
  );
    logic [7:0] f;
    logic [7:0] res;
    logic h;
    logic [7:0] adj;
    begin
      res = a - v;
      h = (a[3:0] < v[3:0]);
      adj = res - (h ? 8'd1 : 8'd0);
      f = f_in & Z85_F_C;
      f |= Z85_F_N;
      if (res[7]) f |= Z85_F_S;
      if (res == 8'h00) f |= Z85_F_Z;
      if (h) f |= Z85_F_H;
      if (bc_after != 0) f |= Z85_F_PV;
      f |= adj & (Z85_F_X | Z85_F_Y);
      flags_cp_block = f;
    end
  endfunction

  function automatic logic [7:0] flags_block_io(
      input logic [7:0] val,
      input logic [7:0] b_after,
      input logic [7:0] c,
      input logic [7:0] l_after,
      input logic       is_in,
      input logic       inc_dir
  );
    logic [7:0] f;
    logic [7:0] tmp;
    logic [8:0] sum;
    begin
      if (is_in) begin
        tmp = inc_dir ? (c + 8'd1) : (c - 8'd1);
      end else begin
        tmp = l_after;
      end
      sum = {1'b0, val} + {1'b0, tmp};
      f = 8'h00;
      f |= b_after & (Z85_F_S | Z85_F_X | Z85_F_Y);
      if (b_after == 8'h00) f |= Z85_F_Z;
      if (sum[8]) f |= (Z85_F_H | Z85_F_C);
      if (parity_even((sum[7:0] & 8'h07) ^ b_after)) f |= Z85_F_PV;
      f |= Z85_F_N;
      flags_block_io = f;
    end
  endfunction

endpackage : z85_flags_pkg
