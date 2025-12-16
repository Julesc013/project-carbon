// Project Carbon - Am9513 accelerator (v1.0)
// am9513_math_pkg: Synthesizable numeric helpers (v1 bounded-accuracy policy).

package am9513_math_pkg;
  import carbon_arch_pkg::*;
  import am9513_pkg::*;

  typedef struct packed {
    logic [31:0] v;
    logic [4:0]  flags;
  } am9513_fp32_t;

  typedef struct packed {
    logic [63:0] v;
    logic [4:0]  flags;
  } am9513_fp64_t;

  typedef struct packed {
    logic [31:0] v;
    logic [4:0]  flags;
  } am9513_i32_t;

  typedef struct packed {
    logic [63:0] v;
    logic [4:0]  flags;
  } am9513_i64_t;

  typedef struct packed {
    logic [23:0] mant;
    logic        carry;
    logic        nx;
  } am9513_round24_t;

  typedef struct packed {
    logic [52:0] mant;
    logic        carry;
    logic        nx;
  } am9513_round53_t;

  typedef struct packed {
    logic [63:0] res0;
    logic [63:0] res1;
    logic        res1_valid;
    logic [4:0]  exc_flags;
    logic [15:0] cai_status;
    logic [31:0] bytes_written;
  } am9513_exec_result_t;

  localparam logic [31:0] FP32_QNAN = 32'h7FC0_0000;
  localparam logic [63:0] FP64_QNAN = 64'h7FF8_0000_0000_0000;

  localparam logic [31:0] FP32_POS_INF = 32'h7F80_0000;
  localparam logic [31:0] FP32_NEG_INF = 32'hFF80_0000;
  localparam logic [63:0] FP64_POS_INF = 64'h7FF0_0000_0000_0000;
  localparam logic [63:0] FP64_NEG_INF = 64'hFFF0_0000_0000_0000;

  // --------------------------------------------------------------------------
  // Small helpers
  // --------------------------------------------------------------------------
  function automatic logic [26:0] shr_sticky27(input logic [26:0] v, input int unsigned shamt);
    logic sticky;
    logic [26:0] r;
    begin
      if (shamt == 0) begin
        shr_sticky27 = v;
      end else if (shamt >= 27) begin
        shr_sticky27 = {26'b0, (|v)};
      end else begin
        sticky = |v[shamt-1:0];
        r = v >> shamt;
        r[0] |= sticky;
        shr_sticky27 = r;
      end
    end
  endfunction

  function automatic logic [55:0] shr_sticky56(input logic [55:0] v, input int unsigned shamt);
    logic sticky;
    logic [55:0] r;
    begin
      if (shamt == 0) begin
        shr_sticky56 = v;
      end else if (shamt >= 56) begin
        shr_sticky56 = {55'b0, (|v)};
      end else begin
        sticky = |v[shamt-1:0];
        r = v >> shamt;
        r[0] |= sticky;
        shr_sticky56 = r;
      end
    end
  endfunction

  function automatic am9513_round24_t round24(
      input logic sign,
      input logic [26:0] mant_grs,
      input logic [1:0] rm
  );
    am9513_round24_t o;
    logic guard;
    logic roundb;
    logic sticky;
    logic any;
    logic lsb;
    logic inc;
    logic [24:0] sum;
    begin
      guard  = mant_grs[2];
      roundb = mant_grs[1];
      sticky = mant_grs[0];
      any    = guard | roundb | sticky;
      lsb    = mant_grs[3];

      unique case (rm)
        2'(CARBON_RND_RZ): inc = 1'b0;
        2'(CARBON_RND_RP): inc = (!sign) && any;
        2'(CARBON_RND_RM): inc = (sign) && any;
        default: inc = guard && (roundb || sticky || lsb); // RN (ties-to-even)
      endcase

      sum = {1'b0, mant_grs[26:3]} + 25'(inc);
      o.carry = sum[24];
      o.mant  = sum[23:0];
      o.nx    = any;
      round24 = o;
    end
  endfunction

  function automatic am9513_round53_t round53(
      input logic sign,
      input logic [55:0] mant_grs,
      input logic [1:0] rm
  );
    am9513_round53_t o;
    logic guard;
    logic roundb;
    logic sticky;
    logic any;
    logic lsb;
    logic inc;
    logic [53:0] sum;
    begin
      guard  = mant_grs[2];
      roundb = mant_grs[1];
      sticky = mant_grs[0];
      any    = guard | roundb | sticky;
      lsb    = mant_grs[3];

      unique case (rm)
        2'(CARBON_RND_RZ): inc = 1'b0;
        2'(CARBON_RND_RP): inc = (!sign) && any;
        2'(CARBON_RND_RM): inc = (sign) && any;
        default: inc = guard && (roundb || sticky || lsb); // RN
      endcase

      sum = {1'b0, mant_grs[55:3]} + 54'(inc);
      o.carry = sum[53];
      o.mant  = sum[52:0];
      o.nx    = any;
      round53 = o;
    end
  endfunction

  // --------------------------------------------------------------------------
  // Integer square root (binary method), returning remainder-nonzero for NX.
  // --------------------------------------------------------------------------
  typedef struct packed {
    logic [23:0] root;
    logic        rem_nonzero;
  } am9513_isqrt48_t;

  typedef struct packed {
    logic [52:0] root;
    logic        rem_nonzero;
  } am9513_isqrt106_t;

  function automatic am9513_isqrt48_t isqrt48(input logic [47:0] n_in);
    am9513_isqrt48_t o;
    logic [47:0] n;
    logic [47:0] res;
    logic [47:0] bit;
    int i;
    begin
      n = n_in;
      res = '0;
      bit = 48'h1 << 46; // highest power-of-four candidate within 48 bits

      for (i = 0; i < 24; i++) begin
        if (bit > n) bit = bit >> 2;
      end

      while (bit != 0) begin
        if (n >= (res + bit)) begin
          n = n - (res + bit);
          res = (res >> 1) + bit;
        end else begin
          res = (res >> 1);
        end
        bit = bit >> 2;
      end

      o.root = res[23:0];
      o.rem_nonzero = (n != 0);
      isqrt48 = o;
    end
  endfunction

  function automatic am9513_isqrt106_t isqrt106(input logic [105:0] n_in);
    am9513_isqrt106_t o;
    logic [105:0] n;
    logic [105:0] res;
    logic [105:0] bit;
    int i;
    begin
      n = n_in;
      res = '0;
      bit = 106'h1 << 104; // highest power-of-four candidate within 106 bits

      for (i = 0; i < 53; i++) begin
        if (bit > n) bit = bit >> 2;
      end

      while (bit != 0) begin
        if (n >= (res + bit)) begin
          n = n - (res + bit);
          res = (res >> 1) + bit;
        end else begin
          res = (res >> 1);
        end
        bit = bit >> 2;
      end

      o.root = res[52:0];
      o.rem_nonzero = (n != 0);
      isqrt106 = o;
    end
  endfunction

  // --------------------------------------------------------------------------
  // FP32 core ops (flush subnormals to zero; deterministic subset)
  // --------------------------------------------------------------------------
  function automatic am9513_fp32_t fp32_add(input logic [31:0] a, input logic [31:0] b, input logic [1:0] rm);
    am9513_fp32_t o;
    logic sa, sb, sr;
    logic [7:0] ea, eb, er;
    logic [22:0] fa, fb;
    logic za, zb, ia, ib, na, nb;
    logic [23:0] ma, mb;
    logic [26:0] ma_ext, mb_ext, mb_sh;
    logic [27:0] sum;
    logic [26:0] mant;
    am9513_round24_t r;
    int unsigned sh;
    begin
      o.v = '0;
      o.flags = '0;

      sa = a[31]; ea = a[30:23]; fa = a[22:0];
      sb = b[31]; eb = b[30:23]; fb = b[22:0];

      za = (ea == 8'h00) && (fa == 23'h0);
      zb = (eb == 8'h00) && (fb == 23'h0);
      ia = (ea == 8'hFF) && (fa == 23'h0);
      ib = (eb == 8'hFF) && (fb == 23'h0);
      na = (ea == 8'hFF) && (fa != 23'h0);
      nb = (eb == 8'hFF) && (fb != 23'h0);

      if (na || nb) begin
        o.v = FP32_QNAN;
        fp32_add = o;
        return;
      end

      if (ia && ib && (sa != sb)) begin
        o.v = FP32_QNAN;
        o.flags |= AM9513_F_NV;
        fp32_add = o;
        return;
      end

      if (ia) begin
        o.v = sa ? FP32_NEG_INF : FP32_POS_INF;
        fp32_add = o;
        return;
      end

      if (ib) begin
        o.v = sb ? FP32_NEG_INF : FP32_POS_INF;
        fp32_add = o;
        return;
      end

      if (za && zb) begin
        o.v = 32'h0000_0000;
        fp32_add = o;
        return;
      end

      if (za) begin
        o.v = b;
        fp32_add = o;
        return;
      end

      if (zb) begin
        o.v = a;
        fp32_add = o;
        return;
      end

      // Flush subnormals to zero (v1 policy).
      if (ea == 8'h00) begin
        o.v = b;
        o.flags |= AM9513_F_UF;
        fp32_add = o;
        return;
      end
      if (eb == 8'h00) begin
        o.v = a;
        o.flags |= AM9513_F_UF;
        fp32_add = o;
        return;
      end

      ma = {1'b1, fa};
      mb = {1'b1, fb};

      // Ensure |a| >= |b| for subtraction path.
      if ((ea < eb) || ((ea == eb) && (ma < mb))) begin
        {sa, sb} = {sb, sa};
        {ea, eb} = {eb, ea};
        {ma, mb} = {mb, ma};
      end

      sr = sa;
      er = ea;

      ma_ext = {ma, 3'b000};
      mb_ext = {mb, 3'b000};
      sh = int'(ea) - int'(eb);
      mb_sh = shr_sticky27(mb_ext, sh);

      if (sa == sb) begin
        sum = {1'b0, ma_ext} + {1'b0, mb_sh};
        if (sum[27]) begin
          mant = sum[27:1];
          mant[0] |= sum[0];
          er = er + 8'd1;
        end else begin
          mant = sum[26:0];
        end
      end else begin
        if (ma_ext == mb_sh) begin
          o.v = 32'h0000_0000;
          fp32_add = o;
          return;
        end
        mant = ma_ext - mb_sh;
        while ((mant[26] == 1'b0) && (er != 0) && (mant != 0)) begin
          mant = mant << 1;
          er = er - 8'd1;
        end
      end

      if (er >= 8'hFF) begin
        o.v = sr ? FP32_NEG_INF : FP32_POS_INF;
        o.flags |= AM9513_F_OF;
        fp32_add = o;
        return;
      end

      if (er == 8'h00) begin
        o.v = 32'h0000_0000;
        o.flags |= AM9513_F_UF;
        fp32_add = o;
        return;
      end

      r = round24(sr, mant, rm);
      if (r.carry) begin
        er = er + 8'd1;
        r.mant = {1'b1, r.mant[23:1]};
      end

      if (er >= 8'hFF) begin
        o.v = sr ? FP32_NEG_INF : FP32_POS_INF;
        o.flags |= (AM9513_F_OF | AM9513_F_NX);
        fp32_add = o;
        return;
      end

      if (r.nx) o.flags |= AM9513_F_NX;
      o.v = {sr, er, r.mant[22:0]};
      fp32_add = o;
    end
  endfunction

  function automatic am9513_fp32_t fp32_sub(input logic [31:0] a, input logic [31:0] b, input logic [1:0] rm);
    return fp32_add(a, {~b[31], b[30:0]}, rm);
  endfunction

  function automatic am9513_fp32_t fp32_mul(input logic [31:0] a, input logic [31:0] b, input logic [1:0] rm);
    am9513_fp32_t o;
    logic sa, sb, sr;
    logic [7:0] ea, eb, er;
    logic [22:0] fa, fb;
    logic za, zb, ia, ib, na, nb;
    logic [23:0] ma, mb;
    logic [47:0] prod;
    logic [47:0] prod_n;
    logic [26:0] mant;
    am9513_round24_t r;
    int signed exp_unb;
    int signed er_s;
    logic sticky;
    begin
      o.v = '0;
      o.flags = '0;

      sa = a[31]; ea = a[30:23]; fa = a[22:0];
      sb = b[31]; eb = b[30:23]; fb = b[22:0];
      sr = sa ^ sb;

      za = (ea == 8'h00) && (fa == 23'h0);
      zb = (eb == 8'h00) && (fb == 23'h0);
      ia = (ea == 8'hFF) && (fa == 23'h0);
      ib = (eb == 8'hFF) && (fb == 23'h0);
      na = (ea == 8'hFF) && (fa != 23'h0);
      nb = (eb == 8'hFF) && (fb != 23'h0);

      if (na || nb) begin
        o.v = FP32_QNAN;
        fp32_mul = o;
        return;
      end

      if ((ia && zb) || (ib && za)) begin
        o.v = FP32_QNAN;
        o.flags |= AM9513_F_NV;
        fp32_mul = o;
        return;
      end

      if (ia || ib) begin
        o.v = sr ? FP32_NEG_INF : FP32_POS_INF;
        fp32_mul = o;
        return;
      end

      if (za || zb) begin
        o.v = {sr, 31'h0};
        fp32_mul = o;
        return;
      end

      if ((ea == 8'h00) || (eb == 8'h00)) begin
        o.v = {sr, 31'h0};
        o.flags |= AM9513_F_UF;
        fp32_mul = o;
        return;
      end

      ma = {1'b1, fa};
      mb = {1'b1, fb};
      prod = ma * mb;

      exp_unb = (int'(ea) - 127) + (int'(eb) - 127);
      er_s = exp_unb + 127;

      if (prod[47]) begin
        prod_n = prod >> 1;
        er_s = er_s + 1;
      end else begin
        prod_n = prod;
      end

      if (er_s >= 255) begin
        o.v = sr ? FP32_NEG_INF : FP32_POS_INF;
        o.flags |= AM9513_F_OF;
        fp32_mul = o;
        return;
      end

      if (er_s <= 0) begin
        o.v = {sr, 31'h0};
        o.flags |= AM9513_F_UF;
        fp32_mul = o;
        return;
      end

      sticky = |prod_n[20:0];
      mant = {prod_n[46:23], prod_n[22], prod_n[21], sticky};
      r = round24(sr, mant, rm);
      er = 8'(er_s);

      if (r.carry) begin
        er = er + 8'd1;
        r.mant = {1'b1, r.mant[23:1]};
      end

      if (er >= 8'hFF) begin
        o.v = sr ? FP32_NEG_INF : FP32_POS_INF;
        o.flags |= (AM9513_F_OF | AM9513_F_NX);
        fp32_mul = o;
        return;
      end

      if (r.nx) o.flags |= AM9513_F_NX;
      o.v = {sr, er, r.mant[22:0]};
      fp32_mul = o;
    end
  endfunction

  function automatic am9513_fp32_t fp32_div(input logic [31:0] a, input logic [31:0] b, input logic [1:0] rm);
    am9513_fp32_t o;
    logic sa, sb, sr;
    logic [7:0] ea, eb, er;
    logic [22:0] fa, fb;
    logic za, zb, ia, ib, na, nb;
    logic [23:0] ma, mb;
    logic [49:0] numer;
    logic [63:0] q_full;
    logic [23:0] rem;
    logic [26:0] mant;
    am9513_round24_t r;
    int signed exp_unb;
    int signed er_s;
    begin
      o.v = '0;
      o.flags = '0;

      sa = a[31]; ea = a[30:23]; fa = a[22:0];
      sb = b[31]; eb = b[30:23]; fb = b[22:0];
      sr = sa ^ sb;

      za = (ea == 8'h00) && (fa == 23'h0);
      zb = (eb == 8'h00) && (fb == 23'h0);
      ia = (ea == 8'hFF) && (fa == 23'h0);
      ib = (eb == 8'hFF) && (fb == 23'h0);
      na = (ea == 8'hFF) && (fa != 23'h0);
      nb = (eb == 8'hFF) && (fb != 23'h0);

      if (na || nb) begin
        o.v = FP32_QNAN;
        fp32_div = o;
        return;
      end

      if ((ia && ib) || (za && zb)) begin
        o.v = FP32_QNAN;
        o.flags |= AM9513_F_NV;
        fp32_div = o;
        return;
      end

      if (zb) begin
        if (za) begin
          o.v = FP32_QNAN;
          o.flags |= AM9513_F_NV;
        end else begin
          o.v = sr ? FP32_NEG_INF : FP32_POS_INF;
          o.flags |= AM9513_F_DZ;
        end
        fp32_div = o;
        return;
      end

      if (ia) begin
        o.v = sr ? FP32_NEG_INF : FP32_POS_INF;
        fp32_div = o;
        return;
      end

      if (ib) begin
        o.v = {sr, 31'h0};
        fp32_div = o;
        return;
      end

      if (za) begin
        o.v = {sr, 31'h0};
        fp32_div = o;
        return;
      end

      if ((ea == 8'h00) || (eb == 8'h00)) begin
        o.v = {sr, 31'h0};
        o.flags |= AM9513_F_UF;
        fp32_div = o;
        return;
      end

      ma = {1'b1, fa};
      mb = {1'b1, fb};

      exp_unb = (int'(ea) - 127) - (int'(eb) - 127);
      er_s = exp_unb + 127;

      numer = {ma, 26'b0}; // ma << (23+3)
      q_full = numer / mb;
      rem = numer % mb;
      mant = 27'(q_full[26:0]);
      if (rem != 0) mant[0] = 1'b1;

      if (mant[26] == 1'b0) begin
        mant = mant << 1;
        er_s = er_s - 1;
      end

      if (er_s >= 255) begin
        o.v = sr ? FP32_NEG_INF : FP32_POS_INF;
        o.flags |= AM9513_F_OF;
        fp32_div = o;
        return;
      end

      if (er_s <= 0) begin
        o.v = {sr, 31'h0};
        o.flags |= AM9513_F_UF;
        fp32_div = o;
        return;
      end

      r = round24(sr, mant, rm);
      er = 8'(er_s);
      if (r.carry) begin
        er = er + 8'd1;
        r.mant = {1'b1, r.mant[23:1]};
      end

      if (er >= 8'hFF) begin
        o.v = sr ? FP32_NEG_INF : FP32_POS_INF;
        o.flags |= (AM9513_F_OF | AM9513_F_NX);
        fp32_div = o;
        return;
      end

      if (r.nx) o.flags |= AM9513_F_NX;
      o.v = {sr, er, r.mant[22:0]};
      fp32_div = o;
    end
  endfunction

  function automatic am9513_fp32_t fp32_sqrt(input logic [31:0] a, input logic [1:0] rm);
    am9513_fp32_t o;
    logic sa;
    logic [7:0] ea, er;
    logic [22:0] fa;
    logic za, ia, na;
    logic [24:0] ma;
    int signed e_unb;
    int signed e_adj;
    int signed e_out;
    logic [47:0] rad;
    am9513_isqrt48_t s;
    logic [23:0] mant24;
    begin
      o.v = '0;
      o.flags = '0;

      sa = a[31]; ea = a[30:23]; fa = a[22:0];
      za = (ea == 8'h00) && (fa == 23'h0);
      ia = (ea == 8'hFF) && (fa == 23'h0);
      na = (ea == 8'hFF) && (fa != 23'h0);

      if (na) begin
        o.v = FP32_QNAN;
        fp32_sqrt = o;
        return;
      end

      if (ia) begin
        o.v = sa ? FP32_QNAN : FP32_POS_INF;
        if (sa) o.flags |= AM9513_F_NV;
        fp32_sqrt = o;
        return;
      end

      if (za) begin
        o.v = a;
        fp32_sqrt = o;
        return;
      end

      if (sa) begin
        o.v = FP32_QNAN;
        o.flags |= AM9513_F_NV;
        fp32_sqrt = o;
        return;
      end

      if (ea == 8'h00) begin
        o.v = 32'h0000_0000;
        o.flags |= AM9513_F_UF;
        fp32_sqrt = o;
        return;
      end

      e_unb = int'(ea) - 127;
      ma = {1'b1, fa};
      e_adj = e_unb;
      if (e_adj[0]) begin
        ma = ma << 1;
        e_adj = e_adj - 1;
      end

      e_out = (e_adj >>> 1);
      er = 8'(e_out + 127);

      rad = 48'(ma) << 23;
      s = isqrt48(rad);
      mant24 = s.root;
      if (mant24[23] == 1'b0) begin
        mant24 = mant24 << 1;
        er = er - 8'd1;
      end

      if (s.rem_nonzero) o.flags |= AM9513_F_NX;
      o.v = {1'b0, er, mant24[22:0]};
      fp32_sqrt = o;
    end
  endfunction

  function automatic am9513_fp32_t fp32_fma(
      input logic [31:0] a,
      input logic [31:0] b,
      input logic [31:0] c,
      input logic [1:0] rm
  );
    am9513_fp32_t m;
    am9513_fp32_t s;
    begin
      m = fp32_mul(a, b, rm);
      s = fp32_add(m.v, c, rm);
      s.flags |= m.flags;
      fp32_fma = s;
    end
  endfunction

  // --------------------------------------------------------------------------
  // FP64 core ops (flush subnormals to zero; deterministic subset)
  // --------------------------------------------------------------------------
  function automatic am9513_fp64_t fp64_add(input logic [63:0] a, input logic [63:0] b, input logic [1:0] rm);
    am9513_fp64_t o;
    logic sa, sb, sr;
    logic [10:0] ea, eb, er;
    logic [51:0] fa, fb;
    logic za, zb, ia, ib, na, nb;
    logic [52:0] ma, mb;
    logic [55:0] ma_ext, mb_ext, mb_sh;
    logic [56:0] sum;
    logic [55:0] mant;
    am9513_round53_t r;
    int unsigned sh;
    begin
      o.v = '0;
      o.flags = '0;

      sa = a[63]; ea = a[62:52]; fa = a[51:0];
      sb = b[63]; eb = b[62:52]; fb = b[51:0];

      za = (ea == 11'h000) && (fa == 52'h0);
      zb = (eb == 11'h000) && (fb == 52'h0);
      ia = (ea == 11'h7FF) && (fa == 52'h0);
      ib = (eb == 11'h7FF) && (fb == 52'h0);
      na = (ea == 11'h7FF) && (fa != 52'h0);
      nb = (eb == 11'h7FF) && (fb != 52'h0);

      if (na || nb) begin
        o.v = FP64_QNAN;
        fp64_add = o;
        return;
      end

      if (ia && ib && (sa != sb)) begin
        o.v = FP64_QNAN;
        o.flags |= AM9513_F_NV;
        fp64_add = o;
        return;
      end

      if (ia) begin
        o.v = sa ? FP64_NEG_INF : FP64_POS_INF;
        fp64_add = o;
        return;
      end

      if (ib) begin
        o.v = sb ? FP64_NEG_INF : FP64_POS_INF;
        fp64_add = o;
        return;
      end

      if (za && zb) begin
        o.v = 64'h0000_0000_0000_0000;
        fp64_add = o;
        return;
      end

      if (za) begin
        o.v = b;
        fp64_add = o;
        return;
      end

      if (zb) begin
        o.v = a;
        fp64_add = o;
        return;
      end

      if (ea == 11'h000) begin
        o.v = b;
        o.flags |= AM9513_F_UF;
        fp64_add = o;
        return;
      end
      if (eb == 11'h000) begin
        o.v = a;
        o.flags |= AM9513_F_UF;
        fp64_add = o;
        return;
      end

      ma = {1'b1, fa};
      mb = {1'b1, fb};

      if ((ea < eb) || ((ea == eb) && (ma < mb))) begin
        {sa, sb} = {sb, sa};
        {ea, eb} = {eb, ea};
        {ma, mb} = {mb, ma};
      end

      sr = sa;
      er = ea;
      ma_ext = {ma, 3'b000};
      mb_ext = {mb, 3'b000};
      sh = int'(ea) - int'(eb);
      mb_sh = shr_sticky56(mb_ext, sh);

      if (sa == sb) begin
        sum = {1'b0, ma_ext} + {1'b0, mb_sh};
        if (sum[56]) begin
          mant = sum[56:1];
          mant[0] |= sum[0];
          er = er + 11'd1;
        end else begin
          mant = sum[55:0];
        end
      end else begin
        if (ma_ext == mb_sh) begin
          o.v = 64'h0000_0000_0000_0000;
          fp64_add = o;
          return;
        end
        mant = ma_ext - mb_sh;
        while ((mant[55] == 1'b0) && (er != 0) && (mant != 0)) begin
          mant = mant << 1;
          er = er - 11'd1;
        end
      end

      if (er >= 11'h7FF) begin
        o.v = sr ? FP64_NEG_INF : FP64_POS_INF;
        o.flags |= AM9513_F_OF;
        fp64_add = o;
        return;
      end

      if (er == 11'h000) begin
        o.v = 64'h0000_0000_0000_0000;
        o.flags |= AM9513_F_UF;
        fp64_add = o;
        return;
      end

      r = round53(sr, mant, rm);
      if (r.carry) begin
        er = er + 11'd1;
        r.mant = {1'b1, r.mant[52:1]};
      end

      if (er >= 11'h7FF) begin
        o.v = sr ? FP64_NEG_INF : FP64_POS_INF;
        o.flags |= (AM9513_F_OF | AM9513_F_NX);
        fp64_add = o;
        return;
      end

      if (r.nx) o.flags |= AM9513_F_NX;
      o.v = {sr, er, r.mant[51:0]};
      fp64_add = o;
    end
  endfunction

  function automatic am9513_fp64_t fp64_sub(input logic [63:0] a, input logic [63:0] b, input logic [1:0] rm);
    return fp64_add(a, {~b[63], b[62:0]}, rm);
  endfunction

  function automatic am9513_fp64_t fp64_mul(input logic [63:0] a, input logic [63:0] b, input logic [1:0] rm);
    am9513_fp64_t o;
    logic sa, sb, sr;
    logic [10:0] ea, eb, er;
    logic [51:0] fa, fb;
    logic za, zb, ia, ib, na, nb;
    logic [52:0] ma, mb;
    logic [105:0] prod;
    logic [105:0] prod_n;
    logic [55:0] mant;
    am9513_round53_t r;
    int signed exp_unb;
    int signed er_s;
    logic sticky;
    begin
      o.v = '0;
      o.flags = '0;

      sa = a[63]; ea = a[62:52]; fa = a[51:0];
      sb = b[63]; eb = b[62:52]; fb = b[51:0];
      sr = sa ^ sb;

      za = (ea == 11'h000) && (fa == 52'h0);
      zb = (eb == 11'h000) && (fb == 52'h0);
      ia = (ea == 11'h7FF) && (fa == 52'h0);
      ib = (eb == 11'h7FF) && (fb == 52'h0);
      na = (ea == 11'h7FF) && (fa != 52'h0);
      nb = (eb == 11'h7FF) && (fb != 52'h0);

      if (na || nb) begin
        o.v = FP64_QNAN;
        fp64_mul = o;
        return;
      end

      if ((ia && zb) || (ib && za)) begin
        o.v = FP64_QNAN;
        o.flags |= AM9513_F_NV;
        fp64_mul = o;
        return;
      end

      if (ia || ib) begin
        o.v = sr ? FP64_NEG_INF : FP64_POS_INF;
        fp64_mul = o;
        return;
      end

      if (za || zb) begin
        o.v = {sr, 63'h0};
        fp64_mul = o;
        return;
      end

      if ((ea == 11'h000) || (eb == 11'h000)) begin
        o.v = {sr, 63'h0};
        o.flags |= AM9513_F_UF;
        fp64_mul = o;
        return;
      end

      ma = {1'b1, fa};
      mb = {1'b1, fb};
      prod = ma * mb;

      exp_unb = (int'(ea) - 1023) + (int'(eb) - 1023);
      er_s = exp_unb + 1023;

      if (prod[105]) begin
        prod_n = prod >> 1;
        er_s = er_s + 1;
      end else begin
        prod_n = prod;
      end

      if (er_s >= 2047) begin
        o.v = sr ? FP64_NEG_INF : FP64_POS_INF;
        o.flags |= AM9513_F_OF;
        fp64_mul = o;
        return;
      end

      if (er_s <= 0) begin
        o.v = {sr, 63'h0};
        o.flags |= AM9513_F_UF;
        fp64_mul = o;
        return;
      end

      sticky = |prod_n[49:0];
      mant = {prod_n[104:52], prod_n[51], prod_n[50], sticky};
      r = round53(sr, mant, rm);
      er = 11'(er_s);

      if (r.carry) begin
        er = er + 11'd1;
        r.mant = {1'b1, r.mant[52:1]};
      end

      if (er >= 11'h7FF) begin
        o.v = sr ? FP64_NEG_INF : FP64_POS_INF;
        o.flags |= (AM9513_F_OF | AM9513_F_NX);
        fp64_mul = o;
        return;
      end

      if (r.nx) o.flags |= AM9513_F_NX;
      o.v = {sr, er, r.mant[51:0]};
      fp64_mul = o;
    end
  endfunction

  function automatic am9513_fp64_t fp64_div(input logic [63:0] a, input logic [63:0] b, input logic [1:0] rm);
    am9513_fp64_t o;
    logic sa, sb, sr;
    logic [10:0] ea, eb, er;
    logic [51:0] fa, fb;
    logic za, zb, ia, ib, na, nb;
    logic [52:0] ma, mb;
    logic [107:0] numer;
    logic [127:0] q_full;
    logic [52:0] rem;
    logic [55:0] mant;
    am9513_round53_t r;
    int signed exp_unb;
    int signed er_s;
    begin
      o.v = '0;
      o.flags = '0;

      sa = a[63]; ea = a[62:52]; fa = a[51:0];
      sb = b[63]; eb = b[62:52]; fb = b[51:0];
      sr = sa ^ sb;

      za = (ea == 11'h000) && (fa == 52'h0);
      zb = (eb == 11'h000) && (fb == 52'h0);
      ia = (ea == 11'h7FF) && (fa == 52'h0);
      ib = (eb == 11'h7FF) && (fb == 52'h0);
      na = (ea == 11'h7FF) && (fa != 52'h0);
      nb = (eb == 11'h7FF) && (fb != 52'h0);

      if (na || nb) begin
        o.v = FP64_QNAN;
        fp64_div = o;
        return;
      end

      if ((ia && ib) || (za && zb)) begin
        o.v = FP64_QNAN;
        o.flags |= AM9513_F_NV;
        fp64_div = o;
        return;
      end

      if (zb) begin
        if (za) begin
          o.v = FP64_QNAN;
          o.flags |= AM9513_F_NV;
        end else begin
          o.v = sr ? FP64_NEG_INF : FP64_POS_INF;
          o.flags |= AM9513_F_DZ;
        end
        fp64_div = o;
        return;
      end

      if (ia) begin
        o.v = sr ? FP64_NEG_INF : FP64_POS_INF;
        fp64_div = o;
        return;
      end

      if (ib) begin
        o.v = {sr, 63'h0};
        fp64_div = o;
        return;
      end

      if (za) begin
        o.v = {sr, 63'h0};
        fp64_div = o;
        return;
      end

      if ((ea == 11'h000) || (eb == 11'h000)) begin
        o.v = {sr, 63'h0};
        o.flags |= AM9513_F_UF;
        fp64_div = o;
        return;
      end

      ma = {1'b1, fa};
      mb = {1'b1, fb};

      exp_unb = (int'(ea) - 1023) - (int'(eb) - 1023);
      er_s = exp_unb + 1023;

      numer = {ma, 55'b0}; // ma << (52+3)
      q_full = numer / mb;
      rem = numer % mb;
      mant = 56'(q_full[55:0]);
      if (rem != 0) mant[0] = 1'b1;

      if (mant[55] == 1'b0) begin
        mant = mant << 1;
        er_s = er_s - 1;
      end

      if (er_s >= 2047) begin
        o.v = sr ? FP64_NEG_INF : FP64_POS_INF;
        o.flags |= AM9513_F_OF;
        fp64_div = o;
        return;
      end

      if (er_s <= 0) begin
        o.v = {sr, 63'h0};
        o.flags |= AM9513_F_UF;
        fp64_div = o;
        return;
      end

      r = round53(sr, mant, rm);
      er = 11'(er_s);
      if (r.carry) begin
        er = er + 11'd1;
        r.mant = {1'b1, r.mant[52:1]};
      end

      if (er >= 11'h7FF) begin
        o.v = sr ? FP64_NEG_INF : FP64_POS_INF;
        o.flags |= (AM9513_F_OF | AM9513_F_NX);
        fp64_div = o;
        return;
      end

      if (r.nx) o.flags |= AM9513_F_NX;
      o.v = {sr, er, r.mant[51:0]};
      fp64_div = o;
    end
  endfunction

  function automatic am9513_fp64_t fp64_sqrt(input logic [63:0] a, input logic [1:0] rm);
    am9513_fp64_t o;
    logic sa;
    logic [10:0] ea, er;
    logic [51:0] fa;
    logic za, ia, na;
    logic [53:0] ma;
    int signed e_unb;
    int signed e_adj;
    int signed e_out;
    logic [105:0] rad;
    am9513_isqrt106_t s;
    logic [52:0] mant53;
    begin
      o.v = '0;
      o.flags = '0;

      sa = a[63]; ea = a[62:52]; fa = a[51:0];
      za = (ea == 11'h000) && (fa == 52'h0);
      ia = (ea == 11'h7FF) && (fa == 52'h0);
      na = (ea == 11'h7FF) && (fa != 52'h0);

      if (na) begin
        o.v = FP64_QNAN;
        fp64_sqrt = o;
        return;
      end

      if (ia) begin
        o.v = sa ? FP64_QNAN : FP64_POS_INF;
        if (sa) o.flags |= AM9513_F_NV;
        fp64_sqrt = o;
        return;
      end

      if (za) begin
        o.v = a;
        fp64_sqrt = o;
        return;
      end

      if (sa) begin
        o.v = FP64_QNAN;
        o.flags |= AM9513_F_NV;
        fp64_sqrt = o;
        return;
      end

      if (ea == 11'h000) begin
        o.v = 64'h0000_0000_0000_0000;
        o.flags |= AM9513_F_UF;
        fp64_sqrt = o;
        return;
      end

      e_unb = int'(ea) - 1023;
      ma = {1'b1, fa};
      e_adj = e_unb;
      if (e_adj[0]) begin
        ma = ma << 1;
        e_adj = e_adj - 1;
      end

      e_out = (e_adj >>> 1);
      er = 11'(e_out + 1023);

      rad = 106'(ma) << 52;
      s = isqrt106(rad);
      mant53 = s.root;
      if (mant53[52] == 1'b0) begin
        mant53 = mant53 << 1;
        er = er - 11'd1;
      end

      if (s.rem_nonzero) o.flags |= AM9513_F_NX;
      o.v = {1'b0, er, mant53[51:0]};
      fp64_sqrt = o;
    end
  endfunction

  function automatic am9513_fp64_t fp64_fma(
      input logic [63:0] a,
      input logic [63:0] b,
      input logic [63:0] c,
      input logic [1:0] rm
  );
    am9513_fp64_t m;
    am9513_fp64_t s;
    begin
      m = fp64_mul(a, b, rm);
      s = fp64_add(m.v, c, rm);
      s.flags |= m.flags;
      fp64_fma = s;
    end
  endfunction

  // --------------------------------------------------------------------------
  // Conversions (float<->float; float<->int)
  // --------------------------------------------------------------------------
  function automatic am9513_fp32_t fp16_to_fp32(input logic [15:0] h);
    am9513_fp32_t o;
    logic s;
    logic [4:0] e;
    logic [9:0] f;
    logic [7:0] e32;
    begin
      o.v = '0;
      o.flags = '0;
      s = h[15];
      e = h[14:10];
      f = h[9:0];

      if (e == 5'h00) begin
        o.v = {s, 31'h0};
        if (f != 0) o.flags |= AM9513_F_UF;
        fp16_to_fp32 = o;
        return;
      end

      if (e == 5'h1F) begin
        if (f == 0) o.v = s ? FP32_NEG_INF : FP32_POS_INF;
        else o.v = FP32_QNAN;
        fp16_to_fp32 = o;
        return;
      end

      e32 = 8'(int'(e) + (127 - 15));
      o.v = {s, e32, {f, 13'b0}};
      fp16_to_fp32 = o;
    end
  endfunction

  function automatic am9513_fp32_t bf16_to_fp32(input logic [15:0] b);
    am9513_fp32_t o;
    begin
      o.v = {b, 16'h0000};
      o.flags = '0;
      bf16_to_fp32 = o;
    end
  endfunction

  function automatic logic [15:0] fp32_to_bf16_bits(
      input logic [31:0] a,
      input logic [1:0] rm,
      output logic nx
  );
    logic sign;
    logic [15:0] top;
    logic [15:0] low;
    logic lsb;
    logic inc;
    begin
      sign = a[31];
      top = a[31:16];
      low = a[15:0];
      lsb = top[0];
      nx = (low != 0);

      unique case (rm)
        2'(CARBON_RND_RZ): inc = 1'b0;
        2'(CARBON_RND_RP): inc = (!sign) && (low != 0);
        2'(CARBON_RND_RM): inc = (sign) && (low != 0);
        default: inc = (low > 16'h8000) || ((low == 16'h8000) && lsb);
      endcase

      fp32_to_bf16_bits = top + 16'(inc);
    end
  endfunction

  function automatic am9513_fp32_t fp32_to_fp16(input logic [31:0] a, input logic [1:0] rm);
    am9513_fp32_t o;
    logic s;
    logic [7:0] e;
    logic [22:0] f;
    int signed e_unb;
    int signed e16;
    logic [23:0] mant;
    logic [12:0] drop;
    logic guard, roundb, sticky, any, lsb, inc;
    logic [11:0] mant11;
    logic [4:0] e5;
    logic [9:0] f10;
    begin
      o.v = '0;
      o.flags = '0;

      s = a[31];
      e = a[30:23];
      f = a[22:0];

      if (e == 8'h00) begin
        o.v = {s, 31'h0};
        if (f != 0) o.flags |= AM9513_F_UF;
        fp32_to_fp16 = o;
        return;
      end

      if (e == 8'hFF) begin
        if (f == 0) o.v = {16'h0000, (s ? 16'hFC00 : 16'h7C00)};
        else o.v = {16'h0000, 16'h7E00};
        fp32_to_fp16 = o;
        return;
      end

      e_unb = int'(e) - 127;
      e16 = e_unb + 15;
      if (e16 >= 31) begin
        o.v = {16'h0000, (s ? 16'hFC00 : 16'h7C00)};
        o.flags |= (AM9513_F_OF | AM9513_F_NX);
        fp32_to_fp16 = o;
        return;
      end

      if (e16 <= 0) begin
        o.v = {16'h0000, (s ? 16'h8000 : 16'h0000)};
        o.flags |= (AM9513_F_UF | AM9513_F_NX);
        fp32_to_fp16 = o;
        return;
      end

      mant = {1'b1, f};
      mant11 = mant[23:13];
      drop = mant[12:0];
      guard = drop[12];
      roundb = drop[11];
      sticky = |drop[10:0];
      any = guard | roundb | sticky;
      lsb = mant11[0];

      unique case (rm)
        2'(CARBON_RND_RZ): inc = 1'b0;
        2'(CARBON_RND_RP): inc = (!s) && any;
        2'(CARBON_RND_RM): inc = (s) && any;
        default: inc = guard && (roundb || sticky || lsb);
      endcase

      mant11 = mant11 + 12'(inc);
      if (mant11[11]) begin
        mant11 = {1'b1, mant11[11:1]};
        e16 = e16 + 1;
        if (e16 >= 31) begin
          o.v = {16'h0000, (s ? 16'hFC00 : 16'h7C00)};
          o.flags |= (AM9513_F_OF | AM9513_F_NX);
          fp32_to_fp16 = o;
          return;
        end
      end

      e5 = 5'(e16);
      f10 = mant11[9:0];
      o.v = {16'h0000, {s, e5, f10}};
      if (any) o.flags |= AM9513_F_NX;
      fp32_to_fp16 = o;
    end
  endfunction

  function automatic am9513_fp32_t fp32_to_bf16(input logic [31:0] a, input logic [1:0] rm);
    am9513_fp32_t o;
    logic nx;
    logic [15:0] bits;
    begin
      bits = fp32_to_bf16_bits(a, rm, nx);
      o.v = {16'h0000, bits};
      o.flags = nx ? AM9513_F_NX : 5'h0;
      fp32_to_bf16 = o;
    end
  endfunction

  function automatic am9513_fp64_t fp32_to_fp64(input logic [31:0] a);
    am9513_fp64_t o;
    logic s;
    logic [7:0] e;
    logic [22:0] f;
    logic [10:0] e64;
    begin
      o.v = '0;
      o.flags = '0;
      s = a[31]; e = a[30:23]; f = a[22:0];

      if (e == 8'h00) begin
        o.v = {s, 63'h0};
        fp32_to_fp64 = o;
        return;
      end
      if (e == 8'hFF) begin
        if (f == 0) o.v = s ? FP64_NEG_INF : FP64_POS_INF;
        else o.v = FP64_QNAN;
        fp32_to_fp64 = o;
        return;
      end

      e64 = 11'(int'(e) + (1023 - 127));
      o.v = {s, e64, {f, 29'b0}};
      fp32_to_fp64 = o;
    end
  endfunction

  function automatic am9513_fp32_t fp64_to_fp32(input logic [63:0] a, input logic [1:0] rm);
    am9513_fp32_t o;
    logic s;
    logic [10:0] e;
    logic [51:0] f;
    int signed e_unb;
    int signed e32;
    logic [52:0] mant;
    logic [28:0] drop;
    logic guard, roundb, sticky, any, lsb, inc;
    logic [24:0] mant24;
    logic [7:0] e8;
    begin
      o.v = '0;
      o.flags = '0;

      s = a[63]; e = a[62:52]; f = a[51:0];
      if (e == 11'h000) begin
        o.v = {s, 31'h0};
        if (f != 0) o.flags |= AM9513_F_UF;
        fp64_to_fp32 = o;
        return;
      end

      if (e == 11'h7FF) begin
        if (f == 0) o.v = s ? FP32_NEG_INF : FP32_POS_INF;
        else o.v = FP32_QNAN;
        fp64_to_fp32 = o;
        return;
      end

      e_unb = int'(e) - 1023;
      e32 = e_unb + 127;
      if (e32 >= 255) begin
        o.v = s ? FP32_NEG_INF : FP32_POS_INF;
        o.flags |= (AM9513_F_OF | AM9513_F_NX);
        fp64_to_fp32 = o;
        return;
      end

      if (e32 <= 0) begin
        o.v = {s, 31'h0};
        o.flags |= (AM9513_F_UF | AM9513_F_NX);
        fp64_to_fp32 = o;
        return;
      end

      mant = {1'b1, f};
      mant24 = mant[52:28];
      drop = mant[27:0];
      guard = drop[28];
      roundb = drop[27];
      sticky = |drop[26:0];
      any = guard | roundb | sticky;
      lsb = mant24[0];

      unique case (rm)
        2'(CARBON_RND_RZ): inc = 1'b0;
        2'(CARBON_RND_RP): inc = (!s) && any;
        2'(CARBON_RND_RM): inc = (s) && any;
        default: inc = guard && (roundb || sticky || lsb);
      endcase

      mant24 = mant24 + 25'(inc);
      if (mant24[24]) begin
        mant24 = {1'b1, mant24[24:1]};
        e32 = e32 + 1;
        if (e32 >= 255) begin
          o.v = s ? FP32_NEG_INF : FP32_POS_INF;
          o.flags |= (AM9513_F_OF | AM9513_F_NX);
          fp64_to_fp32 = o;
          return;
        end
      end

      e8 = 8'(e32);
      o.v = {s, e8, mant24[22:0]};
      if (any) o.flags |= AM9513_F_NX;
      fp64_to_fp32 = o;
    end
  endfunction

  function automatic am9513_fp32_t int32_to_fp32(input logic [31:0] a, input logic [1:0] rm);
    am9513_fp32_t o;
    logic s;
    logic [31:0] mag;
    int msb;
    int signed e_unb;
    logic [55:0] shifted;
    logic [23:0] mant;
    logic [31:0] dropped;
    logic sticky;
    logic [7:0] e8;
    begin
      o.v = '0;
      o.flags = '0;

      if (a == 32'h0) begin
        o.v = 32'h0;
        int32_to_fp32 = o;
        return;
      end

      s = a[31];
      mag = s ? (32'(~a) + 1) : a;

      msb = 31;
      while ((msb > 0) && !mag[msb]) msb--;
      e_unb = msb;

      if (msb > 23) begin
        shifted = 56'(mag) >> (msb - 23);
        dropped = mag & ((32'h1 << (msb - 23)) - 1);
      end else begin
        shifted = 56'(mag) << (23 - msb);
        dropped = 32'h0;
      end

      mant = shifted[23:0];
      sticky = (dropped != 0);
      e8 = 8'(e_unb + 127);
      o.v = {s, e8, mant[22:0]};
      if (sticky) o.flags |= AM9513_F_NX;
      int32_to_fp32 = o;
    end
  endfunction

  function automatic am9513_fp64_t int64_to_fp64(input logic [63:0] a, input logic [1:0] rm);
    am9513_fp64_t o;
    logic s;
    logic [63:0] mag;
    int msb;
    int signed e_unb;
    logic [127:0] shifted;
    logic [52:0] mant;
    logic [63:0] dropped;
    logic sticky;
    logic [10:0] e11;
    begin
      o.v = '0;
      o.flags = '0;

      if (a == 64'h0) begin
        o.v = 64'h0;
        int64_to_fp64 = o;
        return;
      end

      s = a[63];
      mag = s ? (64'(~a) + 1) : a;

      msb = 63;
      while ((msb > 0) && !mag[msb]) msb--;
      e_unb = msb;

      if (msb > 52) begin
        shifted = 128'(mag) >> (msb - 52);
        dropped = mag & ((64'h1 << (msb - 52)) - 1);
      end else begin
        shifted = 128'(mag) << (52 - msb);
        dropped = 64'h0;
      end

      mant = shifted[52:0];
      sticky = (dropped != 0);
      e11 = 11'(e_unb + 1023);
      o.v = {s, e11, mant[51:0]};
      if (sticky) o.flags |= AM9513_F_NX;
      int64_to_fp64 = o;
    end
  endfunction

  function automatic am9513_i32_t fp32_to_int32(input logic [31:0] a, input logic [1:0] rm);
    am9513_i32_t o;
    logic s;
    logic [7:0] e;
    logic [22:0] f;
    int signed e_unb;
    logic [23:0] mant;
    int unsigned sh;
    logic [31:0] int_mag;
    logic [23:0] rem;
    logic inc;
    logic [31:0] mag_rounded;
    begin
      o.v = '0;
      o.flags = '0;

      s = a[31];
      e = a[30:23];
      f = a[22:0];

      // NaN/Inf
      if (e == 8'hFF) begin
        o.flags |= AM9513_F_NV;
        if (f != 0) o.v = 32'h0000_0000;
        else o.v = s ? 32'h8000_0000 : 32'h7FFF_FFFF;
        fp32_to_int32 = o;
        return;
      end

      // Zero/subnormal
      if (e == 8'h00) begin
        if (f == 0) begin
          o.v = 32'h0000_0000;
        end else begin
          o.flags |= AM9513_F_NX;
          unique case (rm)
            2'(CARBON_RND_RP): o.v = s ? 32'h0000_0000 : 32'h0000_0001;
            2'(CARBON_RND_RM): o.v = s ? 32'hFFFF_FFFF : 32'h0000_0000;
            default: o.v = 32'h0000_0000;
          endcase
        end
        fp32_to_int32 = o;
        return;
      end

      e_unb = int'(e) - 127;
      mant = {1'b1, f};

      // Magnitude < 1.0
      if (e_unb < 0) begin
        o.flags |= AM9513_F_NX;
        unique case (rm)
          2'(CARBON_RND_RP): o.v = s ? 32'h0000_0000 : 32'h0000_0001;
          2'(CARBON_RND_RM): o.v = s ? 32'hFFFF_FFFF : 32'h0000_0000;
          default: begin
            // RN/RZ: only values in [0.5,1) round to +/-1 under RN.
            if ((e_unb == -1) && (mant > 24'h800000)) o.v = s ? 32'hFFFF_FFFF : 32'h0000_0001;
            else o.v = 32'h0000_0000;
          end
        endcase
        fp32_to_int32 = o;
        return;
      end

      // Overflow check (allow exact -2^31).
      if (e_unb > 31) begin
        o.flags |= AM9513_F_NV;
        o.v = s ? 32'h8000_0000 : 32'h7FFF_FFFF;
        fp32_to_int32 = o;
        return;
      end
      if (e_unb == 31) begin
        if (s && (f == 0)) o.v = 32'h8000_0000;
        else begin
          o.flags |= AM9513_F_NV;
          o.v = s ? 32'h8000_0000 : 32'h7FFF_FFFF;
        end
        fp32_to_int32 = o;
        return;
      end

      rem = '0;
      if (e_unb >= 23) begin
        int_mag = 32'(mant) << (e_unb - 23);
      end else begin
        sh = 23 - e_unb;
        int_mag = 32'(mant) >> sh;
        rem = mant[sh-1:0];
        if (rem != 0) o.flags |= AM9513_F_NX;
      end

      inc = 1'b0;
      if ((e_unb < 23) && (rem != 0)) begin
        unique case (rm)
          2'(CARBON_RND_RZ): inc = 1'b0;
          2'(CARBON_RND_RP): inc = (!s);
          2'(CARBON_RND_RM): inc = (s);
          default: begin
            logic [23:0] half;
            half = 24'(1) << ((23 - e_unb) - 1);
            if (rem > half) inc = 1'b1;
            else if (rem == half) inc = int_mag[0];
          end
        endcase
      end

      mag_rounded = int_mag + 32'(inc);
      if (!s) begin
        if (mag_rounded > 32'h7FFF_FFFF) begin
          o.flags |= AM9513_F_NV;
          o.v = 32'h7FFF_FFFF;
        end else begin
          o.v = mag_rounded;
        end
      end else begin
        if (mag_rounded > 32'h8000_0000) begin
          o.flags |= AM9513_F_NV;
          o.v = 32'h8000_0000;
        end else begin
          o.v = 32'(~mag_rounded + 1);
        end
      end

      fp32_to_int32 = o;
    end
  endfunction

  function automatic am9513_i64_t fp64_to_int64(input logic [63:0] a, input logic [1:0] rm);
    am9513_i64_t o;
    logic s;
    logic [10:0] e;
    logic [51:0] f;
    int signed e_unb;
    logic [52:0] mant;
    int unsigned sh;
    logic [63:0] int_mag;
    logic [52:0] rem;
    logic inc;
    logic [63:0] mag_rounded;
    begin
      o.v = '0;
      o.flags = '0;

      s = a[63];
      e = a[62:52];
      f = a[51:0];

      // NaN/Inf
      if (e == 11'h7FF) begin
        o.flags |= AM9513_F_NV;
        if (f != 0) o.v = 64'h0;
        else o.v = s ? 64'h8000_0000_0000_0000 : 64'h7FFF_FFFF_FFFF_FFFF;
        fp64_to_int64 = o;
        return;
      end

      // Zero/subnormal
      if (e == 11'h000) begin
        if (f == 0) begin
          o.v = 64'h0;
        end else begin
          o.flags |= AM9513_F_NX;
          unique case (rm)
            2'(CARBON_RND_RP): o.v = s ? 64'h0 : 64'h1;
            2'(CARBON_RND_RM): o.v = s ? 64'hFFFF_FFFF_FFFF_FFFF : 64'h0;
            default: o.v = 64'h0;
          endcase
        end
        fp64_to_int64 = o;
        return;
      end

      e_unb = int'(e) - 1023;
      mant = {1'b1, f};

      // Magnitude < 1.0
      if (e_unb < 0) begin
        o.flags |= AM9513_F_NX;
        unique case (rm)
          2'(CARBON_RND_RP): o.v = s ? 64'h0 : 64'h1;
          2'(CARBON_RND_RM): o.v = s ? 64'hFFFF_FFFF_FFFF_FFFF : 64'h0;
          default: begin
            if ((e_unb == -1) && (mant > 53'(1) << 52)) o.v = s ? 64'hFFFF_FFFF_FFFF_FFFF : 64'h1;
            else o.v = 64'h0;
          end
        endcase
        fp64_to_int64 = o;
        return;
      end

      // Overflow check (allow exact -2^63).
      if (e_unb > 63) begin
        o.flags |= AM9513_F_NV;
        o.v = s ? 64'h8000_0000_0000_0000 : 64'h7FFF_FFFF_FFFF_FFFF;
        fp64_to_int64 = o;
        return;
      end
      if (e_unb == 63) begin
        if (s && (f == 0)) o.v = 64'h8000_0000_0000_0000;
        else begin
          o.flags |= AM9513_F_NV;
          o.v = s ? 64'h8000_0000_0000_0000 : 64'h7FFF_FFFF_FFFF_FFFF;
        end
        fp64_to_int64 = o;
        return;
      end

      rem = '0;
      if (e_unb >= 52) begin
        int_mag = 64'(mant) << (e_unb - 52);
      end else begin
        sh = 52 - e_unb;
        int_mag = 64'(mant) >> sh;
        rem = mant[sh-1:0];
        if (rem != 0) o.flags |= AM9513_F_NX;
      end

      inc = 1'b0;
      if ((e_unb < 52) && (rem != 0)) begin
        unique case (rm)
          2'(CARBON_RND_RZ): inc = 1'b0;
          2'(CARBON_RND_RP): inc = (!s);
          2'(CARBON_RND_RM): inc = (s);
          default: begin
            logic [52:0] half;
            half = 53'(1) << ((52 - e_unb) - 1);
            if (rem > half) inc = 1'b1;
            else if (rem == half) inc = int_mag[0];
          end
        endcase
      end

      mag_rounded = int_mag + 64'(inc);
      if (!s) begin
        if (mag_rounded > 64'h7FFF_FFFF_FFFF_FFFF) begin
          o.flags |= AM9513_F_NV;
          o.v = 64'h7FFF_FFFF_FFFF_FFFF;
        end else begin
          o.v = mag_rounded;
        end
      end else begin
        if (mag_rounded > 64'h8000_0000_0000_0000) begin
          o.flags |= AM9513_F_NV;
          o.v = 64'h8000_0000_0000_0000;
        end else begin
          o.v = 64'(~mag_rounded + 1);
        end
      end

      fp64_to_int64 = o;
    end
  endfunction

  // --------------------------------------------------------------------------
  // Simple transcendental approximations (v1: fp32 primary; fp64 via fp32)
  // --------------------------------------------------------------------------
  localparam logic [31:0] FP32_ONE   = 32'h3F80_0000;
  localparam logic [31:0] FP32_HALF  = 32'h3F00_0000;
  localparam logic [31:0] FP32_LN2   = 32'h3F31_7218; // ~0.69314718
  localparam logic [31:0] FP32_PI    = 32'h4049_0FDB; // ~3.1415927
  localparam logic [31:0] FP32_INV6  = 32'h3E2A_AAAB; // 1/6
  localparam logic [31:0] FP32_INV24 = 32'h3D2A_AAAB; // 1/24
  localparam logic [31:0] FP32_INV3  = 32'h3EAA_AAAB; // 1/3
  localparam logic [31:0] FP32_INV4  = 32'h3E80_0000; // 1/4
  localparam logic [31:0] FP32_INV5  = 32'h3DCC_CCCD; // 1/5

  function automatic am9513_fp32_t fp32_exp(input logic [31:0] x, input logic [1:0] rm);
    // exp(x) ≈ 1 + x + x^2/2 + x^3/6 + x^4/24 (bounded-error v1 policy).
    am9513_fp32_t o;
    am9513_fp32_t x2, x3, x4;
    am9513_fp32_t t1, t2, t3, t4;
    begin
      x2 = fp32_mul(x, x, rm);
      x3 = fp32_mul(x2.v, x, rm);
      x4 = fp32_mul(x2.v, x2.v, rm);

      t1 = fp32_add(FP32_ONE, x, rm);
      t2 = fp32_add(t1.v, fp32_mul(x2.v, FP32_HALF, rm).v, rm);
      t3 = fp32_add(t2.v, fp32_mul(x3.v, FP32_INV6, rm).v, rm);
      t4 = fp32_add(t3.v, fp32_mul(x4.v, FP32_INV24, rm).v, rm);

      o = t4;
      o.flags |= x2.flags | x3.flags | x4.flags;
      fp32_exp = o;
    end
  endfunction

  function automatic am9513_fp32_t fp32_log(input logic [31:0] x, input logic [1:0] rm);
    // ln(x) for x>0: x=m*2^e, m in [1,2), u=m-1, ln(m)≈u-u^2/2+u^3/3-u^4/4
    am9513_fp32_t o;
    logic s;
    logic [7:0] e;
    logic [22:0] f;
    int signed e_unb;
    am9513_fp32_t m;
    am9513_fp32_t u;
    am9513_fp32_t u2, u3, u4;
    am9513_fp32_t ln_m;
    am9513_fp32_t term2, term3, term4;
    am9513_fp32_t e_fp;
    begin
      o.v = FP32_QNAN;
      o.flags = '0;

      s = x[31];
      e = x[30:23];
      f = x[22:0];

      if (e == 8'h00) begin
        if (f == 0) begin
          o.v = FP32_NEG_INF;
          o.flags |= AM9513_F_DZ;
        end else begin
          o.v = FP32_QNAN;
          o.flags |= AM9513_F_NV;
        end
        fp32_log = o;
        return;
      end

      if (e == 8'hFF) begin
        if (f == 0) o.v = x;
        else o.v = FP32_QNAN;
        fp32_log = o;
        return;
      end

      if (s) begin
        o.v = FP32_QNAN;
        o.flags |= AM9513_F_NV;
        fp32_log = o;
        return;
      end

      e_unb = int'(e) - 127;
      m.v = {1'b0, 8'(127), f};
      m.flags = '0;
      u = fp32_sub(m.v, FP32_ONE, rm);

      u2 = fp32_mul(u.v, u.v, rm);
      u3 = fp32_mul(u2.v, u.v, rm);
      u4 = fp32_mul(u2.v, u2.v, rm);

      term2 = fp32_mul(u2.v, FP32_HALF, rm);
      term3 = fp32_mul(u3.v, FP32_INV3, rm);
      term4 = fp32_mul(u4.v, FP32_INV4, rm);

      ln_m = fp32_sub(u.v, term2.v, rm);
      ln_m = fp32_add(ln_m.v, term3.v, rm);
      ln_m = fp32_sub(ln_m.v, term4.v, rm);

      e_fp = int32_to_fp32(32'(e_unb), rm);
      o = fp32_add(ln_m.v, fp32_mul(e_fp.v, FP32_LN2, rm).v, rm);
      o.flags |= u.flags | u2.flags | u3.flags | u4.flags;
      o.flags |= term2.flags | term3.flags | term4.flags | ln_m.flags | e_fp.flags;
      fp32_log = o;
    end
  endfunction

  function automatic am9513_fp32_t fp32_sin(input logic [31:0] x, input logic [1:0] rm);
    // v1: small-angle approximation sin(x)≈x-x^3/6.
    am9513_fp32_t x2, x3;
    am9513_fp32_t t;
    am9513_fp32_t o;
    begin
      x2 = fp32_mul(x, x, rm);
      x3 = fp32_mul(x2.v, x, rm);
      t = fp32_mul(x3.v, FP32_INV6, rm);
      o = fp32_sub(x, t.v, rm);
      o.flags |= x2.flags | x3.flags | t.flags;
      fp32_sin = o;
    end
  endfunction

  function automatic am9513_fp32_t fp32_cos(input logic [31:0] x, input logic [1:0] rm);
    // v1: small-angle approximation cos(x)≈1-x^2/2.
    am9513_fp32_t x2;
    am9513_fp32_t t;
    am9513_fp32_t o;
    begin
      x2 = fp32_mul(x, x, rm);
      t = fp32_mul(x2.v, FP32_HALF, rm);
      o = fp32_sub(FP32_ONE, t.v, rm);
      o.flags |= x2.flags | t.flags;
      fp32_cos = o;
    end
  endfunction

  function automatic am9513_fp32_t fp32_atan2(input logic [31:0] y, input logic [31:0] x, input logic [1:0] rm);
    // v1: atan2 via atan(z)≈z-z^3/3+z^5/5 with coarse quadrant correction.
    am9513_fp32_t o;
    am9513_fp32_t z, z2, z3, z5;
    am9513_fp32_t t3, t5;
    logic x_neg;
    logic y_neg;
    begin
      x_neg = x[31];
      y_neg = y[31];

      if ((x[30:0] == 31'h0) && (y[30:0] == 31'h0)) begin
        o.v = FP32_QNAN;
        o.flags = AM9513_F_NV;
        fp32_atan2 = o;
        return;
      end

      z = fp32_div(y, x, rm);
      z2 = fp32_mul(z.v, z.v, rm);
      z3 = fp32_mul(z2.v, z.v, rm);
      z5 = fp32_mul(z3.v, z2.v, rm);
      t3 = fp32_mul(z3.v, FP32_INV3, rm);
      t5 = fp32_mul(z5.v, FP32_INV5, rm);

      o = fp32_sub(z.v, t3.v, rm);
      o = fp32_add(o.v, t5.v, rm);
      o.flags |= z.flags | z2.flags | z3.flags | z5.flags | t3.flags | t5.flags;

      if (x_neg && !y_neg) o = fp32_add(o.v, FP32_PI, rm);
      else if (x_neg && y_neg) o = fp32_sub(o.v, FP32_PI, rm);

      fp32_atan2 = o;
    end
  endfunction

  function automatic am9513_fp32_t fp32_hypot(input logic [31:0] a, input logic [31:0] b, input logic [1:0] rm);
    am9513_fp32_t a2, b2, s, o;
    begin
      a2 = fp32_mul(a, a, rm);
      b2 = fp32_mul(b, b, rm);
      s  = fp32_add(a2.v, b2.v, rm);
      o  = fp32_sqrt(s.v, rm);
      o.flags |= a2.flags | b2.flags | s.flags;
      fp32_hypot = o;
    end
  endfunction

  function automatic am9513_fp32_t fp32_pow(input logic [31:0] a, input logic [31:0] b, input logic [1:0] rm);
    am9513_fp32_t ln, prod, o;
    begin
      ln = fp32_log(a, rm);
      prod = fp32_mul(ln.v, b, rm);
      o = fp32_exp(prod.v, rm);
      o.flags |= ln.flags | prod.flags;
      fp32_pow = o;
    end
  endfunction

  // --------------------------------------------------------------------------
  // Unified execute helper (format-aware; returns CAI status + bytes_written).
  // --------------------------------------------------------------------------
  function automatic int unsigned fmt_bytes(input logic [7:0] fmt);
    begin
      unique case (fmt)
        8'(CARBON_FMT_BINARY16): fmt_bytes = 2;
        8'(CARBON_FMT_BFLOAT16): fmt_bytes = 2;
        8'(CARBON_FMT_BINARY32): fmt_bytes = 4;
        default: fmt_bytes = 8;
      endcase
    end
  endfunction

  function automatic am9513_exec_result_t am9513_execute(
      input logic [7:0] func,
      input logic [7:0] fmt,
      input logic [31:0] submit_flags,
      input logic [63:0] op0,
      input logic [63:0] op1,
      input logic [63:0] op2,
      input logic [1:0] rm
  );
    am9513_exec_result_t r;
    am9513_fp32_t a32, b32, c32, res32, tmp32;
    am9513_fp64_t a64, b64, c64, res64, tmp64;
    logic [7:0] src_fmt;
    int signed cmp;
    begin
      r = '0;
      r.cai_status = 16'(CARBON_CAI_STATUS_OK);
      r.bytes_written = 32'(fmt_bytes(fmt));

      src_fmt = submit_flags[AM9513_SUBMIT_FLAG_CONV_SRC_FMT_LSB +: AM9513_SUBMIT_FLAG_CONV_SRC_FMT_WIDTH];

      // Helpers for operand decode into fp32.
      unique case (fmt)
        8'(CARBON_FMT_BINARY16): begin
          a32 = fp16_to_fp32(op0[15:0]);
          b32 = fp16_to_fp32(op1[15:0]);
          c32 = fp16_to_fp32(op2[15:0]);
        end
        8'(CARBON_FMT_BFLOAT16): begin
          a32 = bf16_to_fp32(op0[15:0]);
          b32 = bf16_to_fp32(op1[15:0]);
          c32 = bf16_to_fp32(op2[15:0]);
        end
        8'(CARBON_FMT_BINARY32): begin
          a32.v = op0[31:0]; a32.flags = '0;
          b32.v = op1[31:0]; b32.flags = '0;
          c32.v = op2[31:0]; c32.flags = '0;
        end
        default: begin
          a64.v = op0; a64.flags = '0;
          b64.v = op1; b64.flags = '0;
          c64.v = op2; c64.flags = '0;
          a32 = fp64_to_fp32(a64.v, rm);
          b32 = fp64_to_fp32(b64.v, rm);
          c32 = fp64_to_fp32(c64.v, rm);
        end
      endcase

      if (fmt != 8'(CARBON_FMT_BINARY64)) begin
        r.exc_flags |= a32.flags | b32.flags | c32.flags;
      end

      unique case (func)
        AM9513_FUNC_CONV: begin
          unique case (src_fmt)
            8'(CARBON_FMT_BINARY16): a32 = fp16_to_fp32(op0[15:0]);
            8'(CARBON_FMT_BFLOAT16): a32 = bf16_to_fp32(op0[15:0]);
            8'(CARBON_FMT_BINARY32): begin a32.v = op0[31:0]; a32.flags = '0; end
            default: a32 = fp64_to_fp32(op0, rm);
          endcase
          r.exc_flags |= a32.flags;

          unique case (fmt)
            8'(CARBON_FMT_BINARY16): begin
              res32 = fp32_to_fp16(a32.v, rm);
              r.res0[15:0] = res32.v[15:0];
              r.exc_flags |= res32.flags;
              r.bytes_written = 32'd2;
            end
            8'(CARBON_FMT_BFLOAT16): begin
              res32 = fp32_to_bf16(a32.v, rm);
              r.res0[15:0] = res32.v[15:0];
              r.exc_flags |= res32.flags;
              r.bytes_written = 32'd2;
            end
            8'(CARBON_FMT_BINARY32): begin
              r.res0[31:0] = a32.v;
              r.bytes_written = 32'd4;
            end
            default: begin
              tmp64 = fp32_to_fp64(a32.v);
              r.res0 = tmp64.v;
              r.exc_flags |= tmp64.flags;
              r.bytes_written = 32'd8;
            end
          endcase
        end

        AM9513_FUNC_I32_TO_F32: begin
          if (fmt != 8'(CARBON_FMT_BINARY32)) begin
            r.cai_status = 16'(CARBON_CAI_STATUS_INVALID_OP);
            am9513_execute = r;
            return;
          end
          res32 = int32_to_fp32(op0[31:0], rm);
          r.res0[31:0] = res32.v;
          r.exc_flags |= res32.flags;
          r.bytes_written = 32'd4;
          am9513_execute = r;
          return;
        end

        AM9513_FUNC_I64_TO_F64: begin
          if (fmt != 8'(CARBON_FMT_BINARY64)) begin
            r.cai_status = 16'(CARBON_CAI_STATUS_INVALID_OP);
            am9513_execute = r;
            return;
          end
          res64 = int64_to_fp64(op0, rm);
          r.res0 = res64.v;
          r.exc_flags |= res64.flags;
          r.bytes_written = 32'd8;
          am9513_execute = r;
          return;
        end

        AM9513_FUNC_F32_TO_I32: begin
          am9513_i32_t i32;
          if (fmt != 8'(CARBON_FMT_BINARY32)) begin
            r.cai_status = 16'(CARBON_CAI_STATUS_INVALID_OP);
            am9513_execute = r;
            return;
          end
          i32 = fp32_to_int32(op0[31:0], rm);
          r.res0[31:0] = i32.v;
          r.exc_flags |= i32.flags;
          r.bytes_written = 32'd4;
          am9513_execute = r;
          return;
        end

        AM9513_FUNC_F64_TO_I64: begin
          am9513_i64_t i64;
          if (fmt != 8'(CARBON_FMT_BINARY64)) begin
            r.cai_status = 16'(CARBON_CAI_STATUS_INVALID_OP);
            am9513_execute = r;
            return;
          end
          i64 = fp64_to_int64(op0, rm);
          r.res0 = i64.v;
          r.exc_flags |= i64.flags;
          r.bytes_written = 32'd8;
          am9513_execute = r;
          return;
        end

        AM9513_FUNC_ADD: begin
          if (fmt == 8'(CARBON_FMT_BINARY64)) res64 = fp64_add(op0, op1, rm);
          else begin res32 = fp32_add(a32.v, b32.v, rm); r.exc_flags |= res32.flags; end
        end
        AM9513_FUNC_SUB: begin
          if (fmt == 8'(CARBON_FMT_BINARY64)) res64 = fp64_sub(op0, op1, rm);
          else begin res32 = fp32_sub(a32.v, b32.v, rm); r.exc_flags |= res32.flags; end
        end
        AM9513_FUNC_MUL: begin
          if (fmt == 8'(CARBON_FMT_BINARY64)) res64 = fp64_mul(op0, op1, rm);
          else begin res32 = fp32_mul(a32.v, b32.v, rm); r.exc_flags |= res32.flags; end
        end
        AM9513_FUNC_DIV: begin
          if (fmt == 8'(CARBON_FMT_BINARY64)) res64 = fp64_div(op0, op1, rm);
          else begin res32 = fp32_div(a32.v, b32.v, rm); r.exc_flags |= res32.flags; end
        end
        AM9513_FUNC_SQRT: begin
          if (fmt == 8'(CARBON_FMT_BINARY64)) res64 = fp64_sqrt(op0, rm);
          else begin res32 = fp32_sqrt(a32.v, rm); r.exc_flags |= res32.flags; end
        end
        AM9513_FUNC_FMA: begin
          if (fmt == 8'(CARBON_FMT_BINARY64)) res64 = fp64_fma(op0, op1, op2, rm);
          else begin res32 = fp32_fma(a32.v, b32.v, c32.v, rm); r.exc_flags |= res32.flags; end
        end
        AM9513_FUNC_SIN: begin
          if (fmt == 8'(CARBON_FMT_BINARY64)) r.exc_flags |= a32.flags;
          res32 = fp32_sin(a32.v, rm);
          r.exc_flags |= res32.flags;
          if (fmt == 8'(CARBON_FMT_BINARY64)) begin
            res64 = fp32_to_fp64(res32.v);
            res64.flags |= res32.flags;
          end
        end
        AM9513_FUNC_COS: begin
          if (fmt == 8'(CARBON_FMT_BINARY64)) r.exc_flags |= a32.flags;
          res32 = fp32_cos(a32.v, rm);
          r.exc_flags |= res32.flags;
          if (fmt == 8'(CARBON_FMT_BINARY64)) begin
            res64 = fp32_to_fp64(res32.v);
            res64.flags |= res32.flags;
          end
        end
        AM9513_FUNC_SINCOS: begin
          if (fmt == 8'(CARBON_FMT_BINARY64)) r.exc_flags |= a32.flags;
          res32 = fp32_sin(a32.v, rm);
          tmp32 = fp32_cos(a32.v, rm);
          r.exc_flags |= res32.flags | tmp32.flags;
          if (fmt == 8'(CARBON_FMT_BINARY64)) begin
            tmp64 = fp32_to_fp64(res32.v);
            r.res0 = tmp64.v;
            tmp64 = fp32_to_fp64(tmp32.v);
            r.res1 = tmp64.v;
            r.res1_valid = 1'b1;
            r.bytes_written = 32'd16;
            am9513_execute = r;
            return;
          end else begin
            // Pack after formatting below.
            r.res1_valid = 1'b1;
            r.bytes_written = 32'(fmt_bytes(fmt)) * 2;
          end
        end
        AM9513_FUNC_EXP: begin
          if (fmt == 8'(CARBON_FMT_BINARY64)) r.exc_flags |= a32.flags;
          res32 = fp32_exp(a32.v, rm);
          r.exc_flags |= res32.flags;
          if (fmt == 8'(CARBON_FMT_BINARY64)) begin
            res64 = fp32_to_fp64(res32.v);
            res64.flags |= res32.flags;
          end
        end
        AM9513_FUNC_LOG: begin
          if (fmt == 8'(CARBON_FMT_BINARY64)) r.exc_flags |= a32.flags;
          res32 = fp32_log(a32.v, rm);
          r.exc_flags |= res32.flags;
          if (fmt == 8'(CARBON_FMT_BINARY64)) begin
            res64 = fp32_to_fp64(res32.v);
            res64.flags |= res32.flags;
          end
        end
        AM9513_FUNC_POW: begin
          if (fmt == 8'(CARBON_FMT_BINARY64)) r.exc_flags |= (a32.flags | b32.flags);
          res32 = fp32_pow(a32.v, b32.v, rm);
          r.exc_flags |= res32.flags;
          if (fmt == 8'(CARBON_FMT_BINARY64)) begin
            res64 = fp32_to_fp64(res32.v);
            res64.flags |= res32.flags;
          end
        end
        AM9513_FUNC_ATAN2: begin
          if (fmt == 8'(CARBON_FMT_BINARY64)) r.exc_flags |= (a32.flags | b32.flags);
          res32 = fp32_atan2(a32.v, b32.v, rm);
          r.exc_flags |= res32.flags;
          if (fmt == 8'(CARBON_FMT_BINARY64)) begin
            res64 = fp32_to_fp64(res32.v);
            res64.flags |= res32.flags;
          end
        end
        AM9513_FUNC_HYPOT: begin
          if (fmt == 8'(CARBON_FMT_BINARY64)) r.exc_flags |= (a32.flags | b32.flags);
          res32 = fp32_hypot(a32.v, b32.v, rm);
          r.exc_flags |= res32.flags;
          if (fmt == 8'(CARBON_FMT_BINARY64)) begin
            res64 = fp32_to_fp64(res32.v);
            res64.flags |= res32.flags;
          end
        end
        AM9513_FUNC_CMP: begin
          if (((a32.v[30:23] == 8'hFF) && (a32.v[22:0] != 0)) ||
              ((b32.v[30:23] == 8'hFF) && (b32.v[22:0] != 0))) begin
            r.exc_flags |= AM9513_F_NV;
            cmp = 0;
          end else if (a32.v == b32.v) begin
            cmp = 0;
          end else if ($signed(a32.v) < $signed(b32.v)) begin
            cmp = -1;
          end else begin
            cmp = 1;
          end
          r.res0[31:0] = 32'(cmp);
          r.bytes_written = 32'd4;
          am9513_execute = r;
          return;
        end
        AM9513_FUNC_MIN: begin
          r.res0[31:0] = ($signed(a32.v) < $signed(b32.v)) ? a32.v : b32.v;
          r.bytes_written = 32'(fmt_bytes(fmt));
          am9513_execute = r;
          return;
        end
        AM9513_FUNC_MAX: begin
          r.res0[31:0] = ($signed(a32.v) > $signed(b32.v)) ? a32.v : b32.v;
          r.bytes_written = 32'(fmt_bytes(fmt));
          am9513_execute = r;
          return;
        end
        AM9513_FUNC_CLASS: begin
          if ((a32.v[30:23] == 8'h00) && (a32.v[22:0] == 0)) cmp = 0;
          else if ((a32.v[30:23] == 8'hFF) && (a32.v[22:0] == 0)) cmp = 3;
          else if ((a32.v[30:23] == 8'hFF) && (a32.v[22:0] != 0)) cmp = 4;
          else if (a32.v[30:23] == 8'h00) cmp = 1;
          else cmp = 2;
          r.res0[31:0] = 32'(cmp);
          r.bytes_written = 32'd4;
          am9513_execute = r;
          return;
        end
        default: begin
          r.cai_status = 16'(CARBON_CAI_STATUS_INVALID_OP);
          am9513_execute = r;
          return;
        end
      endcase

      // Pack scalar results for non-CONV non-CLASS operations.
      if (func != AM9513_FUNC_CONV) begin
        if (fmt == 8'(CARBON_FMT_BINARY64)) begin
          r.res0 = res64.v;
          r.exc_flags |= res64.flags;
          r.bytes_written = 32'd8;
        end else begin
          // SINCOS uses res32+tmp32.
          if (func == AM9513_FUNC_SINCOS) begin
            unique case (fmt)
              8'(CARBON_FMT_BINARY16): begin
                r.res0[15:0] = fp32_to_fp16(res32.v, rm).v[15:0];
                r.res1[15:0] = fp32_to_fp16(tmp32.v, rm).v[15:0];
              end
              8'(CARBON_FMT_BFLOAT16): begin
                r.res0[15:0] = fp32_to_bf16(res32.v, rm).v[15:0];
                r.res1[15:0] = fp32_to_bf16(tmp32.v, rm).v[15:0];
              end
              default: begin
                r.res0[31:0] = res32.v;
                r.res1[31:0] = tmp32.v;
              end
            endcase
          end else begin
            unique case (fmt)
              8'(CARBON_FMT_BINARY16): begin
                tmp32 = fp32_to_fp16(res32.v, rm);
                r.res0[15:0] = tmp32.v[15:0];
                r.exc_flags |= tmp32.flags;
                r.bytes_written = 32'd2;
              end
              8'(CARBON_FMT_BFLOAT16): begin
                tmp32 = fp32_to_bf16(res32.v, rm);
                r.res0[15:0] = tmp32.v[15:0];
                r.exc_flags |= tmp32.flags;
                r.bytes_written = 32'd2;
              end
              default: begin
                r.res0[31:0] = res32.v;
                r.bytes_written = 32'd4;
              end
            endcase
          end
        end
      end

      am9513_execute = r;
    end
  endfunction

endpackage : am9513_math_pkg
