// Project Carbon - Z90 core (Z180-class integration helpers)
// z90_alu_pkg: Simple 16-bit ALU helpers and Z90 flag definitions.

package z90_alu_pkg;

  // Z90 FLAGS (legacy fast-path encoding; unused by the Z180-class core)
  // - Bits not listed are reserved and read as 0.
  localparam logic [7:0] Z90_F_Z = 8'h01; // Zero
  localparam logic [7:0] Z90_F_S = 8'h02; // Sign (MSB of result)
  localparam logic [7:0] Z90_F_C = 8'h04; // Carry / borrow
  localparam logic [7:0] Z90_F_V = 8'h08; // Signed overflow

  typedef struct packed {
    logic [15:0] res;
    logic [7:0]  f;
  } z90_alu16_t;

  function automatic logic _ov_add16(input logic [15:0] a, input logic [15:0] b, input logic [15:0] r);
    return (((~(a ^ b)) & (a ^ r)) & 16'h8000) != 0;
  endfunction

  function automatic logic _ov_sub16(input logic [15:0] a, input logic [15:0] b, input logic [15:0] r);
    return (((a ^ b) & (a ^ r)) & 16'h8000) != 0;
  endfunction

  function automatic logic [7:0] _flags_sz(input logic [15:0] r);
    logic [7:0] f;
    begin
      f = 8'h00;
      if (r == 16'h0000) f |= Z90_F_Z;
      if (r[15])         f |= Z90_F_S;
      _flags_sz = f;
    end
  endfunction

  function automatic z90_alu16_t alu_add16(input logic [15:0] a, input logic [15:0] b);
    logic [16:0] sum;
    z90_alu16_t o;
    begin
      sum = {1'b0, a} + {1'b0, b};
      o.res = sum[15:0];
      o.f   = _flags_sz(o.res);
      if (sum[16]) o.f |= Z90_F_C;
      if (_ov_add16(a, b, o.res)) o.f |= Z90_F_V;
      alu_add16 = o;
    end
  endfunction

  function automatic z90_alu16_t alu_sub16(input logic [15:0] a, input logic [15:0] b);
    logic [16:0] diff;
    z90_alu16_t o;
    begin
      diff = {1'b0, a} - {1'b0, b};
      o.res = diff[15:0];
      o.f   = _flags_sz(o.res);
      if (diff[16]) o.f |= Z90_F_C; // borrow
      if (_ov_sub16(a, b, o.res)) o.f |= Z90_F_V;
      alu_sub16 = o;
    end
  endfunction

  function automatic z90_alu16_t alu_and16(input logic [15:0] a, input logic [15:0] b);
    z90_alu16_t o;
    begin
      o.res = a & b;
      o.f   = _flags_sz(o.res);
      alu_and16 = o;
    end
  endfunction

  function automatic z90_alu16_t alu_or16(input logic [15:0] a, input logic [15:0] b);
    z90_alu16_t o;
    begin
      o.res = a | b;
      o.f   = _flags_sz(o.res);
      alu_or16 = o;
    end
  endfunction

  function automatic z90_alu16_t alu_xor16(input logic [15:0] a, input logic [15:0] b);
    z90_alu16_t o;
    begin
      o.res = a ^ b;
      o.f   = _flags_sz(o.res);
      alu_xor16 = o;
    end
  endfunction

endpackage : z90_alu_pkg
