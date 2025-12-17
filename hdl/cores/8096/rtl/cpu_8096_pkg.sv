// Project Carbon - 8096 CPU core (v1.0)
// cpu_8096_pkg: Helpers for an 8086-compatible functional subset.

package cpu_8096_pkg;
  import carbon_arch_pkg::*;

  // FLAGS bit positions (8086-compatible layout; v1 uses a subset)
  localparam int unsigned X96_FLAG_CF_BIT = 0;
  localparam int unsigned X96_FLAG_PF_BIT = 2;
  localparam int unsigned X96_FLAG_AF_BIT = 4;
  localparam int unsigned X96_FLAG_ZF_BIT = 6;
  localparam int unsigned X96_FLAG_SF_BIT = 7;
  localparam int unsigned X96_FLAG_TF_BIT = 8;
  localparam int unsigned X96_FLAG_IF_BIT = 9;
  localparam int unsigned X96_FLAG_DF_BIT = 10;
  localparam int unsigned X96_FLAG_OF_BIT = 11;

  localparam logic [15:0] X96_FLAGS_RESET = 16'h0002;  // bit1 always 1

  typedef struct packed {
    logic [15:0] res;
    logic        cf;
    logic        pf;
    logic        af;
    logic        zf;
    logic        sf;
    logic        of;
  } x96_alu16_t;

  function automatic logic parity_even8(input logic [7:0] v);
    // PF=1 for even parity (even number of set bits).
    parity_even8 = ~^v;
  endfunction

  function automatic logic [15:0] sext8to16(input logic [7:0] v);
    sext8to16 = {{8{v[7]}}, v};
  endfunction

  function automatic x96_alu16_t alu_add16(input logic [15:0] a, input logic [15:0] b);
    x96_alu16_t o;
    logic [16:0] sum;
    begin
      sum   = {1'b0, a} + {1'b0, b};
      o.res = sum[15:0];
      o.cf  = sum[16];
      o.af  = (a[3:0] + b[3:0]) > 5'h0F;
      o.sf  = o.res[15];
      o.zf  = (o.res == 16'h0000);
      o.pf  = parity_even8(o.res[7:0]);
      o.of  = (~(a[15] ^ b[15])) & (a[15] ^ o.res[15]);
      alu_add16 = o;
    end
  endfunction

  function automatic x96_alu16_t alu_sub16(input logic [15:0] a, input logic [15:0] b);
    x96_alu16_t o;
    logic [16:0] diff;
    begin
      diff  = {1'b0, a} - {1'b0, b};
      o.res = diff[15:0];
      o.cf  = diff[16];  // borrow
      o.af  = (a[3:0] < b[3:0]);
      o.sf  = o.res[15];
      o.zf  = (o.res == 16'h0000);
      o.pf  = parity_even8(o.res[7:0]);
      o.of  = (a[15] ^ b[15]) & (a[15] ^ o.res[15]);
      alu_sub16 = o;
    end
  endfunction

  function automatic x96_alu16_t alu_and16(input logic [15:0] a, input logic [15:0] b);
    x96_alu16_t o;
    begin
      o.res = a & b;
      o.cf  = 1'b0;
      o.of  = 1'b0;
      o.af  = 1'b0;
      o.sf  = o.res[15];
      o.zf  = (o.res == 16'h0000);
      o.pf  = parity_even8(o.res[7:0]);
      alu_and16 = o;
    end
  endfunction

  function automatic x96_alu16_t alu_or16(input logic [15:0] a, input logic [15:0] b);
    x96_alu16_t o;
    begin
      o.res = a | b;
      o.cf  = 1'b0;
      o.of  = 1'b0;
      o.af  = 1'b0;
      o.sf  = o.res[15];
      o.zf  = (o.res == 16'h0000);
      o.pf  = parity_even8(o.res[7:0]);
      alu_or16 = o;
    end
  endfunction

  function automatic x96_alu16_t alu_xor16(input logic [15:0] a, input logic [15:0] b);
    x96_alu16_t o;
    begin
      o.res = a ^ b;
      o.cf  = 1'b0;
      o.of  = 1'b0;
      o.af  = 1'b0;
      o.sf  = o.res[15];
      o.zf  = (o.res == 16'h0000);
      o.pf  = parity_even8(o.res[7:0]);
      alu_xor16 = o;
    end
  endfunction

endpackage : cpu_8096_pkg

