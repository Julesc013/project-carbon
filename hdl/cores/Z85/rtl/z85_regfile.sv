// Project Carbon - Z85 core (strict Z80 engine)
// z85_regfile: Architectural state container and register selection helpers.

package z85_regfile_pkg;
  import carbon_arch_pkg::*;

  // Flag bits (F register)
  localparam logic [7:0] Z85_F_S  = 8'h80;
  localparam logic [7:0] Z85_F_Z  = 8'h40;
  localparam logic [7:0] Z85_F_Y  = 8'h20; // undocumented copy of bit 5
  localparam logic [7:0] Z85_F_H  = 8'h10;
  localparam logic [7:0] Z85_F_X  = 8'h08; // undocumented copy of bit 3
  localparam logic [7:0] Z85_F_PV = 8'h04;
  localparam logic [7:0] Z85_F_N  = 8'h02;
  localparam logic [7:0] Z85_F_C  = 8'h01;

  typedef enum logic [1:0] {
    Z85_IDX_NONE = 2'd0,
    Z85_IDX_IX   = 2'd1,
    Z85_IDX_IY   = 2'd2
  } z85_idx_sel_e;

  typedef struct packed {
    // Main set
    logic [7:0] A;
    logic [7:0] F;
    logic [7:0] B, C;
    logic [7:0] D, E;
    logic [7:0] H, L;

    // Alternate set
    logic [7:0] A2;
    logic [7:0] F2;
    logic [7:0] B2, C2;
    logic [7:0] D2, E2;
    logic [7:0] H2, L2;

    // Index and pointers
    logic [15:0] IX;
    logic [15:0] IY;
    logic [15:0] SP;
    logic [15:0] PC;

    // Interrupt/vector and refresh
    logic [7:0] I;
    logic [7:0] R;
    logic       IFF1;
    logic       IFF2;
    logic [1:0] IM;

    logic halt_latch;

    // Internal helper (WZ register used by some instructions)
    logic [15:0] WZ;
  } z85_state_t;

  function automatic logic [15:0] pack16(input logic [7:0] hi, input logic [7:0] lo);
    return {hi, lo};
  endfunction

  function automatic logic [7:0] hi8(input logic [15:0] v);
    return v[15:8];
  endfunction

  function automatic logic [7:0] lo8(input logic [15:0] v);
    return v[7:0];
  endfunction

  function automatic logic [15:0] get_HL(input z85_state_t s);
    return pack16(s.H, s.L);
  endfunction

  function automatic void set_HL(inout z85_state_t s, input logic [15:0] v);
    s.H = v[15:8];
    s.L = v[7:0];
  endfunction

  function automatic logic [7:0] get_IXH(input z85_state_t s);
    return s.IX[15:8];
  endfunction
  function automatic logic [7:0] get_IXL(input z85_state_t s);
    return s.IX[7:0];
  endfunction
  function automatic void set_IXH(inout z85_state_t s, input logic [7:0] v);
    s.IX[15:8] = v;
  endfunction
  function automatic void set_IXL(inout z85_state_t s, input logic [7:0] v);
    s.IX[7:0] = v;
  endfunction

  function automatic logic [7:0] get_IYH(input z85_state_t s);
    return s.IY[15:8];
  endfunction
  function automatic logic [7:0] get_IYL(input z85_state_t s);
    return s.IY[7:0];
  endfunction
  function automatic void set_IYH(inout z85_state_t s, input logic [7:0] v);
    s.IY[15:8] = v;
  endfunction
  function automatic void set_IYL(inout z85_state_t s, input logic [7:0] v);
    s.IY[7:0] = v;
  endfunction

  // 8-bit register selection (r field in opcodes).
  // r: 0=B 1=C 2=D 3=E 4=H 5=L 6=(HL) 7=A
  function automatic logic [7:0] get_r8(input z85_state_t s, input logic [2:0] r, input z85_idx_sel_e idx);
    unique case (r)
      3'd0: return s.B;
      3'd1: return s.C;
      3'd2: return s.D;
      3'd3: return s.E;
      3'd4: begin
        unique case (idx)
          Z85_IDX_IX: return get_IXH(s);
          Z85_IDX_IY: return get_IYH(s);
          default:    return s.H;
        endcase
      end
      3'd5: begin
        unique case (idx)
          Z85_IDX_IX: return get_IXL(s);
          Z85_IDX_IY: return get_IYL(s);
          default:    return s.L;
        endcase
      end
      3'd7: return s.A;
      default: return 8'h00; // (HL) handled by executor
    endcase
  endfunction

  function automatic void set_r8(
      inout z85_state_t s,
      input logic [2:0] r,
      input z85_idx_sel_e idx,
      input logic [7:0] v
  );
    unique case (r)
      3'd0: s.B = v;
      3'd1: s.C = v;
      3'd2: s.D = v;
      3'd3: s.E = v;
      3'd4: begin
        unique case (idx)
          Z85_IDX_IX: set_IXH(s, v);
          Z85_IDX_IY: set_IYH(s, v);
          default:    s.H = v;
        endcase
      end
      3'd5: begin
        unique case (idx)
          Z85_IDX_IX: set_IXL(s, v);
          Z85_IDX_IY: set_IYL(s, v);
          default:    s.L = v;
        endcase
      end
      3'd7: s.A = v;
      default: begin end
    endcase
  endfunction

  // 16-bit register selection for "ss" field: 0=BC 1=DE 2=HL/IX/IY 3=SP
  function automatic logic [15:0] get_ss(input z85_state_t s, input logic [1:0] ss, input z85_idx_sel_e idx);
    unique case (ss)
      2'd0: return pack16(s.B, s.C);
      2'd1: return pack16(s.D, s.E);
      2'd2: begin
        unique case (idx)
          Z85_IDX_IX: return s.IX;
          Z85_IDX_IY: return s.IY;
          default:    return get_HL(s);
        endcase
      end
      default: return s.SP;
    endcase
  endfunction

  function automatic void set_ss(
      inout z85_state_t s,
      input logic [1:0] ss,
      input z85_idx_sel_e idx,
      input logic [15:0] v
  );
    unique case (ss)
      2'd0: begin s.B = v[15:8]; s.C = v[7:0]; end
      2'd1: begin s.D = v[15:8]; s.E = v[7:0]; end
      2'd2: begin
        unique case (idx)
          Z85_IDX_IX: s.IX = v;
          Z85_IDX_IY: s.IY = v;
          default:    set_HL(s, v);
        endcase
      end
      default: s.SP = v;
    endcase
  endfunction

  // 16-bit register selection for "pp" field used by PUSH/POP: 0=BC 1=DE 2=HL/IX/IY 3=AF
  function automatic logic [15:0] get_pp(input z85_state_t s, input logic [1:0] pp, input z85_idx_sel_e idx);
    unique case (pp)
      2'd0: return pack16(s.B, s.C);
      2'd1: return pack16(s.D, s.E);
      2'd2: begin
        unique case (idx)
          Z85_IDX_IX: return s.IX;
          Z85_IDX_IY: return s.IY;
          default:    return get_HL(s);
        endcase
      end
      default: return pack16(s.A, s.F);
    endcase
  endfunction

  function automatic void set_pp(
      inout z85_state_t s,
      input logic [1:0] pp,
      input z85_idx_sel_e idx,
      input logic [15:0] v
  );
    unique case (pp)
      2'd0: begin s.B = v[15:8]; s.C = v[7:0]; end
      2'd1: begin s.D = v[15:8]; s.E = v[7:0]; end
      2'd2: begin
        unique case (idx)
          Z85_IDX_IX: s.IX = v;
          Z85_IDX_IY: s.IY = v;
          default:    set_HL(s, v);
        endcase
      end
      default: begin s.A = v[15:8]; s.F = v[7:0]; end
    endcase
  endfunction

  function automatic logic [15:0] hl_eff_addr(
      input z85_state_t s,
      input z85_idx_sel_e idx,
      input logic signed [7:0] disp
  );
    logic signed [16:0] tmp;
    begin
      unique case (idx)
        Z85_IDX_IX: tmp = $signed({1'b0, s.IX}) + $signed({{9{disp[7]}}, disp});
        Z85_IDX_IY: tmp = $signed({1'b0, s.IY}) + $signed({{9{disp[7]}}, disp});
        default:    tmp = $signed({1'b0, get_HL(s)});
      endcase
      hl_eff_addr = tmp[15:0];
    end
  endfunction

  function automatic void r_inc_on_opcode_fetch(inout z85_state_t s);
    // Approximation: increment low 7 bits on each opcode/prefix fetch; preserve bit 7.
    s.R[6:0] = s.R[6:0] + 7'd1;
  endfunction

endpackage : z85_regfile_pkg

