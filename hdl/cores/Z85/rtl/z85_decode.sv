// Project Carbon - Z85 core (strict Z80 engine)
// z85_decode: Prefix-aware decode helpers.
//
// This package provides common Z80 opcode field extraction and helpers for
// instruction classification. The core implements the prefix byte fetch loop
// (DD/FD/ED/CB and DD/FD+CB+d forms).

package z85_decode_pkg;
  import z85_regfile_pkg::*;

  typedef enum logic [1:0] {
    Z85_GRP_BASE = 2'd0,
    Z85_GRP_CB   = 2'd1,
    Z85_GRP_ED   = 2'd2,
    Z85_GRP_DDCB = 2'd3
  } z85_grp_e;

  typedef enum logic [2:0] {
    Z85_ALU_ADD = 3'd0,
    Z85_ALU_ADC = 3'd1,
    Z85_ALU_SUB = 3'd2,
    Z85_ALU_SBC = 3'd3,
    Z85_ALU_AND = 3'd4,
    Z85_ALU_XOR = 3'd5,
    Z85_ALU_OR  = 3'd6,
    Z85_ALU_CP  = 3'd7
  } z85_alu_op_e;

  function automatic logic [1:0] op_x(input logic [7:0] op);
    return op[7:6];
  endfunction

  function automatic logic [2:0] op_y(input logic [7:0] op);
    return op[5:3];
  endfunction

  function automatic logic [2:0] op_z(input logic [7:0] op);
    return op[2:0];
  endfunction

  function automatic logic [1:0] op_p(input logic [7:0] op);
    return op[5:4];
  endfunction

  function automatic logic op_q(input logic [7:0] op);
    return op[3];
  endfunction

  // Condition code evaluation for cc field (y).
  function automatic logic cond_true(input logic [2:0] cc, input logic [7:0] f);
    logic z, c, pv, s;
    begin
      z  = (f & Z85_F_Z) != 0;
      c  = (f & Z85_F_C) != 0;
      pv = (f & Z85_F_PV) != 0;
      s  = (f & Z85_F_S) != 0;
      unique case (cc)
        3'd0: cond_true = !z;   // NZ
        3'd1: cond_true = z;    // Z
        3'd2: cond_true = !c;   // NC
        3'd3: cond_true = c;    // C
        3'd4: cond_true = !pv;  // PO
        3'd5: cond_true = pv;   // PE
        3'd6: cond_true = !s;   // P
        default: cond_true = s; // M
      endcase
    end
  endfunction

  // Base opcode uses (HL) as an operand (i.e. r==6 in places where it means (HL)).
  // Used to determine if DD/FD require a displacement byte.
  function automatic logic base_uses_hl_indirect(input logic [7:0] op);
    logic [1:0] x;
    logic [2:0] y, z;
    begin
      x = op_x(op);
      y = op_y(op);
      z = op_z(op);
      base_uses_hl_indirect = 1'b0;

      // LD r,r (excluding HALT)
      if (x == 2'd1) begin
        if (!((y == 3'd6) && (z == 3'd6)) && ((y == 3'd6) || (z == 3'd6))) begin
          base_uses_hl_indirect = 1'b1;
        end
      end

      // INC/DEC r, LD r,n where r=(HL)
      if (x == 2'd0) begin
        if ((z == 3'd4 || z == 3'd5 || z == 3'd6) && (y == 3'd6)) begin
          base_uses_hl_indirect = 1'b1;
        end
      end

      // ALU A,r where r=(HL)
      if (x == 2'd2) begin
        if (z == 3'd6) begin
          base_uses_hl_indirect = 1'b1;
        end
      end
    end
  endfunction

  function automatic logic is_prefix_dd(input logic [7:0] op);
    return op == 8'hDD;
  endfunction

  function automatic logic is_prefix_fd(input logic [7:0] op);
    return op == 8'hFD;
  endfunction

  function automatic logic is_prefix_ed(input logic [7:0] op);
    return op == 8'hED;
  endfunction

  function automatic logic is_prefix_cb(input logic [7:0] op);
    return op == 8'hCB;
  endfunction

endpackage : z85_decode_pkg

