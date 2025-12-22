// Project Carbon - Z85 core reference model (simulation only)
// z85_ref_model: Slow, simple behavioral model used for TB comparison.

module z85_ref_model;
  import z85_regfile_pkg::*;
  import z85_decode_pkg::*;
  import z85_flags_pkg::*;

  // Public state (TBs may compare directly).
  z85_state_t s;

  logic        trapped;
  logic        ei_delay;
  logic [31:0] cause;
  logic [31:0] epc;

  // 64 KiB flat memory for model.
  logic [7:0] mem [0:65535];
  // 64 KiB I/O space model (port address is 16-bit).
  logic [7:0] io_mem [0:65535];

  // --------------------------------------------------------------------------
  // Helpers
  // --------------------------------------------------------------------------
  function automatic logic [7:0] rd8(input logic [15:0] addr);
    return mem[addr];
  endfunction

  task automatic wr8(input logic [15:0] addr, input logic [7:0] v);
    mem[addr] = v;
  endtask

  function automatic logic [7:0] rdio(input logic [15:0] port);
    return io_mem[port];
  endfunction

  task automatic wrio(input logic [15:0] port, input logic [7:0] v);
    io_mem[port] = v;
  endtask

  task automatic push16(input logic [15:0] v);
    s.SP = s.SP - 16'd1;
    wr8(s.SP, v[15:8]);
    s.SP = s.SP - 16'd1;
    wr8(s.SP, v[7:0]);
  endtask

  task automatic pop16(output logic [15:0] v);
    logic [7:0] lo, hi;
    begin
      lo = rd8(s.SP);
      s.SP = s.SP + 16'd1;
      hi = rd8(s.SP);
      s.SP = s.SP + 16'd1;
      v = {hi, lo};
    end
  endtask

  function automatic logic [15:0] rd16(input logic [15:0] addr);
    logic [7:0] lo, hi;
    begin
      lo = rd8(addr);
      hi = rd8(addr + 16'd1);
      rd16 = {hi, lo};
    end
  endfunction

  // --------------------------------------------------------------------------
  // Control
  // --------------------------------------------------------------------------
  task automatic reset_model();
    int i;
    begin
      s = '0;
      s.SP = 16'hFFFE;
      s.PC = 16'h0000;
      s.IM = 2'd0;
      s.halt_latch = 1'b0;
      trapped = 1'b0;
      ei_delay = 1'b0;
      cause = '0;
      epc = '0;
      for (i = 0; i < 65536; i++) mem[i] = 8'h00;
      for (i = 0; i < 65536; i++) io_mem[i] = 8'h00;
    end
  endtask

  // --------------------------------------------------------------------------
  // Execute one boundary event: either take an interrupt or retire one insn.
  // irq_is_nmi is an out-of-band indicator (mirrors z85_core modeling choice).
  // --------------------------------------------------------------------------
  task automatic step(input logic irq_valid, input logic irq_is_nmi, input logic [7:0] irq_byte);
    logic inhibit_int;
    logic inject_im0;
    logic [15:0] start_pc;
    z85_idx_sel_e idx;
    z85_grp_e grp;
    logic signed [7:0] disp;
    logic [7:0] op;
    begin
      if (trapped) return;

      inhibit_int = ei_delay;
      if (ei_delay) ei_delay = 1'b0;
      inject_im0 = 1'b0;

      // Interrupt sampling at boundary.
      if (irq_valid && irq_is_nmi) begin
        s.halt_latch = 1'b0;
        s.IFF2 = s.IFF1;
        s.IFF1 = 1'b0;
        push16(s.PC);
        s.PC = 16'h0066;
        return;
      end
      if (irq_valid && !irq_is_nmi && s.IFF1 && !inhibit_int) begin
        s.halt_latch = 1'b0;
        s.IFF1 = 1'b0;
        s.IFF2 = 1'b0;
        push16(s.PC);
        unique case (s.IM)
          2'd1: begin
            s.PC = 16'h0038;
            return;
          end
          2'd2: begin
            s.PC = rd16({s.I, irq_byte});
            return;
          end
          default: begin
            // IM0: execute injected opcode without consuming memory.
            inject_im0 = 1'b1;
            op = irq_byte;
            r_inc_on_opcode_fetch(s);
          end
        endcase
      end

      if (s.halt_latch) return;

      start_pc = s.PC;

      // Prefix/opcode fetch loop.
      idx = Z85_IDX_NONE;
      grp = Z85_GRP_BASE;
      disp = 8'sd0;

      forever begin
        if (!inject_im0) begin
          op = rd8(s.PC);
          s.PC = s.PC + 16'd1;
          r_inc_on_opcode_fetch(s);
        end
        inject_im0 = 1'b0;

        if (op == 8'hDD) begin idx = Z85_IDX_IX; continue; end
        if (op == 8'hFD) begin idx = Z85_IDX_IY; continue; end
        if (op == 8'hED) begin
          grp = Z85_GRP_ED;
          idx = Z85_IDX_NONE;
          op = rd8(s.PC);
          s.PC = s.PC + 16'd1;
          r_inc_on_opcode_fetch(s);
          break;
        end
        if (op == 8'hCB) begin
          if (idx == Z85_IDX_NONE) begin
            grp = Z85_GRP_CB;
            op = rd8(s.PC);
            s.PC = s.PC + 16'd1;
            r_inc_on_opcode_fetch(s);
            break;
          end else begin
            grp = Z85_GRP_DDCB;
            disp = $signed(rd8(s.PC));
            s.PC = s.PC + 16'd1;
            op = rd8(s.PC);
            s.PC = s.PC + 16'd1;
            r_inc_on_opcode_fetch(s);
            break;
          end
        end

        grp = Z85_GRP_BASE;
        break;
      end

      // Indexed base ops that use (HL) consume a displacement.
      if (grp == Z85_GRP_BASE && idx != Z85_IDX_NONE && base_uses_hl_indirect(op)) begin
        disp = $signed(rd8(s.PC));
        s.PC = s.PC + 16'd1;
      end

      // Execute Z80 instruction semantics.
      unique case (grp)
        Z85_GRP_BASE: begin
          logic [1:0] x;
          logic [2:0] y, z;
          logic [1:0] p;
          logic q;
          logic [15:0] ea;
          logic [15:0] nn;
          logic [7:0] n;
          logic signed [7:0] rel;
          logic [15:0] tmp16;
          z85_alu8_t o8;
          z85_alu16_t o16;
          x = op_x(op);
          y = op_y(op);
          z = op_z(op);
          p = op_p(op);
          q = op_q(op);
          ea = hl_eff_addr(s, idx, disp);

          unique case (x)
            2'd0: begin
              unique case (z)
                3'd0: begin
                  unique case (y)
                    3'd0: begin end // NOP
                    3'd1: begin // EX AF,AF'
                      {s.A, s.F, s.A2, s.F2} = {s.A2, s.F2, s.A, s.F};
                    end
                    3'd2: begin // DJNZ
                      rel = $signed(rd8(s.PC));
                      s.PC = s.PC + 16'd1;
                      s.B = s.B - 8'd1;
                      if (s.B != 8'h00) s.PC = s.PC + rel;
                    end
                    3'd3: begin // JR
                      rel = $signed(rd8(s.PC));
                      s.PC = s.PC + 16'd1;
                      s.PC = s.PC + rel;
                    end
                    default: begin // JR cc
                      rel = $signed(rd8(s.PC));
                      s.PC = s.PC + 16'd1;
                      if (cond_true(y - 3'd4, s.F)) s.PC = s.PC + rel;
                    end
                  endcase
                end
                3'd1: begin
                  if (!q) begin
                    nn = rd16(s.PC);
                    s.PC = s.PC + 16'd2;
                    set_ss(s, p, idx, nn);
                  end else begin
                    o16 = alu_add16_hl(get_ss(s, 2'd2, idx), get_ss(s, p, idx), s.F);
                    set_ss(s, 2'd2, idx, o16.res);
                    s.F = o16.f;
                  end
                end
                3'd2: begin
                  unique case (p)
                    2'd0: begin
                      if (!q) wr8(pack16(s.B, s.C), s.A);
                      else s.A = rd8(pack16(s.B, s.C));
                    end
                    2'd1: begin
                      if (!q) wr8(pack16(s.D, s.E), s.A);
                      else s.A = rd8(pack16(s.D, s.E));
                    end
                    2'd2: begin
                      nn = rd16(s.PC);
                      s.PC = s.PC + 16'd2;
                      if (!q) begin
                        tmp16 = get_ss(s, 2'd2, idx);
                        wr8(nn, tmp16[7:0]);
                        wr8(nn + 16'd1, tmp16[15:8]);
                      end else begin
                        tmp16 = rd16(nn);
                        set_ss(s, 2'd2, idx, tmp16);
                      end
                    end
                    default: begin
                      nn = rd16(s.PC);
                      s.PC = s.PC + 16'd2;
                      if (!q) wr8(nn, s.A);
                      else s.A = rd8(nn);
                    end
                  endcase
                end
                3'd3: begin
                  if (!q) set_ss(s, p, idx, get_ss(s, p, idx) + 16'd1);
                  else set_ss(s, p, idx, get_ss(s, p, idx) - 16'd1);
                end
                3'd4: begin
                  if (y == 3'd6) begin
                    o8 = alu_inc8(rd8(ea), s.F);
                    wr8(ea, o8.res);
                    s.F = o8.f;
                  end else begin
                    o8 = alu_inc8(get_r8(s, y, idx), s.F);
                    set_r8(s, y, idx, o8.res);
                    s.F = o8.f;
                  end
                end
                3'd5: begin
                  if (y == 3'd6) begin
                    o8 = alu_dec8(rd8(ea), s.F);
                    wr8(ea, o8.res);
                    s.F = o8.f;
                  end else begin
                    o8 = alu_dec8(get_r8(s, y, idx), s.F);
                    set_r8(s, y, idx, o8.res);
                    s.F = o8.f;
                  end
                end
                3'd6: begin
                  n = rd8(s.PC);
                  s.PC = s.PC + 16'd1;
                  if (y == 3'd6) wr8(ea, n);
                  else set_r8(s, y, idx, n);
                end
                3'd7: begin
                  unique case (y)
                    3'd0: begin // RLCA
                      logic c;
                      c = s.A[7];
                      s.A = {s.A[6:0], s.A[7]};
                      s.F = flags_rlca_rrca_rla_rra(s.F, s.A, c);
                    end
                    3'd1: begin // RRCA
                      logic c;
                      c = s.A[0];
                      s.A = {s.A[0], s.A[7:1]};
                      s.F = flags_rlca_rrca_rla_rra(s.F, s.A, c);
                    end
                    3'd2: begin // RLA
                      logic c;
                      c = s.A[7];
                      s.A = {s.A[6:0], (s.F & Z85_F_C) != 0};
                      s.F = flags_rlca_rrca_rla_rra(s.F, s.A, c);
                    end
                    3'd3: begin // RRA
                      logic c;
                      c = s.A[0];
                      s.A = {(s.F & Z85_F_C) != 0, s.A[7:1]};
                      s.F = flags_rlca_rrca_rla_rra(s.F, s.A, c);
                    end
                    3'd4: begin // DAA
                      o8 = alu_daa(s.A, s.F);
                      s.A = o8.res;
                      s.F = o8.f;
                    end
                    3'd5: begin // CPL
                      s.A = ~s.A;
                      s.F = flags_cpl(s.F, s.A);
                    end
                    3'd6: begin // SCF
                      s.F = flags_scf(s.F, s.A);
                    end
                    default: begin // CCF
                      s.F = flags_ccf(s.F, s.A);
                    end
                  endcase
                end
              endcase
            end
            2'd1: begin
              if (y == 3'd6 && z == 3'd6) begin
                s.halt_latch = 1'b1;
              end else if (y == 3'd6) begin
                wr8(ea, get_r8(s, z, idx));
              end else if (z == 3'd6) begin
                set_r8(s, y, idx, rd8(ea));
              end else begin
                set_r8(s, y, idx, get_r8(s, z, idx));
              end
            end
            2'd2: begin
              logic [7:0] v;
              v = (z == 3'd6) ? rd8(ea) : get_r8(s, z, idx);
              unique case (y)
                3'd0: o8 = alu_add8(s.A, v);
                3'd1: o8 = alu_adc8(s.A, v, (s.F & Z85_F_C) != 0);
                3'd2: o8 = alu_sub8(s.A, v);
                3'd3: o8 = alu_sbc8(s.A, v, (s.F & Z85_F_C) != 0);
                3'd4: o8 = alu_and8(s.A, v);
                3'd5: o8 = alu_xor8(s.A, v);
                3'd6: o8 = alu_or8(s.A, v);
                default: o8 = alu_cp8(s.A, v, s.F);
              endcase
              if (y == 3'd7) begin
                s.F = o8.f;
              end else begin
                s.A = o8.res;
                s.F = o8.f;
              end
            end
            default: begin
              unique case (z)
                3'd0: begin
                  if (cond_true(y, s.F)) begin
                    pop16(tmp16);
                    s.PC = tmp16;
                  end
                end
                3'd1: begin
                  if (!q) begin
                    pop16(tmp16);
                    if (p == 2'd3) begin
                      s.A = tmp16[15:8];
                      s.F = tmp16[7:0];
                    end else begin
                      set_pp(s, p, idx, tmp16);
                    end
                  end else begin
                    unique case (p)
                      2'd0: begin
                        pop16(tmp16);
                        s.PC = tmp16;
                      end
                      2'd1: begin
                        {s.B, s.C, s.D, s.E, s.H, s.L, s.B2, s.C2, s.D2, s.E2, s.H2, s.L2} =
                            {s.B2, s.C2, s.D2, s.E2, s.H2, s.L2, s.B, s.C, s.D, s.E, s.H, s.L};
                      end
                      2'd2: begin
                        s.PC = get_ss(s, 2'd2, idx);
                      end
                      default: begin
                        s.SP = get_ss(s, 2'd2, idx);
                      end
                    endcase
                  end
                end
                3'd2: begin
                  nn = rd16(s.PC);
                  s.PC = s.PC + 16'd2;
                  if (cond_true(y, s.F)) s.PC = nn;
                end
                3'd3: begin
                  unique case (y)
                    3'd0: begin
                      nn = rd16(s.PC);
                      s.PC = nn;
                    end
                    3'd2: begin
                      n = rd8(s.PC);
                      s.PC = s.PC + 16'd1;
                      wrio({s.A, n}, s.A);
                    end
                    3'd3: begin
                      n = rd8(s.PC);
                      s.PC = s.PC + 16'd1;
                      s.A = rdio({s.A, n});
                      o8 = alu_in8_flags(s.A, s.F);
                      s.F = o8.f;
                    end
                    3'd4: begin
                      tmp16 = rd16(s.SP);
                      wr8(s.SP, get_ss(s, 2'd2, idx)[7:0]);
                      wr8(s.SP + 16'd1, get_ss(s, 2'd2, idx)[15:8]);
                      set_ss(s, 2'd2, idx, tmp16);
                    end
                    3'd5: begin
                      tmp16 = get_ss(s, 2'd2, idx);
                      set_ss(s, 2'd2, idx, pack16(s.D, s.E));
                      s.D = tmp16[15:8];
                      s.E = tmp16[7:0];
                    end
                    3'd6: begin
                      s.IFF1 = 1'b0;
                      s.IFF2 = 1'b0;
                      ei_delay = 1'b0;
                    end
                    default: begin
                      s.IFF1 = 1'b1;
                      s.IFF2 = 1'b1;
                      ei_delay = 1'b1;
                    end
                  endcase
                end
                3'd4: begin
                  nn = rd16(s.PC);
                  s.PC = s.PC + 16'd2;
                  if (cond_true(y, s.F)) begin
                    push16(s.PC);
                    s.PC = nn;
                  end
                end
                3'd5: begin
                  if (!q) begin
                    tmp16 = (p == 2'd3) ? pack16(s.A, s.F) : get_pp(s, p, idx);
                    push16(tmp16);
                  end else if (p == 2'd0) begin
                    nn = rd16(s.PC);
                    s.PC = s.PC + 16'd2;
                    push16(s.PC);
                    s.PC = nn;
                  end
                end
                3'd6: begin
                  n = rd8(s.PC);
                  s.PC = s.PC + 16'd1;
                  unique case (y)
                    3'd0: o8 = alu_add8(s.A, n);
                    3'd1: o8 = alu_adc8(s.A, n, (s.F & Z85_F_C) != 0);
                    3'd2: o8 = alu_sub8(s.A, n);
                    3'd3: o8 = alu_sbc8(s.A, n, (s.F & Z85_F_C) != 0);
                    3'd4: o8 = alu_and8(s.A, n);
                    3'd5: o8 = alu_xor8(s.A, n);
                    3'd6: o8 = alu_or8(s.A, n);
                    default: o8 = alu_cp8(s.A, n, s.F);
                  endcase
                  if (y == 3'd7) s.F = o8.f;
                  else begin
                    s.A = o8.res;
                    s.F = o8.f;
                  end
                end
                default: begin
                  push16(s.PC);
                  s.PC = {5'b0, y, 3'b000};
                end
              endcase
            end
          endcase
        end

        Z85_GRP_CB, Z85_GRP_DDCB: begin
          logic [1:0] x;
          logic [2:0] y, z;
          logic [7:0] v;
          logic [7:0] res;
          z85_alu8_t o2;
          logic [15:0] ea;
          x = op_x(op);
          y = op_y(op);
          z = op_z(op);
          ea = (grp == Z85_GRP_DDCB) ? hl_eff_addr(s, idx, disp) : get_HL(s);
          v = (grp == Z85_GRP_DDCB || z == 3'd6) ? rd8(ea) : get_r8(s, z, Z85_IDX_NONE);

          if (x == 2'd0) begin
            o2 = alu_rotshift(y, v, s.F);
            res = o2.res;
            s.F = o2.f;
            if (grp == Z85_GRP_DDCB && z != 3'd6) set_r8(s, z, Z85_IDX_NONE, res);
            if (grp == Z85_GRP_DDCB || z == 3'd6) wr8(ea, res);
            else set_r8(s, z, Z85_IDX_NONE, res);
          end else if (x == 2'd1) begin
            s.F = flags_bitop(y, v, s.F, (grp == Z85_GRP_DDCB) ? ea[15:8] : v);
          end else if (x == 2'd2 || x == 2'd3) begin
            res = v;
            res[y] = (x == 2'd3);
            if (grp == Z85_GRP_DDCB && z != 3'd6) set_r8(s, z, Z85_IDX_NONE, res);
            if (grp == Z85_GRP_DDCB || z == 3'd6) wr8(ea, res);
            else set_r8(s, z, Z85_IDX_NONE, res);
          end
        end

        Z85_GRP_ED: begin
          logic [15:0] nn;
          logic [15:0] rr;
          logic [7:0] v;
          logic [7:0] f;
          z85_alu8_t o2;
          z85_alu16_t o16;

          if ((op & 8'hC7) == 8'h40) begin
            v = rdio({s.B, s.C});
            o2 = alu_in8_flags(v, s.F);
            s.F = o2.f;
            if (op[5:3] != 3'd6) set_r8(s, op[5:3], Z85_IDX_NONE, v);
          end else if ((op & 8'hC7) == 8'h41) begin
            v = (op[5:3] == 3'd6) ? 8'h00 : get_r8(s, op[5:3], Z85_IDX_NONE);
            wrio({s.B, s.C}, v);
          end else if ((op & 8'hCF) == 8'h43) begin
            nn = rd16(s.PC);
            s.PC = s.PC + 16'd2;
            rr = get_ss(s, op[5:4], Z85_IDX_NONE);
            wr8(nn, rr[7:0]);
            wr8(nn + 16'd1, rr[15:8]);
          end else if ((op & 8'hCF) == 8'h4B) begin
            nn = rd16(s.PC);
            s.PC = s.PC + 16'd2;
            rr = rd16(nn);
            set_ss(s, op[5:4], Z85_IDX_NONE, rr);
          end else if ((op & 8'hCF) == 8'h42) begin
            rr = get_ss(s, op[5:4], Z85_IDX_NONE);
            o16 = alu_sbc16_hl(get_HL(s), rr, (s.F & Z85_F_C) != 0);
            set_HL(s, o16.res);
            s.F = o16.f;
          end else if ((op & 8'hCF) == 8'h4A) begin
            rr = get_ss(s, op[5:4], Z85_IDX_NONE);
            o16 = alu_adc16_hl(get_HL(s), rr, (s.F & Z85_F_C) != 0);
            set_HL(s, o16.res);
            s.F = o16.f;
          end else if ((op & 8'hC7) == 8'h44) begin
            o2 = alu_neg(s.A, s.F);
            s.A = o2.res;
            s.F = o2.f;
          end else if ((op & 8'hC7) == 8'h45) begin
            pop16(nn);
            s.PC = nn;
            s.IFF1 = s.IFF2;
          end else if ((op & 8'hC7) == 8'h4D) begin
            pop16(nn);
            s.PC = nn;
            s.IFF1 = s.IFF2;
          end else begin
            unique case (op)
              8'h47: s.I = s.A;
              8'h4F: s.R = s.A;
              8'h57: begin
                s.A = s.I;
                f = (s.F & Z85_F_C) | flags_sz_xy(s.A);
                if (s.IFF2) f |= Z85_F_PV;
                s.F = f;
              end
              8'h5F: begin
                s.A = s.R;
                f = (s.F & Z85_F_C) | flags_sz_xy(s.A);
                if (s.IFF2) f |= Z85_F_PV;
                s.F = f;
              end
              8'h46, 8'h4E, 8'h66, 8'h6E: s.IM = 2'd0;
              8'h56, 8'h76: s.IM = 2'd1;
              8'h5E, 8'h7E: s.IM = 2'd2;
              8'h67: begin
                v = rd8(get_HL(s));
                wr8(get_HL(s), {s.A[3:0], v[7:4]});
                s.A = {s.A[7:4], v[3:0]};
                f = (s.F & Z85_F_C) | flags_szp_xy(s.A);
                s.F = f;
              end
              8'h6F: begin
                v = rd8(get_HL(s));
                wr8(get_HL(s), {v[3:0], s.A[3:0]});
                s.A = {s.A[7:4], v[7:4]};
                f = (s.F & Z85_F_C) | flags_szp_xy(s.A);
                s.F = f;
              end
              8'hA0, 8'hB0, 8'hA8, 8'hB8: begin
                logic [7:0] tmp;
                tmp = rd8(get_HL(s));
                wr8(pack16(s.D, s.E), tmp);
                if (op[3]) begin
                  set_HL(s, get_HL(s) - 16'd1);
                  set_ss(s, 2'd1, Z85_IDX_NONE, pack16(s.D, s.E) - 16'd1);
                end else begin
                  set_HL(s, get_HL(s) + 16'd1);
                  set_ss(s, 2'd1, Z85_IDX_NONE, pack16(s.D, s.E) + 16'd1);
                end
                set_ss(s, 2'd0, Z85_IDX_NONE, pack16(s.B, s.C) - 16'd1);
                s.F = flags_ld_block(s.F, s.A, tmp, pack16(s.B, s.C));
                if (op[4] && pack16(s.B, s.C) != 16'h0000) s.PC = start_pc;
              end
              8'hA1, 8'hB1, 8'hA9, 8'hB9: begin
                logic [7:0] tmp;
                tmp = rd8(get_HL(s));
                if (op[3]) set_HL(s, get_HL(s) - 16'd1);
                else set_HL(s, get_HL(s) + 16'd1);
                set_ss(s, 2'd0, Z85_IDX_NONE, pack16(s.B, s.C) - 16'd1);
                s.F = flags_cp_block(s.F, s.A, tmp, pack16(s.B, s.C));
                if (op[4] && pack16(s.B, s.C) != 16'h0000 && (s.F & Z85_F_Z) == 0) s.PC = start_pc;
              end
              8'hA2, 8'hB2, 8'hAA, 8'hBA: begin
                v = rdio({s.B, s.C});
                wr8(get_HL(s), v);
                if (op[3]) set_HL(s, get_HL(s) - 16'd1);
                else set_HL(s, get_HL(s) + 16'd1);
                s.B = s.B - 8'd1;
                s.F = flags_block_io(v, s.B, s.C, get_HL(s)[7:0], 1'b1, !op[3]);
                if (op[4] && s.B != 8'h00) s.PC = start_pc;
              end
              8'hA3, 8'hB3, 8'hAB, 8'hBB: begin
                v = rd8(get_HL(s));
                wrio({s.B, s.C}, v);
                if (op[3]) set_HL(s, get_HL(s) - 16'd1);
                else set_HL(s, get_HL(s) + 16'd1);
                s.B = s.B - 8'd1;
                s.F = flags_block_io(v, s.B, s.C, get_HL(s)[7:0], 1'b0, !op[3]);
                if (op[4] && s.B != 8'h00) s.PC = start_pc;
              end
              default: begin
                // Undefined ED opcodes act as NOP.
              end
            endcase
          end
        end
      endcase
    end
  endtask

endmodule : z85_ref_model
