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

  // --------------------------------------------------------------------------
  // Helpers
  // --------------------------------------------------------------------------
  function automatic logic [7:0] rd8(input logic [15:0] addr);
    return mem[addr];
  endfunction

  task automatic wr8(input logic [15:0] addr, input logic [7:0] v);
    mem[addr] = v;
  endtask

  task automatic push16(input logic [15:0] v);
    s.SP = s.SP - 16'd1;
    wr8(s.SP, v[15:8]);
    s.SP = s.SP - 16'd1;
    wr8(s.SP, v[7:0]);
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
    end
  endtask

  // --------------------------------------------------------------------------
  // Execute one boundary event: either take an interrupt or retire one insn.
  // irq_is_nmi is an out-of-band indicator (mirrors z85_core modeling choice).
  // --------------------------------------------------------------------------
  task automatic step(input logic irq_valid, input logic irq_is_nmi, input logic [7:0] irq_byte);
    logic inhibit_int;
    logic [15:0] start_pc;
    z85_idx_sel_e idx;
    z85_grp_e grp;
    logic signed [7:0] disp;
    logic [7:0] op;
    begin
      if (trapped) return;

      inhibit_int = ei_delay;
      if (ei_delay) ei_delay = 1'b0;

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
          2'd1: s.PC = 16'h0038;
          2'd2: s.PC = rd16({s.I, irq_byte});
          default: begin
            if ((irq_byte & 8'hC7) == 8'hC7) begin
              s.PC = {13'b0, irq_byte[5:3], 3'b000};
            end else begin
              trapped = 1'b1;
              cause = 32'h0000_0003;
              epc = {16'h0000, s.PC};
            end
          end
        endcase
        return;
      end

      if (s.halt_latch) return;

      start_pc = s.PC;

      // Prefix/opcode fetch loop.
      idx = Z85_IDX_NONE;
      grp = Z85_GRP_BASE;
      disp = 8'sd0;

      forever begin
        op = rd8(s.PC);
        s.PC = s.PC + 16'd1;
        r_inc_on_opcode_fetch(s);

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

      // Execute minimal subset matching current RTL.
      unique case (grp)
        Z85_GRP_BASE: begin
          if (op == 8'h00) begin
            // NOP
          end else if (op == 8'h76) begin
            s.halt_latch = 1'b1;
          end else if (op == 8'hF3) begin
            s.IFF1 = 1'b0;
            s.IFF2 = 1'b0;
            ei_delay = 1'b0;
          end else if (op == 8'hFB) begin
            s.IFF1 = 1'b1;
            s.IFF2 = 1'b1;
            ei_delay = 1'b1;
          end else if (op == 8'h27) begin
            z85_alu8_t o2;
            o2 = alu_daa(s.A, s.F);
            s.A = o2.res;
            s.F = o2.f;
          end else if ((op & 8'hC7) == 8'h06) begin
            // LD r,n
            logic [2:0] r;
            logic [7:0] n;
            r = op[5:3];
            n = rd8(s.PC);
            s.PC = s.PC + 16'd1;
            if (r == 3'd6) begin
              wr8(hl_eff_addr(s, idx, disp), n);
            end else begin
              set_r8(s, r, idx, n);
            end
          end else if (op == 8'h21 || op == 8'h31) begin
            logic [15:0] nn;
            nn = rd16(s.PC);
            s.PC = s.PC + 16'd2;
            if (op == 8'h31) s.SP = nn;
            else set_ss(s, 2'd2, idx, nn);
          end else if (op == 8'hC6 || op == 8'hCE || op == 8'hD6 || op == 8'hDE) begin
            logic [7:0] n;
            z85_alu8_t o2;
            n = rd8(s.PC);
            s.PC = s.PC + 16'd1;
            unique case (op)
              8'hC6: o2 = alu_add8(s.A, n);
              8'hCE: o2 = alu_adc8(s.A, n, (s.F & Z85_F_C) != 0);
              8'hD6: o2 = alu_sub8(s.A, n);
              default: o2 = alu_sbc8(s.A, n, (s.F & Z85_F_C) != 0);
            endcase
            s.A = o2.res;
            s.F = o2.f;
          end else begin
            trapped = 1'b1;
            cause = 32'h0000_0001;
            epc = {16'h0000, start_pc};
          end
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
          if (op == 8'h47) begin
            s.I = s.A;
          end else if (op == 8'h5E || op == 8'h7E) begin
            s.IM = 2'd2;
          end else if (op == 8'h56 || op == 8'h76) begin
            s.IM = 2'd1;
          end else if (op == 8'h46 || op == 8'h4E) begin
            s.IM = 2'd0;
          end else begin
            trapped = 1'b1;
            cause = 32'h0000_0001;
            epc = {16'h0000, start_pc};
          end
        end

        default: begin
          trapped = 1'b1;
          cause = 32'h0000_0001;
          epc = {16'h0000, start_pc};
        end
      endcase
    end
  endtask

endmodule : z85_ref_model

