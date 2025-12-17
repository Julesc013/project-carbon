#include "carbon_sim/cpu/z80.h"

#include <iomanip>
#include <iostream>
#include <optional>
#include <sstream>
#include <utility>

#include "carbon_sim/devices/interrupt_controller.h"

namespace carbon_sim {

static std::string hex16(u16 v) {
  std::ostringstream oss;
  oss << "0x" << std::hex << std::uppercase << std::setw(4) << std::setfill('0')
      << static_cast<unsigned>(v);
  return oss.str();
}

Z80::Z80(Bus& bus, InterruptController* irq) : bus_(bus), irq_(irq) { init_tables(); }

void Z80::init_tables() {
  for (int i = 0; i < 256; ++i) {
    const u8 v = static_cast<u8>(i);
    u8 f = 0;
    if (v & 0x80) {
      f |= FLAG_S;
    }
    if (v == 0) {
      f |= FLAG_Z;
    }
    if (parity(v)) {
      f |= FLAG_PV;
    }
    f |= (v & (FLAG_X | FLAG_Y));
    szp_[i] = f;
  }
}

bool Z80::parity(u8 value) const {
  bool even = true;
  while (value != 0) {
    even = !even;
    value &= static_cast<u8>(value - 1);
  }
  return even;
}

void Z80::reset() {
  a_ = f_ = b_ = c_ = d_ = e_ = h_ = l_ = 0;
  a2_ = f2_ = b2_ = c2_ = d2_ = e2_ = h2_ = l2_ = 0;
  ix_ = iy_ = 0;
  sp_ = 0xFFFF;
  pc_ = 0;
  i_ = r_ = 0;
  iff1_ = iff2_ = false;
  im_ = 0;
  halt_ = false;
  ei_delay_ = false;
  trapped_ = false;
  trap_reason_.clear();
  step_cycles_ = 0;
  total_cycles_ = 0;
}

u8 Z80::mem_read(u16 addr) {
  step_cycles_ += 3;
  return bus_.mem_read(addr);
}

void Z80::mem_write(u16 addr, u8 value) {
  step_cycles_ += 3;
  bus_.mem_write(addr, value);
}

u8 Z80::io_read(u16 port) {
  step_cycles_ += 4;
  return bus_.io_read(port);
}

void Z80::io_write(u16 port, u8 value) {
  step_cycles_ += 4;
  bus_.io_write(port, value);
}

u8 Z80::fetch_op() {
  const u8 v = mem_read(pc_);
  pc_ = static_cast<u16>(pc_ + 1);
  r_ = static_cast<u8>((r_ & 0x80) | ((r_ + 1) & 0x7F));
  step_cycles_ += 4;
  return v;
}

u8 Z80::fetch_byte() {
  const u8 v = mem_read(pc_);
  pc_ = static_cast<u16>(pc_ + 1);
  step_cycles_ += 3;
  return v;
}

u16 Z80::fetch_u16() {
  const u8 lo = fetch_byte();
  const u8 hi = fetch_byte();
  return static_cast<u16>((hi << 8) | lo);
}

void Z80::push_u16(u16 value) {
  const u8 hi = get_hi(value);
  const u8 lo = get_lo(value);
  sp_ = static_cast<u16>(sp_ - 1);
  mem_write(sp_, hi);
  sp_ = static_cast<u16>(sp_ - 1);
  mem_write(sp_, lo);
}

u16 Z80::pop_u16() {
  const u8 lo = mem_read(sp_);
  sp_ = static_cast<u16>(sp_ + 1);
  const u8 hi = mem_read(sp_);
  sp_ = static_cast<u16>(sp_ + 1);
  return static_cast<u16>((hi << 8) | lo);
}

void Z80::trap(std::string reason) {
  trapped_ = true;
  trap_reason_ = std::move(reason);
}

u16& Z80::index_reg(u8 prefix) {
  return (prefix == 0xFD) ? iy_ : ix_;
}

u8 Z80::reg8(int r, u8 index_prefix) const {
  switch (r & 7) {
    case 0:
      return b_;
    case 1:
      return c_;
    case 2:
      return d_;
    case 3:
      return e_;
    case 4:
      return index_prefix == 0 ? h_
                               : get_hi((index_prefix == 0xFD) ? iy_ : ix_);
    case 5:
      return index_prefix == 0 ? l_
                               : get_lo((index_prefix == 0xFD) ? iy_ : ix_);
    case 7:
      return a_;
    default:
      return 0;
  }
}

void Z80::set_reg8(int r, u8 index_prefix, u8 value) {
  switch (r & 7) {
    case 0:
      b_ = value;
      return;
    case 1:
      c_ = value;
      return;
    case 2:
      d_ = value;
      return;
    case 3:
      e_ = value;
      return;
    case 4:
      if (index_prefix == 0) {
        h_ = value;
      } else {
        set_hi(index_reg(index_prefix), value);
      }
      return;
    case 5:
      if (index_prefix == 0) {
        l_ = value;
      } else {
        set_lo(index_reg(index_prefix), value);
      }
      return;
    case 7:
      a_ = value;
      return;
    default:
      return;
  }
}

u16 Z80::reg16(int rp, u8 index_prefix) const {
  switch (rp & 3) {
    case 0:
      return bc();
    case 1:
      return de();
    case 2:
      return index_prefix == 0 ? hl() : ((index_prefix == 0xFD) ? iy_ : ix_);
    case 3:
      return sp_;
    default:
      return 0;
  }
}

void Z80::set_reg16(int rp, u8 index_prefix, u16 value) {
  switch (rp & 3) {
    case 0:
      set_bc(value);
      return;
    case 1:
      set_de(value);
      return;
    case 2:
      if (index_prefix == 0) {
        set_hl(value);
      } else {
        index_reg(index_prefix) = value;
      }
      return;
    case 3:
      sp_ = value;
      return;
    default:
      return;
  }
}

u16 Z80::addr_hl(u8 index_prefix) const {
  return index_prefix == 0 ? hl() : ((index_prefix == 0xFD) ? iy_ : ix_);
}

u16 Z80::addr_hl_disp(u8 index_prefix, std::int8_t disp) const {
  const u16 base = addr_hl(index_prefix);
  return static_cast<u16>(base + static_cast<std::int16_t>(disp));
}

u8 Z80::read_r(int r, u8 index_prefix, std::optional<std::int8_t> disp) {
  if ((r & 7) == 6) {
    if (index_prefix != 0) {
      if (!disp.has_value()) {
        trap("missing displacement for (IX/IY+d) operand");
        return 0xFF;
      }
      return mem_read(addr_hl_disp(index_prefix, *disp));
    }
    return mem_read(hl());
  }
  return reg8(r, index_prefix);
}

void Z80::write_r(int r, u8 index_prefix, std::optional<std::int8_t> disp, u8 value) {
  if ((r & 7) == 6) {
    if (index_prefix != 0) {
      if (!disp.has_value()) {
        trap("missing displacement for (IX/IY+d) operand");
        return;
      }
      mem_write(addr_hl_disp(index_prefix, *disp), value);
      return;
    }
    mem_write(hl(), value);
    return;
  }
  set_reg8(r, index_prefix, value);
}

u8 Z80::inc8(u8 value) {
  const u8 res = static_cast<u8>(value + 1);
  u8 f = static_cast<u8>(f_ & FLAG_C);
  f |= szp_[res];
  if ((value & 0x0F) == 0x0F) {
    f |= FLAG_H;
  }
  if (value == 0x7F) {
    f |= FLAG_PV;
  } else {
    f &= static_cast<u8>(~FLAG_PV);
  }
  f &= static_cast<u8>(~FLAG_N);
  f_ = f;
  return res;
}

u8 Z80::dec8(u8 value) {
  const u8 res = static_cast<u8>(value - 1);
  u8 f = static_cast<u8>(f_ & FLAG_C);
  f |= szp_[res];
  if ((value & 0x0F) == 0x00) {
    f |= FLAG_H;
  }
  if (value == 0x80) {
    f |= FLAG_PV;
  } else {
    f &= static_cast<u8>(~FLAG_PV);
  }
  f |= FLAG_N;
  f_ = f;
  return res;
}

void Z80::alu_add(u8 value, bool with_carry) {
  const u8 carry = (with_carry && (f_ & FLAG_C)) ? 1 : 0;
  const u16 sum = static_cast<u16>(a_) + value + carry;
  const u8 res = static_cast<u8>(sum & 0xFF);
  u8 f = 0;
  f |= (res & (FLAG_S | FLAG_Y | FLAG_X));
  if (res == 0) {
    f |= FLAG_Z;
  }
  if (((a_ & 0x0F) + (value & 0x0F) + carry) > 0x0F) {
    f |= FLAG_H;
  }
  const bool overflow = (~(a_ ^ value) & (a_ ^ res) & 0x80) != 0;
  if (overflow) {
    f |= FLAG_PV;
  }
  if (sum > 0xFF) {
    f |= FLAG_C;
  }
  a_ = res;
  f_ = f;
}

void Z80::alu_sub(u8 value, bool with_carry) {
  const u8 carry = (with_carry && (f_ & FLAG_C)) ? 1 : 0;
  const u16 diff = static_cast<u16>(a_) - value - carry;
  const u8 res = static_cast<u8>(diff & 0xFF);
  u8 f = FLAG_N;
  f |= (res & (FLAG_S | FLAG_Y | FLAG_X));
  if (res == 0) {
    f |= FLAG_Z;
  }
  if ((a_ ^ value ^ res) & 0x10) {
    f |= FLAG_H;
  }
  const bool overflow = ((a_ ^ value) & (a_ ^ res) & 0x80) != 0;
  if (overflow) {
    f |= FLAG_PV;
  }
  if (diff & 0x100) {
    f |= FLAG_C;
  }
  a_ = res;
  f_ = f;
}

void Z80::alu_and(u8 value) {
  a_ = static_cast<u8>(a_ & value);
  f_ = static_cast<u8>(szp_[a_] | FLAG_H);
}

void Z80::alu_or(u8 value) {
  a_ = static_cast<u8>(a_ | value);
  f_ = szp_[a_];
}

void Z80::alu_xor(u8 value) {
  a_ = static_cast<u8>(a_ ^ value);
  f_ = szp_[a_];
}

void Z80::alu_cp(u8 value) {
  const u16 diff = static_cast<u16>(a_) - value;
  const u8 res = static_cast<u8>(diff & 0xFF);
  u8 f = FLAG_N;
  if (res & 0x80) {
    f |= FLAG_S;
  }
  if (res == 0) {
    f |= FLAG_Z;
  }
  f |= (value & (FLAG_X | FLAG_Y));
  if ((a_ ^ value ^ res) & 0x10) {
    f |= FLAG_H;
  }
  const bool overflow = ((a_ ^ value) & (a_ ^ res) & 0x80) != 0;
  if (overflow) {
    f |= FLAG_PV;
  }
  if (diff & 0x100) {
    f |= FLAG_C;
  }
  f_ = f;
}

u16 Z80::add16(u16 lhs, u16 rhs) {
  const u32 sum = static_cast<u32>(lhs) + rhs;
  const u16 res = static_cast<u16>(sum & 0xFFFF);
  u8 f = static_cast<u8>(f_ & (FLAG_S | FLAG_Z | FLAG_PV | FLAG_C));
  if (((lhs & 0x0FFF) + (rhs & 0x0FFF)) > 0x0FFF) {
    f |= FLAG_H;
  }
  if (sum & 0x10000) {
    f |= FLAG_C;
  } else {
    f &= static_cast<u8>(~FLAG_C);
  }
  f &= static_cast<u8>(~FLAG_N);
  f = static_cast<u8>((f & ~(FLAG_X | FLAG_Y)) | ((res >> 8) & (FLAG_X | FLAG_Y)));
  f_ = f;
  return res;
}

u16 Z80::adc16(u16 lhs, u16 rhs) {
  const u16 carry = (f_ & FLAG_C) ? 1 : 0;
  const u32 sum = static_cast<u32>(lhs) + rhs + carry;
  const u16 res = static_cast<u16>(sum & 0xFFFF);
  u8 f = 0;
  if (res & 0x8000) {
    f |= FLAG_S;
  }
  if (res == 0) {
    f |= FLAG_Z;
  }
  if (((lhs & 0x0FFF) + (rhs & 0x0FFF) + carry) > 0x0FFF) {
    f |= FLAG_H;
  }
  const bool overflow = (~(lhs ^ rhs) & (lhs ^ res) & 0x8000) != 0;
  if (overflow) {
    f |= FLAG_PV;
  }
  if (sum & 0x10000) {
    f |= FLAG_C;
  }
  f = static_cast<u8>(f | ((res >> 8) & (FLAG_X | FLAG_Y)));
  f_ = f;
  return res;
}

u16 Z80::sbc16(u16 lhs, u16 rhs) {
  const u16 carry = (f_ & FLAG_C) ? 1 : 0;
  const u32 diff = static_cast<u32>(lhs) - rhs - carry;
  const u16 res = static_cast<u16>(diff & 0xFFFF);
  u8 f = FLAG_N;
  if (res & 0x8000) {
    f |= FLAG_S;
  }
  if (res == 0) {
    f |= FLAG_Z;
  }
  if (((lhs ^ rhs ^ res) & 0x1000) != 0) {
    f |= FLAG_H;
  }
  const bool overflow = ((lhs ^ rhs) & (lhs ^ res) & 0x8000) != 0;
  if (overflow) {
    f |= FLAG_PV;
  }
  if (diff & 0x10000) {
    f |= FLAG_C;
  }
  f = static_cast<u8>(f | ((res >> 8) & (FLAG_X | FLAG_Y)));
  f_ = f;
  return res;
}

u64 Z80::execute_cb(u8 op) {
  const int x = (op >> 6) & 3;
  const int y = (op >> 3) & 7;
  const int z = op & 7;

  const auto rot_shift = [&](u8 v) -> u8 {
    u8 res = v;
    u8 carry = 0;
    switch (y) {
      case 0: { // RLC
        carry = static_cast<u8>((v >> 7) & 1);
        res = static_cast<u8>((v << 1) | carry);
        break;
      }
      case 1: { // RRC
        carry = static_cast<u8>(v & 1);
        res = static_cast<u8>((v >> 1) | (carry << 7));
        break;
      }
      case 2: { // RL
        carry = static_cast<u8>((v >> 7) & 1);
        const u8 c = (f_ & FLAG_C) ? 1 : 0;
        res = static_cast<u8>((v << 1) | c);
        break;
      }
      case 3: { // RR
        carry = static_cast<u8>(v & 1);
        const u8 c = (f_ & FLAG_C) ? 1 : 0;
        res = static_cast<u8>((v >> 1) | (c << 7));
        break;
      }
      case 4: { // SLA
        carry = static_cast<u8>((v >> 7) & 1);
        res = static_cast<u8>(v << 1);
        break;
      }
      case 5: { // SRA
        carry = static_cast<u8>(v & 1);
        res = static_cast<u8>((v >> 1) | (v & 0x80));
        break;
      }
      case 6: { // SLL (undocumented)
        carry = static_cast<u8>((v >> 7) & 1);
        res = static_cast<u8>((v << 1) | 0x01);
        break;
      }
      case 7: { // SRL
        carry = static_cast<u8>(v & 1);
        res = static_cast<u8>(v >> 1);
        break;
      }
      default:
        break;
    }
    f_ = static_cast<u8>(szp_[res] | (carry ? FLAG_C : 0));
    return res;
  };

  if (x == 0) {
    const bool is_mem = z == 6;
    const u8 v = read_r(z, 0, std::nullopt);
    const u8 res = rot_shift(v);
    write_r(z, 0, std::nullopt, res);
    return is_mem ? 15 : 8;
  }

  if (x == 1) { // BIT
    const u8 v = read_r(z, 0, std::nullopt);
    const u8 mask = static_cast<u8>(1U << y);
    u8 f = static_cast<u8>((f_ & FLAG_C) | FLAG_H);
    if ((v & mask) == 0) {
      f |= FLAG_Z | FLAG_PV;
    }
    if (y == 7 && (v & 0x80)) {
      f |= FLAG_S;
    }
    f = static_cast<u8>(f | (v & (FLAG_X | FLAG_Y)));
    f_ = f;
    return z == 6 ? 12 : 8;
  }

  if (x == 2) { // RES
    const bool is_mem = z == 6;
    const u8 v = read_r(z, 0, std::nullopt);
    const u8 res = static_cast<u8>(v & ~(1U << y));
    write_r(z, 0, std::nullopt, res);
    return is_mem ? 15 : 8;
  }

  // SET
  const bool is_mem = z == 6;
  const u8 v = read_r(z, 0, std::nullopt);
  const u8 res = static_cast<u8>(v | (1U << y));
  write_r(z, 0, std::nullopt, res);
  return is_mem ? 15 : 8;
}

u64 Z80::execute_ed(u8 op) {
  const auto cond = [&](int cc) -> bool {
    switch (cc & 7) {
      case 0:
        return (f_ & FLAG_Z) == 0;
      case 1:
        return (f_ & FLAG_Z) != 0;
      case 2:
        return (f_ & FLAG_C) == 0;
      case 3:
        return (f_ & FLAG_C) != 0;
      case 4:
        return (f_ & FLAG_PV) == 0;
      case 5:
        return (f_ & FLAG_PV) != 0;
      case 6:
        return (f_ & FLAG_S) == 0;
      case 7:
        return (f_ & FLAG_S) != 0;
      default:
        return false;
    }
  };

  switch (op) {
    case 0x44:
    case 0x4C:
    case 0x54:
    case 0x5C:
    case 0x64:
    case 0x6C:
    case 0x74:
    case 0x7C: { // NEG
      const u8 old_a = a_;
      a_ = 0;
      alu_sub(old_a, false);
      return 0;
    }

    case 0x45:
    case 0x4D:
    case 0x55:
    case 0x5D:
    case 0x65:
    case 0x6D:
    case 0x75:
    case 0x7D: { // RETN/RETI
      pc_ = pop_u16();
      iff1_ = iff2_;
      return 0;
    }

    case 0x46:
    case 0x4E:
    case 0x66:
    case 0x6E: // IM 0
      im_ = 0;
      return 0;
    case 0x56:
    case 0x76: // IM 1
      im_ = 1;
      return 0;
    case 0x5E:
    case 0x7E: // IM 2
      im_ = 2;
      return 0;

    case 0x47: // LD I,A
      i_ = a_;
      return 0;
    case 0x4F: // LD R,A
      r_ = a_;
      return 0;

    case 0x57: { // LD A,I
      a_ = i_;
      u8 f = static_cast<u8>((f_ & FLAG_C) | (a_ & (FLAG_S | FLAG_Y | FLAG_X)));
      if (a_ == 0) {
        f |= FLAG_Z;
      }
      if (iff2_) {
        f |= FLAG_PV;
      }
      f_ = f;
      return 0;
    }
    case 0x5F: { // LD A,R
      a_ = r_;
      u8 f = static_cast<u8>((f_ & FLAG_C) | (a_ & (FLAG_S | FLAG_Y | FLAG_X)));
      if (a_ == 0) {
        f |= FLAG_Z;
      }
      if (iff2_) {
        f |= FLAG_PV;
      }
      f_ = f;
      return 0;
    }

    case 0x40:
    case 0x48:
    case 0x50:
    case 0x58:
    case 0x60:
    case 0x68:
    case 0x78: { // IN r,(C)
      const int r = (op >> 3) & 7;
      const u16 port = static_cast<u16>((b_ << 8) | c_);
      const u8 v = io_read(port);
      set_reg8(r, 0, v);
      f_ = static_cast<u8>((f_ & FLAG_C) | szp_[v]);
      return 0;
    }
    case 0x70: { // IN (C)
      const u16 port = static_cast<u16>((b_ << 8) | c_);
      const u8 v = io_read(port);
      f_ = static_cast<u8>((f_ & FLAG_C) | szp_[v]);
      return 0;
    }

    case 0x41:
    case 0x49:
    case 0x51:
    case 0x59:
    case 0x61:
    case 0x69:
    case 0x79:
    case 0x71: { // OUT (C),r (r==6 writes 0)
      const int r = (op >> 3) & 7;
      const u16 port = static_cast<u16>((b_ << 8) | c_);
      const u8 v = (r == 6) ? 0 : reg8(r, 0);
      io_write(port, v);
      return 0;
    }

    case 0x42:
    case 0x52:
    case 0x62:
    case 0x72: { // SBC HL,rr
      const int rp = (op >> 4) & 3;
      set_hl(sbc16(hl(), reg16(rp, 0)));
      return 0;
    }
    case 0x4A:
    case 0x5A:
    case 0x6A:
    case 0x7A: { // ADC HL,rr
      const int rp = (op >> 4) & 3;
      set_hl(adc16(hl(), reg16(rp, 0)));
      return 0;
    }

    case 0x43:
    case 0x53:
    case 0x63:
    case 0x73: { // LD (nn),rr
      const int rp = (op >> 4) & 3;
      const u16 addr = fetch_u16();
      const u16 v = reg16(rp, 0);
      mem_write(addr, get_lo(v));
      mem_write(static_cast<u16>(addr + 1), get_hi(v));
      return 0;
    }
    case 0x4B:
    case 0x5B:
    case 0x6B:
    case 0x7B: { // LD rr,(nn)
      const int rp = (op >> 4) & 3;
      const u16 addr = fetch_u16();
      const u8 lo = mem_read(addr);
      const u8 hi = mem_read(static_cast<u16>(addr + 1));
      set_reg16(rp, 0, static_cast<u16>((hi << 8) | lo));
      return 0;
    }

    case 0x67: { // RRD
      const u8 v = mem_read(hl());
      const u8 lo = static_cast<u8>(v & 0x0F);
      const u8 hi = static_cast<u8>((v >> 4) & 0x0F);
      mem_write(hl(), static_cast<u8>((a_ << 4) | lo));
      a_ = static_cast<u8>((a_ & 0xF0) | hi);
      f_ = static_cast<u8>((f_ & FLAG_C) | szp_[a_]);
      return 0;
    }
    case 0x6F: { // RLD
      const u8 v = mem_read(hl());
      const u8 lo = static_cast<u8>(v & 0x0F);
      const u8 hi = static_cast<u8>((v >> 4) & 0x0F);
      mem_write(hl(), static_cast<u8>((hi << 4) | (a_ & 0x0F)));
      a_ = static_cast<u8>((a_ & 0xF0) | lo);
      f_ = static_cast<u8>((f_ & FLAG_C) | szp_[a_]);
      return 0;
    }

    case 0xA0: { // LDI
      const u8 v = mem_read(hl());
      mem_write(de(), v);
      set_hl(static_cast<u16>(hl() + 1));
      set_de(static_cast<u16>(de() + 1));
      set_bc(static_cast<u16>(bc() - 1));
      u8 f = static_cast<u8>(f_ & (FLAG_S | FLAG_Z | FLAG_C));
      if (bc() != 0) {
        f |= FLAG_PV;
      }
      f_ = f;
      return 0;
    }
    case 0xB0: { // LDIR (repeat)
      execute_ed(0xA0);
      if (bc() != 0) {
        pc_ = static_cast<u16>(pc_ - 2);
        step_cycles_ += 5;
      }
      return 0;
    }
    case 0xA8: { // LDD
      const u8 v = mem_read(hl());
      mem_write(de(), v);
      set_hl(static_cast<u16>(hl() - 1));
      set_de(static_cast<u16>(de() - 1));
      set_bc(static_cast<u16>(bc() - 1));
      u8 f = static_cast<u8>(f_ & (FLAG_S | FLAG_Z | FLAG_C));
      if (bc() != 0) {
        f |= FLAG_PV;
      }
      f_ = f;
      return 0;
    }
    case 0xB8: { // LDDR (repeat)
      execute_ed(0xA8);
      if (bc() != 0) {
        pc_ = static_cast<u16>(pc_ - 2);
        step_cycles_ += 5;
      }
      return 0;
    }

    case 0xA1: { // CPI
      const u8 v = mem_read(hl());
      const u8 res = static_cast<u8>(a_ - v);
      set_hl(static_cast<u16>(hl() + 1));
      set_bc(static_cast<u16>(bc() - 1));
      u8 f = static_cast<u8>((f_ & FLAG_C) | FLAG_N);
      if (res & 0x80) {
        f |= FLAG_S;
      }
      if (res == 0) {
        f |= FLAG_Z;
      }
      if ((a_ ^ v ^ res) & 0x10) {
        f |= FLAG_H;
      }
      if (bc() != 0) {
        f |= FLAG_PV;
      }
      f_ = f;
      return 0;
    }
    case 0xB1: { // CPIR (repeat)
      execute_ed(0xA1);
      if ((f_ & FLAG_Z) == 0 && bc() != 0) {
        pc_ = static_cast<u16>(pc_ - 2);
        step_cycles_ += 5;
      }
      return 0;
    }
    case 0xA9: { // CPD
      const u8 v = mem_read(hl());
      const u8 res = static_cast<u8>(a_ - v);
      set_hl(static_cast<u16>(hl() - 1));
      set_bc(static_cast<u16>(bc() - 1));
      u8 f = static_cast<u8>((f_ & FLAG_C) | FLAG_N);
      if (res & 0x80) {
        f |= FLAG_S;
      }
      if (res == 0) {
        f |= FLAG_Z;
      }
      if ((a_ ^ v ^ res) & 0x10) {
        f |= FLAG_H;
      }
      if (bc() != 0) {
        f |= FLAG_PV;
      }
      f_ = f;
      return 0;
    }
    case 0xB9: { // CPDR (repeat)
      execute_ed(0xA9);
      if ((f_ & FLAG_Z) == 0 && bc() != 0) {
        pc_ = static_cast<u16>(pc_ - 2);
        step_cycles_ += 5;
      }
      return 0;
    }

    case 0xA2: { // INI
      const u16 port = static_cast<u16>((b_ << 8) | c_);
      const u8 v = io_read(port);
      mem_write(hl(), v);
      set_hl(static_cast<u16>(hl() + 1));
      b_ = static_cast<u8>(b_ - 1);
      f_ = static_cast<u8>(b_ == 0 ? FLAG_Z : 0);
      return 0;
    }
    case 0xB2: { // INIR (repeat)
      execute_ed(0xA2);
      if (b_ != 0) {
        pc_ = static_cast<u16>(pc_ - 2);
        step_cycles_ += 5;
      }
      return 0;
    }
    case 0xAA: { // IND
      const u16 port = static_cast<u16>((b_ << 8) | c_);
      const u8 v = io_read(port);
      mem_write(hl(), v);
      set_hl(static_cast<u16>(hl() - 1));
      b_ = static_cast<u8>(b_ - 1);
      f_ = static_cast<u8>(b_ == 0 ? FLAG_Z : 0);
      return 0;
    }
    case 0xBA: { // INDR (repeat)
      execute_ed(0xAA);
      if (b_ != 0) {
        pc_ = static_cast<u16>(pc_ - 2);
        step_cycles_ += 5;
      }
      return 0;
    }

    case 0xA3: { // OUTI
      const u8 v = mem_read(hl());
      const u16 port = static_cast<u16>((b_ << 8) | c_);
      io_write(port, v);
      set_hl(static_cast<u16>(hl() + 1));
      b_ = static_cast<u8>(b_ - 1);
      f_ = static_cast<u8>(b_ == 0 ? FLAG_Z : 0);
      return 0;
    }
    case 0xB3: { // OTIR (repeat)
      execute_ed(0xA3);
      if (b_ != 0) {
        pc_ = static_cast<u16>(pc_ - 2);
        step_cycles_ += 5;
      }
      return 0;
    }
    case 0xAB: { // OUTD
      const u8 v = mem_read(hl());
      const u16 port = static_cast<u16>((b_ << 8) | c_);
      io_write(port, v);
      set_hl(static_cast<u16>(hl() - 1));
      b_ = static_cast<u8>(b_ - 1);
      f_ = static_cast<u8>(b_ == 0 ? FLAG_Z : 0);
      return 0;
    }
    case 0xBB: { // OTDR (repeat)
      execute_ed(0xAB);
      if (b_ != 0) {
        pc_ = static_cast<u16>(pc_ - 2);
        step_cycles_ += 5;
      }
      return 0;
    }

    default:
      trap("illegal ED opcode " + hex16(static_cast<u16>(0xED00 | op)));
      return 0;
  }
}

u64 Z80::execute_base(u8 op, u8 index_prefix) {
  // LD r,r'
  if ((op & 0xC0) == 0x40) {
    if (op == 0x76) { // HALT
      halt_ = true;
      return 0;
    }
    const int dst = (op >> 3) & 7;
    const int src = op & 7;
    std::optional<std::int8_t> disp;
    if (index_prefix != 0 && (dst == 6 || src == 6)) {
      disp = static_cast<std::int8_t>(fetch_byte());
    }
    const u8 v = read_r(src, index_prefix, disp);
    write_r(dst, index_prefix, disp, v);
    return 0;
  }

  // ALU A,r
  if ((op & 0xC0) == 0x80) {
    const int y = (op >> 3) & 7;
    const int z = op & 7;
    std::optional<std::int8_t> disp;
    if (index_prefix != 0 && z == 6) {
      disp = static_cast<std::int8_t>(fetch_byte());
    }
    const u8 v = read_r(z, index_prefix, disp);
    switch (y) {
      case 0:
        alu_add(v, false);
        break;
      case 1:
        alu_add(v, true);
        break;
      case 2:
        alu_sub(v, false);
        break;
      case 3:
        alu_sub(v, true);
        break;
      case 4:
        alu_and(v);
        break;
      case 5:
        alu_xor(v);
        break;
      case 6:
        alu_or(v);
        break;
      case 7:
        alu_cp(v);
        break;
      default:
        break;
    }
    return 0;
  }

  // LD r,n
  if ((op & 0xC7) == 0x06) {
    const int r = (op >> 3) & 7;
    std::optional<std::int8_t> disp;
    if (index_prefix != 0 && r == 6) {
      disp = static_cast<std::int8_t>(fetch_byte());
    }
    const u8 n = fetch_byte();
    write_r(r, index_prefix, disp, n);
    return 0;
  }

  // INC r
  if ((op & 0xC7) == 0x04) {
    const int r = (op >> 3) & 7;
    std::optional<std::int8_t> disp;
    if (index_prefix != 0 && r == 6) {
      disp = static_cast<std::int8_t>(fetch_byte());
    }
    write_r(r, index_prefix, disp, inc8(read_r(r, index_prefix, disp)));
    return 0;
  }

  // DEC r
  if ((op & 0xC7) == 0x05) {
    const int r = (op >> 3) & 7;
    std::optional<std::int8_t> disp;
    if (index_prefix != 0 && r == 6) {
      disp = static_cast<std::int8_t>(fetch_byte());
    }
    write_r(r, index_prefix, disp, dec8(read_r(r, index_prefix, disp)));
    return 0;
  }

  // LD rp,nn
  if ((op & 0xCF) == 0x01) {
    const int rp = (op >> 4) & 3;
    set_reg16(rp, index_prefix, fetch_u16());
    return 0;
  }

  // INC rp
  if ((op & 0xCF) == 0x03) {
    const int rp = (op >> 4) & 3;
    set_reg16(rp, index_prefix, static_cast<u16>(reg16(rp, index_prefix) + 1));
    return 0;
  }

  // DEC rp
  if ((op & 0xCF) == 0x0B) {
    const int rp = (op >> 4) & 3;
    set_reg16(rp, index_prefix, static_cast<u16>(reg16(rp, index_prefix) - 1));
    return 0;
  }

  // ADD HL,rr (or ADD IX/IY,rr)
  if ((op & 0xCF) == 0x09) {
    const int rp = (op >> 4) & 3;
    const u16 lhs = reg16(2, index_prefix);
    const u16 rhs = reg16(rp, index_prefix);
    set_reg16(2, index_prefix, add16(lhs, rhs));
    return 0;
  }

  switch (op) {
    case 0x00: // NOP
      return 0;

    case 0x02: // LD (BC),A
      mem_write(bc(), a_);
      return 0;
    case 0x0A: // LD A,(BC)
      a_ = mem_read(bc());
      return 0;
    case 0x12: // LD (DE),A
      mem_write(de(), a_);
      return 0;
    case 0x1A: // LD A,(DE)
      a_ = mem_read(de());
      return 0;

    case 0x07: { // RLCA
      const u8 carry = static_cast<u8>((a_ >> 7) & 1);
      a_ = static_cast<u8>((a_ << 1) | carry);
      f_ = static_cast<u8>((f_ & (FLAG_S | FLAG_Z | FLAG_PV)) | (a_ & (FLAG_X | FLAG_Y)) |
                           (carry ? FLAG_C : 0));
      f_ &= static_cast<u8>(~(FLAG_H | FLAG_N));
      return 0;
    }
    case 0x0F: { // RRCA
      const u8 carry = static_cast<u8>(a_ & 1);
      a_ = static_cast<u8>((a_ >> 1) | (carry << 7));
      f_ = static_cast<u8>((f_ & (FLAG_S | FLAG_Z | FLAG_PV)) | (a_ & (FLAG_X | FLAG_Y)) |
                           (carry ? FLAG_C : 0));
      f_ &= static_cast<u8>(~(FLAG_H | FLAG_N));
      return 0;
    }
    case 0x17: { // RLA
      const u8 carry = static_cast<u8>((a_ >> 7) & 1);
      const u8 c = (f_ & FLAG_C) ? 1 : 0;
      a_ = static_cast<u8>((a_ << 1) | c);
      f_ = static_cast<u8>((f_ & (FLAG_S | FLAG_Z | FLAG_PV)) | (a_ & (FLAG_X | FLAG_Y)) |
                           (carry ? FLAG_C : 0));
      f_ &= static_cast<u8>(~(FLAG_H | FLAG_N));
      return 0;
    }
    case 0x1F: { // RRA
      const u8 carry = static_cast<u8>(a_ & 1);
      const u8 c = (f_ & FLAG_C) ? 1 : 0;
      a_ = static_cast<u8>((a_ >> 1) | (c << 7));
      f_ = static_cast<u8>((f_ & (FLAG_S | FLAG_Z | FLAG_PV)) | (a_ & (FLAG_X | FLAG_Y)) |
                           (carry ? FLAG_C : 0));
      f_ &= static_cast<u8>(~(FLAG_H | FLAG_N));
      return 0;
    }

    case 0x08: // EX AF,AF'
      std::swap(a_, a2_);
      std::swap(f_, f2_);
      return 0;

    case 0x10: { // DJNZ e
      const std::int8_t disp = static_cast<std::int8_t>(fetch_byte());
      b_ = static_cast<u8>(b_ - 1);
      if (b_ != 0) {
        pc_ = static_cast<u16>(pc_ + static_cast<std::int16_t>(disp));
      }
      return 0;
    }

    case 0x18: { // JR e
      const std::int8_t disp = static_cast<std::int8_t>(fetch_byte());
      pc_ = static_cast<u16>(pc_ + static_cast<std::int16_t>(disp));
      return 0;
    }
    case 0x20: { // JR NZ,e
      const std::int8_t disp = static_cast<std::int8_t>(fetch_byte());
      if ((f_ & FLAG_Z) == 0) {
        pc_ = static_cast<u16>(pc_ + static_cast<std::int16_t>(disp));
      }
      return 0;
    }
    case 0x28: { // JR Z,e
      const std::int8_t disp = static_cast<std::int8_t>(fetch_byte());
      if ((f_ & FLAG_Z) != 0) {
        pc_ = static_cast<u16>(pc_ + static_cast<std::int16_t>(disp));
      }
      return 0;
    }
    case 0x30: { // JR NC,e
      const std::int8_t disp = static_cast<std::int8_t>(fetch_byte());
      if ((f_ & FLAG_C) == 0) {
        pc_ = static_cast<u16>(pc_ + static_cast<std::int16_t>(disp));
      }
      return 0;
    }
    case 0x38: { // JR C,e
      const std::int8_t disp = static_cast<std::int8_t>(fetch_byte());
      if ((f_ & FLAG_C) != 0) {
        pc_ = static_cast<u16>(pc_ + static_cast<std::int16_t>(disp));
      }
      return 0;
    }

    case 0x22: { // LD (nn),HL/IX/IY
      const u16 addr = fetch_u16();
      const u16 v = reg16(2, index_prefix);
      mem_write(addr, get_lo(v));
      mem_write(static_cast<u16>(addr + 1), get_hi(v));
      return 0;
    }
    case 0x2A: { // LD HL/IX/IY,(nn)
      const u16 addr = fetch_u16();
      const u8 lo = mem_read(addr);
      const u8 hi = mem_read(static_cast<u16>(addr + 1));
      set_reg16(2, index_prefix, static_cast<u16>((hi << 8) | lo));
      return 0;
    }

    case 0x32: { // LD (nn),A
      mem_write(fetch_u16(), a_);
      return 0;
    }
    case 0x3A: { // LD A,(nn)
      a_ = mem_read(fetch_u16());
      return 0;
    }

    case 0x27: { // DAA
      u8 correction = 0;
      bool carry = (f_ & FLAG_C) != 0;
      const bool neg = (f_ & FLAG_N) != 0;
      if ((f_ & FLAG_H) != 0 || (a_ & 0x0F) > 9) {
        correction |= 0x06;
      }
      if (carry || a_ > 0x99) {
        correction |= 0x60;
        carry = true;
      }
      const u8 old_a = a_;
      a_ = neg ? static_cast<u8>(a_ - correction) : static_cast<u8>(a_ + correction);
      u8 f = static_cast<u8>(f_ & FLAG_N);
      f |= szp_[a_];
      if (carry) {
        f |= FLAG_C;
      }
      if ((old_a ^ a_ ^ correction) & 0x10) {
        f |= FLAG_H;
      }
      f_ = f;
      return 0;
    }

    case 0x2F: // CPL
      a_ = static_cast<u8>(~a_);
      f_ = static_cast<u8>((f_ & (FLAG_S | FLAG_Z | FLAG_PV | FLAG_C)) | (a_ & (FLAG_X | FLAG_Y)) |
                           FLAG_H | FLAG_N);
      return 0;

    case 0x37: // SCF
      f_ = static_cast<u8>((f_ & (FLAG_S | FLAG_Z | FLAG_PV)) | (a_ & (FLAG_X | FLAG_Y)) | FLAG_C);
      f_ &= static_cast<u8>(~(FLAG_H | FLAG_N));
      return 0;

    case 0x3F: { // CCF
      const bool old_c = (f_ & FLAG_C) != 0;
      u8 f = static_cast<u8>((f_ & (FLAG_S | FLAG_Z | FLAG_PV)) | (a_ & (FLAG_X | FLAG_Y)));
      if (old_c) {
        f |= FLAG_H;
      } else {
        f |= FLAG_C;
      }
      f_ = f;
      return 0;
    }

    case 0xC3: // JP nn
      pc_ = fetch_u16();
      return 0;

    case 0xC2:
    case 0xCA:
    case 0xD2:
    case 0xDA:
    case 0xE2:
    case 0xEA:
    case 0xF2:
    case 0xFA: { // JP cc,nn
      const u16 addr = fetch_u16();
      const int cc = (op >> 3) & 7;
      if (cond(cc)) {
        pc_ = addr;
      }
      return 0;
    }

    case 0xE9: // JP (HL/IX/IY)
      pc_ = addr_hl(index_prefix);
      return 0;

    case 0xCD: { // CALL nn
      const u16 addr = fetch_u16();
      push_u16(pc_);
      pc_ = addr;
      return 0;
    }

    case 0xC4:
    case 0xCC:
    case 0xD4:
    case 0xDC:
    case 0xE4:
    case 0xEC:
    case 0xF4:
    case 0xFC: { // CALL cc,nn
      const u16 addr = fetch_u16();
      const int cc = (op >> 3) & 7;
      if (cond(cc)) {
        push_u16(pc_);
        pc_ = addr;
      }
      return 0;
    }

    case 0xC9: // RET
      pc_ = pop_u16();
      return 0;

    case 0xC0:
    case 0xC8:
    case 0xD0:
    case 0xD8:
    case 0xE0:
    case 0xE8:
    case 0xF0:
    case 0xF8: { // RET cc
      const int cc = (op >> 3) & 7;
      if (cond(cc)) {
        pc_ = pop_u16();
      }
      return 0;
    }

    case 0xC7:
    case 0xCF:
    case 0xD7:
    case 0xDF:
    case 0xE7:
    case 0xEF:
    case 0xF7:
    case 0xFF: { // RST p
      const u16 vec = static_cast<u16>(op & 0x38);
      push_u16(pc_);
      pc_ = vec;
      return 0;
    }

    case 0xD3: { // OUT (n),A
      const u8 n = fetch_byte();
      io_write(static_cast<u16>((a_ << 8) | n), a_);
      return 0;
    }
    case 0xDB: { // IN A,(n)
      const u8 n = fetch_byte();
      a_ = io_read(static_cast<u16>((a_ << 8) | n));
      f_ = static_cast<u8>((f_ & FLAG_C) | szp_[a_]);
      return 0;
    }

    case 0xE6:
      alu_and(fetch_byte());
      return 0;
    case 0xEE:
      alu_xor(fetch_byte());
      return 0;
    case 0xF6:
      alu_or(fetch_byte());
      return 0;
    case 0xFE:
      alu_cp(fetch_byte());
      return 0;

    case 0xC6:
      alu_add(fetch_byte(), false);
      return 0;
    case 0xCE:
      alu_add(fetch_byte(), true);
      return 0;
    case 0xD6:
      alu_sub(fetch_byte(), false);
      return 0;
    case 0xDE:
      alu_sub(fetch_byte(), true);
      return 0;

    case 0xF3: // DI
      iff1_ = false;
      iff2_ = false;
      return 0;

    case 0xFB: // EI (delayed one instruction)
      ei_delay_ = true;
      return 0;

    case 0xEB: { // EX DE,HL (DD/FD versions behave as EX DE,IX/IY on many Z80s)
      const u16 tmp = de();
      if (index_prefix == 0) {
        set_de(hl());
        set_hl(tmp);
      } else {
        set_de(index_reg(index_prefix));
        index_reg(index_prefix) = tmp;
      }
      return 0;
    }

    case 0xD9: // EXX
      std::swap(b_, b2_);
      std::swap(c_, c2_);
      std::swap(d_, d2_);
      std::swap(e_, e2_);
      std::swap(h_, h2_);
      std::swap(l_, l2_);
      return 0;

    case 0xE3: { // EX (SP),HL/IX/IY
      const u8 lo = mem_read(sp_);
      const u8 hi = mem_read(static_cast<u16>(sp_ + 1));
      const u16 memv = static_cast<u16>((hi << 8) | lo);
      const u16 regv = reg16(2, index_prefix);
      mem_write(sp_, get_lo(regv));
      mem_write(static_cast<u16>(sp_ + 1), get_hi(regv));
      set_reg16(2, index_prefix, memv);
      return 0;
    }

    case 0xF9: // LD SP,HL/IX/IY
      sp_ = reg16(2, index_prefix);
      return 0;

    case 0xC5:
    case 0xD5:
    case 0xE5:
    case 0xF5: { // PUSH rr (AF uses rp==3)
      const int rp = (op >> 4) & 3;
      push_u16(rp == 3 ? af() : reg16(rp, index_prefix));
      return 0;
    }
    case 0xC1:
    case 0xD1:
    case 0xE1:
    case 0xF1: { // POP rr
      const int rp = (op >> 4) & 3;
      const u16 v = pop_u16();
      if (rp == 3) {
        set_af(v);
      } else {
        set_reg16(rp, index_prefix, v);
      }
      return 0;
    }

    default:
      trap("illegal opcode " + hex16(op));
      return 0;
  }
}

u64 Z80::step() {
  if (trapped_) {
    return 0;
  }

  step_cycles_ = 0;

  // EI enables maskable interrupts after the *following* instruction completes.
  // While the delay is active, INT is blocked for one instruction boundary.
  const bool block_int_this_step = ei_delay_;
  const bool apply_ei_after = ei_delay_;
  ei_delay_ = false;

  // Interrupt sampling at instruction boundaries.
  if (irq_ != nullptr) {
    if (irq_->consume_nmi_pulse()) {
      halt_ = false;
      iff2_ = iff1_;
      iff1_ = false;
      push_u16(pc_);
      pc_ = 0x0066;
      total_cycles_ += step_cycles_;
      return step_cycles_;
    }

    if (!block_int_this_step && iff1_ && irq_->int_line()) {
      halt_ = false;
      iff1_ = false;
      iff2_ = false;

      const u8 vec = irq_->int_vector();
      irq_->ack_int();

      if (im_ == 0) {
        if ((vec & 0xC7) != 0xC7) {
          trap("IM0 unsupported vector " + hex16(vec));
        } else {
          push_u16(pc_);
          pc_ = static_cast<u16>(vec & 0x38);
        }
      } else if (im_ == 1) {
        push_u16(pc_);
        pc_ = 0x0038;
      } else { // IM 2
        const u16 ptr = static_cast<u16>((static_cast<u16>(i_) << 8) | vec);
        const u8 lo = mem_read(ptr);
        const u8 hi = mem_read(static_cast<u16>(ptr + 1));
        push_u16(pc_);
        pc_ = static_cast<u16>((hi << 8) | lo);
      }

      total_cycles_ += step_cycles_;
      return step_cycles_;
    }
  }

  if (halt_) {
    step_cycles_ += 4;
    if (apply_ei_after) {
      iff1_ = true;
      iff2_ = true;
    }
    total_cycles_ += step_cycles_;
    return step_cycles_;
  }

  const u16 pc_before = pc_;
  u8 index_prefix = 0;

  u8 op = fetch_op();
  while (op == 0xDD || op == 0xFD) {
    index_prefix = op;
    op = fetch_op();
  }

  if (trace_) {
    std::cerr << std::hex << std::uppercase << std::setw(4) << std::setfill('0')
              << static_cast<unsigned>(pc_before) << " OP=" << std::setw(2)
              << static_cast<unsigned>(op) << "\n";
  }

  if (op == 0xCB) {
    if (index_prefix != 0) {
      const auto disp = static_cast<std::int8_t>(fetch_byte());
      const u8 cbop = fetch_op();
      const u16 addr = addr_hl_disp(index_prefix, disp);
      const int x = (cbop >> 6) & 3;
      const int y = (cbop >> 3) & 7;
      const int z = cbop & 7;

      u8 v = mem_read(addr);

      auto write_back = [&](u8 new_v) {
        mem_write(addr, new_v);
        if (z != 6) {
          set_reg8(z, 0, new_v);
        }
      };

      if (x == 0) { // rot/shift
        u8 res = v;
        u8 carry = 0;
        switch (y) {
          case 0:
            carry = static_cast<u8>((v >> 7) & 1);
            res = static_cast<u8>((v << 1) | carry);
            break;
          case 1:
            carry = static_cast<u8>(v & 1);
            res = static_cast<u8>((v >> 1) | (carry << 7));
            break;
          case 2: {
            carry = static_cast<u8>((v >> 7) & 1);
            const u8 c = (f_ & FLAG_C) ? 1 : 0;
            res = static_cast<u8>((v << 1) | c);
            break;
          }
          case 3: {
            carry = static_cast<u8>(v & 1);
            const u8 c = (f_ & FLAG_C) ? 1 : 0;
            res = static_cast<u8>((v >> 1) | (c << 7));
            break;
          }
          case 4:
            carry = static_cast<u8>((v >> 7) & 1);
            res = static_cast<u8>(v << 1);
            break;
          case 5:
            carry = static_cast<u8>(v & 1);
            res = static_cast<u8>((v >> 1) | (v & 0x80));
            break;
          case 6:
            carry = static_cast<u8>((v >> 7) & 1);
            res = static_cast<u8>((v << 1) | 0x01);
            break;
          case 7:
            carry = static_cast<u8>(v & 1);
            res = static_cast<u8>(v >> 1);
            break;
          default:
            break;
        }
        f_ = static_cast<u8>(szp_[res] | (carry ? FLAG_C : 0));
        write_back(res);
      } else if (x == 1) { // BIT
        const u8 mask = static_cast<u8>(1U << y);
        u8 f = static_cast<u8>((f_ & FLAG_C) | FLAG_H);
        if ((v & mask) == 0) {
          f |= FLAG_Z | FLAG_PV;
        }
        if (y == 7 && (v & 0x80)) {
          f |= FLAG_S;
        }
        f = static_cast<u8>(f | (v & (FLAG_X | FLAG_Y)));
        f_ = f;
      } else if (x == 2) { // RES
        v = static_cast<u8>(v & ~(1U << y));
        write_back(v);
      } else { // SET
        v = static_cast<u8>(v | (1U << y));
        write_back(v);
      }
    } else {
      execute_cb(fetch_op());
    }
  } else if (op == 0xED) {
    execute_ed(fetch_op());
  } else {
    execute_base(op, index_prefix);
  }

  if (apply_ei_after) {
    iff1_ = true;
    iff2_ = true;
  }

  total_cycles_ += step_cycles_;
  return step_cycles_;
}

} // namespace carbon_sim
