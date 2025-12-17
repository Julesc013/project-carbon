#pragma once

#include <array>
#include <cstdint>
#include <optional>
#include <string>
#include <string_view>

#include "carbon_sim/bus.h"

namespace carbon_sim {

class InterruptController;

class Z80 {
public:
  explicit Z80(Bus& bus, InterruptController* irq = nullptr);

  void reset();
  u64 step();

  bool halted() const { return halt_; }
  bool trapped() const { return trapped_; }
  std::string_view trap_reason() const { return trap_reason_; }

  u64 total_cycles() const { return total_cycles_; }

  u16 pc() const { return pc_; }
  void set_pc(u16 pc) { pc_ = pc; }

  u16 sp() const { return sp_; }
  void set_sp(u16 sp) { sp_ = sp; }

  void set_trace(bool enable) { trace_ = enable; }
  void set_irq_controller(InterruptController* irq) { irq_ = irq; }

private:
  static constexpr u8 FLAG_S = 0x80;
  static constexpr u8 FLAG_Z = 0x40;
  static constexpr u8 FLAG_Y = 0x20;
  static constexpr u8 FLAG_H = 0x10;
  static constexpr u8 FLAG_X = 0x08;
  static constexpr u8 FLAG_PV = 0x04;
  static constexpr u8 FLAG_N = 0x02;
  static constexpr u8 FLAG_C = 0x01;

  Bus& bus_;
  InterruptController* irq_ = nullptr;

  u8 a_ = 0;
  u8 f_ = 0;
  u8 b_ = 0;
  u8 c_ = 0;
  u8 d_ = 0;
  u8 e_ = 0;
  u8 h_ = 0;
  u8 l_ = 0;

  u8 a2_ = 0;
  u8 f2_ = 0;
  u8 b2_ = 0;
  u8 c2_ = 0;
  u8 d2_ = 0;
  u8 e2_ = 0;
  u8 h2_ = 0;
  u8 l2_ = 0;

  u16 ix_ = 0;
  u16 iy_ = 0;
  u16 sp_ = 0;
  u16 pc_ = 0;

  u8 i_ = 0;
  u8 r_ = 0;

  bool iff1_ = false;
  bool iff2_ = false;
  u8 im_ = 0;
  bool halt_ = false;
  bool ei_delay_ = false;

  bool trapped_ = false;
  std::string trap_reason_;

  bool trace_ = false;

  u64 step_cycles_ = 0;
  u64 total_cycles_ = 0;

  std::array<u8, 256> szp_ = {};

  void init_tables();
  bool parity(u8 value) const;

  u8 fetch_op();
  u8 fetch_byte();
  u16 fetch_u16();

  u8 mem_read(u16 addr);
  void mem_write(u16 addr, u8 value);
  u8 io_read(u16 port);
  void io_write(u16 port, u8 value);

  void push_u16(u16 value);
  u16 pop_u16();

  void trap(std::string reason);

  u16 bc() const { return static_cast<u16>((b_ << 8) | c_); }
  u16 de() const { return static_cast<u16>((d_ << 8) | e_); }
  u16 hl() const { return static_cast<u16>((h_ << 8) | l_); }
  u16 af() const { return static_cast<u16>((a_ << 8) | f_); }

  void set_bc(u16 v) {
    b_ = static_cast<u8>(v >> 8);
    c_ = static_cast<u8>(v & 0xFF);
  }
  void set_de(u16 v) {
    d_ = static_cast<u8>(v >> 8);
    e_ = static_cast<u8>(v & 0xFF);
  }
  void set_hl(u16 v) {
    h_ = static_cast<u8>(v >> 8);
    l_ = static_cast<u8>(v & 0xFF);
  }
  void set_af(u16 v) {
    a_ = static_cast<u8>(v >> 8);
    f_ = static_cast<u8>(v & 0xFF);
  }

  u8 get_hi(u16 v) const { return static_cast<u8>(v >> 8); }
  u8 get_lo(u16 v) const { return static_cast<u8>(v & 0xFF); }
  void set_hi(u16& v, u8 hi) { v = static_cast<u16>((v & 0x00FF) | (hi << 8)); }
  void set_lo(u16& v, u8 lo) { v = static_cast<u16>((v & 0xFF00) | lo); }

  u16& index_reg(u8 prefix);

  u8 reg8(int r, u8 index_prefix) const;
  void set_reg8(int r, u8 index_prefix, u8 value);
  u16 reg16(int rp, u8 index_prefix) const;
  void set_reg16(int rp, u8 index_prefix, u16 value);

  u16 addr_hl(u8 index_prefix) const;
  u16 addr_hl_disp(u8 index_prefix, std::int8_t disp) const;

  u8 read_r(int r, u8 index_prefix, std::optional<std::int8_t> disp);
  void write_r(int r, u8 index_prefix, std::optional<std::int8_t> disp, u8 value);

  void alu_add(u8 value, bool with_carry);
  void alu_sub(u8 value, bool with_carry);
  void alu_and(u8 value);
  void alu_or(u8 value);
  void alu_xor(u8 value);
  void alu_cp(u8 value);

  u8 inc8(u8 value);
  u8 dec8(u8 value);

  u16 add16(u16 lhs, u16 rhs);
  u16 adc16(u16 lhs, u16 rhs);
  u16 sbc16(u16 lhs, u16 rhs);

  u64 execute_base(u8 op, u8 index_prefix);
  u64 execute_cb(u8 op);
  u64 execute_ed(u8 op);
};

} // namespace carbon_sim
