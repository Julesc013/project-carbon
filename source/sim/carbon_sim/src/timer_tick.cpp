#include "carbon_sim/devices/timer_tick.h"

namespace carbon_sim {

TimerTick::TimerTick(u16 base_port, InterruptController* irq, u64 cycles_per_tick)
    : base_port_(base_port), irq_(irq), cycles_per_tick_(cycles_per_tick) {}

std::vector<IoRange> TimerTick::io_ranges() const {
  return {{base_port_, static_cast<u16>(base_port_ + 4)}};
}

u8 TimerTick::io_read(u16 port) {
  const u16 reg = static_cast<u16>(port - base_port_);
  switch (reg) {
    case 0:
      return static_cast<u8>(tick_count_ & 0xFF);
    case 1:
      return static_cast<u8>((tick_count_ >> 8) & 0xFF);
    case 2:
      return static_cast<u8>((tick_count_ >> 16) & 0xFF);
    case 3:
      return static_cast<u8>((tick_count_ >> 24) & 0xFF);
    case 4:
      return static_cast<u8>((irq_enable_ ? 0x01 : 0x00) | 0x80);
    default:
      return 0x00;
  }
}

void TimerTick::io_write(u16 port, u8 value) {
  const u16 reg = static_cast<u16>(port - base_port_);
  if (reg == 4) {
    irq_enable_ = (value & 0x01) != 0;
    irq_vector_ = value;
    return;
  }
  if (reg == 0) {
    tick_count_ = 0;
    accum_ = 0;
  }
}

void TimerTick::tick(u64 cycles) {
  if (cycles_per_tick_ == 0) {
    return;
  }

  accum_ += cycles;
  while (accum_ >= cycles_per_tick_) {
    accum_ -= cycles_per_tick_;
    ++tick_count_;
    if (irq_enable_ && irq_ != nullptr && !irq_->int_line()) {
      irq_->request_int(irq_vector_);
    }
  }
}

} // namespace carbon_sim

