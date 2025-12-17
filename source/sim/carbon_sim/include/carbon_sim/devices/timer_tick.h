#pragma once

#include <cstdint>
#include <string_view>

#include "carbon_sim/bus.h"
#include "carbon_sim/devices/interrupt_controller.h"

namespace carbon_sim {

class TimerTick final : public Device {
public:
  TimerTick(u16 base_port, InterruptController* irq, u64 cycles_per_tick);

  std::string_view name() const override { return "TimerTick"; }
  std::vector<IoRange> io_ranges() const override;

  u8 io_read(u16 port) override;
  void io_write(u16 port, u8 value) override;
  void tick(u64 cycles) override;

private:
  u16 base_port_ = 0;
  InterruptController* irq_ = nullptr;
  u64 cycles_per_tick_ = 0;

  u64 accum_ = 0;
  u32 tick_count_ = 0;
  bool irq_enable_ = false;
  u8 irq_vector_ = 0xFF;
};

} // namespace carbon_sim

