#pragma once

#include <cstdint>
#include <deque>
#include <ostream>
#include <string_view>

#include "carbon_sim/bus.h"

namespace carbon_sim {

class UARTConsole final : public Device {
public:
  explicit UARTConsole(u16 base_port, std::ostream& out);

  std::string_view name() const override { return "UARTConsole"; }
  std::vector<IoRange> io_ranges() const override;

  u8 io_read(u16 port) override;
  void io_write(u16 port, u8 value) override;

  void feed_input(std::string_view bytes);

private:
  u16 base_port_ = 0;
  std::ostream* out_ = nullptr;
  std::deque<u8> rx_;
};

} // namespace carbon_sim

