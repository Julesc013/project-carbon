#pragma once

#include <cstdint>
#include <optional>
#include <string_view>
#include <vector>

#include "carbon_sim/bus.h"

namespace carbon_sim {

class BootRomOverlay final : public Device {
public:
  BootRomOverlay(u16 base_addr, std::vector<u8> image, u16 control_port);

  std::string_view name() const override { return "BootRomOverlay"; }
  void reset() override { enabled_ = true; }

  std::vector<IoRange> io_ranges() const override;
  u8 io_read(u16 port) override;
  void io_write(u16 port, u8 value) override;

  std::optional<u8> mem_read(u16 addr) override;

  bool enabled() const { return enabled_; }

private:
  u16 base_addr_ = 0;
  u16 control_port_ = 0;
  std::vector<u8> rom_;
  bool enabled_ = true;
};

} // namespace carbon_sim

