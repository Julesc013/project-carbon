#pragma once

#include <array>
#include <cstdint>
#include <vector>

#include "carbon_sim/bus.h"

namespace carbon_sim {

class CarbonDMA final : public Device {
public:
  CarbonDMA(u16 base_port, Bus* bus);

  std::string_view name() const override { return "CarbonDMA"; }
  std::vector<IoRange> io_ranges() const override;

  u8 io_read(u16 port) override;
  void io_write(u16 port, u8 value) override;

  std::optional<u8> mem_read(u16 addr) override;
  bool mem_write(u16 addr, u8 value) override;

private:
  struct Channel {
    std::uint64_t src = 0;
    std::uint64_t dst = 0;
    std::uint32_t len = 0;
    std::uint32_t ctrl = 0;
    std::uint32_t attr = 0;
    std::uint32_t fill = 0;
    bool busy = false;
    bool done = false;
    bool err = false;
  };

  u16 base_port_ = 0;
  Bus* bus_ = nullptr;

  std::uint32_t cfg_enable_ = 1;
  std::uint32_t ch_sel_ = 0;
  std::array<Channel, 4> channels_ = {};

  u8 read_byte(u16 offset);
  void write_byte(u16 offset, u8 value);
  std::uint32_t read_reg(u16 reg);
  void write_reg_byte(u16 reg, u8 value, unsigned shift);

  void start_transfer(Channel& ch);
};

} // namespace carbon_sim
