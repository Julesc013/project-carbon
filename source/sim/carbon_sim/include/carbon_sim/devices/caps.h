#pragma once

#include <array>
#include <cstdint>

#include "carbon_sim/bus.h"

namespace carbon_sim {

struct BdtCapsInfo {
  std::uint32_t base_lo = 0;
  std::uint32_t base_hi = 0;
  std::uint16_t entry_size = 0;
  std::uint16_t entry_count = 0;
  std::uint16_t header_size = 0;
};

class CapsDevice final : public Device {
public:
  CapsDevice(u16 base_port, BdtCapsInfo bdt_info, std::uint32_t features0);

  std::string_view name() const override { return "CapsDevice"; }
  std::vector<IoRange> io_ranges() const override;

  u8 io_read(u16 port) override;
  void io_write(u16 port, u8 value) override;

private:
  u16 base_port_ = 0;
  BdtCapsInfo bdt_info_ = {};
  std::uint32_t features0_ = 0;
  std::uint32_t leaf_id_ = 0;

  u8 read_byte(u16 offset) const;
  void write_byte(u16 offset, u8 value);
  std::uint32_t read_reg(u16 reg) const;
  std::array<std::uint32_t, 4> read_leaf(std::uint32_t leaf) const;
};

} // namespace carbon_sim
