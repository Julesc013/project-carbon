#pragma once

#include <array>
#include <cstdint>
#include <optional>
#include <string_view>

#include "carbon_sim/bus.h"

namespace carbon_sim {

class TierHostStub final : public Device {
public:
  explicit TierHostStub(u16 base_addr);

  std::string_view name() const override { return "TierHostStub"; }
  void reset() override;

  std::optional<u8> mem_read(u16 addr) override;
  bool mem_write(u16 addr, u8 value) override;

private:
  static constexpr u16 kWindowBytes = 0x0100;
  static constexpr u16 kReqOff = 0x0000;
  static constexpr u16 kStatusOff = 0x0004;
  static constexpr u16 kEntryLoOff = 0x0008;
  static constexpr u16 kEntryHiOff = 0x000C;
  static constexpr u16 kCtrlOff = 0x0010;

  static constexpr std::size_t kStackDepth = 4;

  u16 base_addr_ = 0;
  u8 req_ = 0;
  u8 active_tier_ = 0;
  u8 stack_depth_ = 0;
  u8 active_core_ = 0;
  bool err_invalid_ = false;
  bool err_overflow_ = false;
  bool err_underflow_ = false;
  std::array<u8, kStackDepth> stack_ = {};
  std::uint32_t entry_lo_ = 0;
  std::uint32_t entry_hi_ = 0;

  bool in_range(u16 addr) const;
  void handle_request(u8 req);
  u8 tier_to_core(u8 tier) const;
  std::uint32_t status_word() const;
};

} // namespace carbon_sim
