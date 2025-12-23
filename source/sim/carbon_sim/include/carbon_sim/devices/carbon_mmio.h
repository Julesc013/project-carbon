#pragma once

#include <cstdint>
#include <optional>
#include <ostream>
#include <string_view>

#include "carbon_sim/bus.h"

namespace carbon_sim {

class CarbonMmioRegs final : public Device {
public:
  CarbonMmioRegs(u16 base_addr, std::uint32_t signature_reset, std::ostream* uart_out);

  std::string_view name() const override { return "CarbonMmioRegs"; }
  void reset() override;

  std::optional<u8> mem_read(u16 addr) override;
  bool mem_write(u16 addr, u8 value) override;

  std::uint32_t signature() const { return signature_; }
  bool poweroff() const { return poweroff_; }

private:
  static constexpr u16 kWindowBytes = 0x0100;
  static constexpr u16 kSigOff = 0x0000;
  static constexpr u16 kPowerOffOff = 0x0004;
  static constexpr u16 kUartTxOff = 0x0008;

  u16 base_addr_ = 0;
  std::uint32_t signature_reset_ = 0;
  std::uint32_t signature_ = 0;
  bool poweroff_ = false;
  std::ostream* uart_out_ = nullptr;

  bool in_range(u16 addr) const;
};

} // namespace carbon_sim
