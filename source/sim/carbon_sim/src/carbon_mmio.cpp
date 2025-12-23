#include "carbon_sim/devices/carbon_mmio.h"

namespace carbon_sim {

CarbonMmioRegs::CarbonMmioRegs(u16 base_addr, std::uint32_t signature_reset, std::ostream* uart_out)
    : base_addr_(base_addr),
      signature_reset_(signature_reset),
      signature_(signature_reset),
      uart_out_(uart_out) {}

void CarbonMmioRegs::reset() {
  signature_ = signature_reset_;
  poweroff_ = false;
}

bool CarbonMmioRegs::in_range(u16 addr) const {
  return addr >= base_addr_ && addr < static_cast<u16>(base_addr_ + kWindowBytes);
}

std::optional<u8> CarbonMmioRegs::mem_read(u16 addr) {
  if (!in_range(addr)) {
    return std::nullopt;
  }
  const u16 off = static_cast<u16>(addr - base_addr_);
  if (off < 4) {
    const unsigned shift = static_cast<unsigned>(off * 8);
    return static_cast<u8>((signature_ >> shift) & 0xFFu);
  }
  return 0x00;
}

bool CarbonMmioRegs::mem_write(u16 addr, u8 value) {
  if (!in_range(addr)) {
    return false;
  }
  const u16 off = static_cast<u16>(addr - base_addr_);
  if (off < 4) {
    const unsigned shift = static_cast<unsigned>(off * 8);
    const std::uint32_t mask = 0xFFu << shift;
    signature_ = (signature_ & ~mask) | (static_cast<std::uint32_t>(value) << shift);
    return true;
  }
  if (off >= kPowerOffOff && off < static_cast<u16>(kPowerOffOff + 4)) {
    poweroff_ = true;
    return true;
  }
  if (off == kUartTxOff) {
    if (uart_out_ != nullptr) {
      uart_out_->put(static_cast<char>(value));
      uart_out_->flush();
    }
    return true;
  }
  return true;
}

} // namespace carbon_sim
