#include "carbon_sim/devices/boot_rom.h"

namespace carbon_sim {

BootRomOverlay::BootRomOverlay(u16 base_addr, std::vector<u8> image, u16 control_port)
    : base_addr_(base_addr), control_port_(control_port), rom_(std::move(image)) {}

std::vector<IoRange> BootRomOverlay::io_ranges() const {
  return {{control_port_, control_port_}};
}

u8 BootRomOverlay::io_read(u16 /*port*/) {
  return static_cast<u8>(enabled_ ? 0x01 : 0x00);
}

void BootRomOverlay::io_write(u16 /*port*/, u8 value) {
  enabled_ = (value & 0x01) != 0;
}

std::optional<u8> BootRomOverlay::mem_read(u16 addr) {
  if (!enabled_ || rom_.empty()) {
    return std::nullopt;
  }
  const u16 end = static_cast<u16>(base_addr_ + rom_.size() - 1);
  if (addr < base_addr_ || addr > end) {
    return std::nullopt;
  }
  return rom_.at(static_cast<std::size_t>(addr - base_addr_));
}

} // namespace carbon_sim

