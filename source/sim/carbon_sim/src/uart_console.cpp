#include "carbon_sim/devices/uart_console.h"

#include <iostream>

namespace carbon_sim {

UARTConsole::UARTConsole(u16 base_port, std::ostream& out) : base_port_(base_port), out_(&out) {}

std::vector<IoRange> UARTConsole::io_ranges() const {
  return {{base_port_, static_cast<u16>(base_port_ + 1)}};
}

u8 UARTConsole::io_read(u16 port) {
  const u16 reg = static_cast<u16>(port - base_port_);
  if (reg == 0) {
    if (rx_.empty()) {
      return 0x00;
    }
    const u8 v = rx_.front();
    rx_.pop_front();
    return v;
  }

  // Status:
  // bit0: RX ready
  // bit1: TX ready
  u8 status = 0;
  if (!rx_.empty()) {
    status |= 0x01;
  }
  status |= 0x02;
  return status;
}

void UARTConsole::io_write(u16 port, u8 value) {
  const u16 reg = static_cast<u16>(port - base_port_);
  if (reg != 0) {
    return;
  }
  if (!out_) {
    return;
  }
  out_->put(static_cast<char>(value));
  out_->flush();
}

void UARTConsole::feed_input(std::string_view bytes) {
  for (unsigned char c : bytes) {
    rx_.push_back(static_cast<u8>(c));
  }
}

} // namespace carbon_sim

