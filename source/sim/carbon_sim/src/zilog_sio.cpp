#include "carbon_sim/devices/zilog_sio.h"

namespace carbon_sim {

ZilogSio::ZilogSio(u16 base_port, std::ostream& out) : base_port_(base_port), out_(&out) {}

std::vector<IoRange> ZilogSio::io_ranges() const {
  return {{base_port_, static_cast<u16>(base_port_ + 3)}};
}

ZilogSio::Channel& ZilogSio::chan_for_port(u16 port) {
  const u16 offset = static_cast<u16>(port - base_port_);
  return (offset >= 2) ? ch_b_ : ch_a_;
}

bool ZilogSio::is_ctrl_port(u16 port) const {
  const u16 offset = static_cast<u16>(port - base_port_);
  return (offset & 1U) == 1U;
}

bool ZilogSio::is_data_port(u16 port) const {
  const u16 offset = static_cast<u16>(port - base_port_);
  return (offset & 1U) == 0U;
}

u8 ZilogSio::read_rr0(Channel& ch) const {
  // RR0 (subset):
  // bit0: RX character available
  // bit2: TX buffer empty
  u8 v = 0x04;
  if (!ch.rx.empty()) {
    v |= 0x01;
  }
  return v;
}

u8 ZilogSio::io_read(u16 port) {
  auto& ch = chan_for_port(port);
  if (is_data_port(port)) {
    if (ch.rx.empty()) {
      return 0x00;
    }
    const u8 v = ch.rx.front();
    ch.rx.pop_front();
    return v;
  }

  // Control port: RR0 by default.
  if (ch.selected_reg == 0) {
    return read_rr0(ch);
  }
  // Unimplemented read registers return 0.
  ch.selected_reg = 0;
  return 0x00;
}

void ZilogSio::io_write(u16 port, u8 value) {
  auto& ch = chan_for_port(port);
  if (is_data_port(port)) {
    if (out_ != nullptr) {
      out_->put(static_cast<char>(value));
      out_->flush();
    }
    return;
  }

  // Very small subset of the SIO control protocol:
  // - First write selects a WR register (bits 0..2) for the next write.
  // - Second write stores into that WR register.
  if (ch.selected_reg != 0) {
    ch.wr[ch.selected_reg & 7] = value;
    ch.selected_reg = 0;
    return;
  }

  const u8 sel = static_cast<u8>(value & 0x07);
  ch.selected_reg = sel;

  // Common reset commands are ignored for now; keep RX FIFO intact.
}

void ZilogSio::feed_input(std::string_view bytes) {
  for (unsigned char c : bytes) {
    ch_a_.rx.push_back(static_cast<u8>(c));
  }
}

} // namespace carbon_sim

