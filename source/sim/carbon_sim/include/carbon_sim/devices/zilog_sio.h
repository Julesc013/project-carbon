#pragma once

#include <array>
#include <cstdint>
#include <deque>
#include <ostream>
#include <string_view>

#include "carbon_sim/bus.h"

namespace carbon_sim {

class ZilogSio final : public Device {
public:
  explicit ZilogSio(u16 base_port, std::ostream& out);

  std::string_view name() const override { return "ZilogSio"; }
  std::vector<IoRange> io_ranges() const override;

  u8 io_read(u16 port) override;
  void io_write(u16 port, u8 value) override;

  void feed_input(std::string_view bytes);

private:
  struct Channel {
    std::array<u8, 8> wr = {};
    u8 selected_reg = 0;
    std::deque<u8> rx;
  };

  u16 base_port_ = 0;
  std::ostream* out_ = nullptr;
  Channel ch_a_;
  Channel ch_b_;

  Channel& chan_for_port(u16 port);
  bool is_ctrl_port(u16 port) const;
  bool is_data_port(u16 port) const;
  u8 read_rr0(Channel& ch) const;
};

} // namespace carbon_sim

