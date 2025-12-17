#pragma once

#include <cstdint>
#include <string_view>

#include "carbon_sim/bus.h"

namespace carbon_sim {

class InterruptController final : public Device {
public:
  InterruptController() = default;

  std::string_view name() const override { return "InterruptController"; }
  void reset() override;

  void request_int(u8 vector = 0xFF);
  void ack_int();
  bool int_line() const { return int_line_; }
  u8 int_vector() const { return int_vector_; }

  void pulse_nmi();
  bool consume_nmi_pulse();

private:
  bool int_line_ = false;
  u8 int_vector_ = 0xFF;
  bool nmi_pulse_ = false;
};

} // namespace carbon_sim

