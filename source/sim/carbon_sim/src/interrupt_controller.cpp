#include "carbon_sim/devices/interrupt_controller.h"

namespace carbon_sim {

void InterruptController::reset() {
  int_line_ = false;
  int_vector_ = 0xFF;
  nmi_pulse_ = false;
}

void InterruptController::request_int(u8 vector) {
  int_line_ = true;
  int_vector_ = vector;
}

void InterruptController::ack_int() {
  int_line_ = false;
}

void InterruptController::pulse_nmi() {
  nmi_pulse_ = true;
}

bool InterruptController::consume_nmi_pulse() {
  if (!nmi_pulse_) {
    return false;
  }
  nmi_pulse_ = false;
  return true;
}

} // namespace carbon_sim

