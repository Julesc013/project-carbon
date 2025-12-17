#include "carbon_sim/rtl/verilator_backend.h"

#include <iostream>

#ifdef CARBON_SIM_ENABLE_VERILATOR
#include <verilated.h>
#endif

namespace carbon_sim {

bool VerilatorBackend::built() {
#ifdef CARBON_SIM_ENABLE_VERILATOR
  return true;
#else
  return false;
#endif
}

std::string VerilatorBackend::info() {
#ifdef CARBON_SIM_ENABLE_VERILATOR
  return "verilator-backend=preview";
#else
  return "verilator-backend=disabled";
#endif
}

int VerilatorBackend::run(const SimConfig& /*cfg*/) {
#ifdef CARBON_SIM_ENABLE_VERILATOR
  std::cerr << "carbon-sim: Verilator backend is a preview scaffold and is not wired to the RTL yet.\n";
  return 2;
#else
  std::cerr << "carbon-sim: built without Verilator backend support.\n";
  return 2;
#endif
}

} // namespace carbon_sim

