#pragma once

#include <string>

#include "carbon_sim/sim_config.h"

namespace carbon_sim {

class VerilatorBackend {
public:
  static bool built();
  static std::string info();
  static int run(const SimConfig& cfg);
};

} // namespace carbon_sim

