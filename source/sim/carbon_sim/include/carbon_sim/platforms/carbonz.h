#pragma once

#include <memory>
#include <ostream>

#include "carbon_sim/sim_config.h"

namespace carbon_sim {

class Machine;

std::unique_ptr<Machine> create_platform_carbonz80(const SimConfig& config, std::ostream& console_out);
std::unique_ptr<Machine> create_platform_carbonz90(const SimConfig& config, std::ostream& console_out);
std::unique_ptr<Machine> create_platform_carbonz380(const SimConfig& config, std::ostream& console_out);
std::unique_ptr<Machine> create_platform_carbonz480(const SimConfig& config, std::ostream& console_out);

} // namespace carbon_sim
