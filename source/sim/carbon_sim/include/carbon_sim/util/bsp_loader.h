#pragma once

#include <cstdint>
#include <string>
#include <vector>

#include "carbon_sim/bus.h"

namespace carbon_sim {

std::vector<u8> load_bsp_blob(const std::string& path);
void inject_bsp_blob(Bus& bus, u16 base_addr, const std::vector<u8>& blob);

} // namespace carbon_sim
