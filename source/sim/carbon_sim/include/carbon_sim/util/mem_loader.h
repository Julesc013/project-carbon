#pragma once

#include <cstdint>
#include <string>
#include <vector>

#include "carbon_sim/bus.h"

namespace carbon_sim {

std::vector<u8> load_mem_image(const std::string& path);
void inject_mem_image(Bus& bus, u16 base_addr, const std::vector<u8>& image);

} // namespace carbon_sim
