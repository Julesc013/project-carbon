#pragma once

#include <array>
#include <cstdint>
#include <string>

namespace carbon_sim {

struct SimConfig {
  std::string platform; // "cpm22" | "romwbw" | "carbonz80" | "carbonz90" | "carbonz380" | "carbonz480"
  std::string rom_path;
  std::string bsp_path;
  std::array<std::string, 4> disk_paths = {};

  std::uint16_t bsp_addr = 0xFF00;

  bool trace = false;
  bool turbo = false;
  bool verilator = false;

  std::uint64_t max_cycles = 0; // 0 = unlimited
};

} // namespace carbon_sim
