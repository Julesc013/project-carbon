#pragma once

#include <array>
#include <cstdint>
#include <string>

namespace carbon_sim {

struct SimConfig {
  std::string platform; // "cpm1" | "cpm22" | "cpm3" | "romwbw" | "carbonz80" | "carbonz90" | "carbonz380" | "carbonz480"
  std::string rom_path;
  std::string bsp_path;
  std::string mem_path;
  std::array<std::string, 4> disk_paths = {};

  std::uint16_t bsp_addr = 0xFF00;
  std::uint16_t mem_addr = 0x0000;

  bool trace = false;
  bool turbo = false;
  bool verilator = false;

  std::uint64_t max_cycles = 0; // 0 = unlimited
};

} // namespace carbon_sim
