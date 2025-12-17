#include <filesystem>
#include <fstream>
#include <iostream>
#include <sstream>
#include <string>
#include <vector>

#include "carbon_sim/platforms/cpm22.h"
#include "carbon_sim/platforms/machine.h"
#include "carbon_sim/platforms/romwbw.h"
#include "carbon_sim/sim_config.h"

namespace carbon_sim {

static void write_file(const std::filesystem::path& path, const std::vector<u8>& bytes) {
  std::ofstream f(path, std::ios::binary | std::ios::out | std::ios::trunc);
  if (!f) {
    throw std::runtime_error("failed to create file: " + path.string());
  }
  if (!bytes.empty()) {
    f.write(reinterpret_cast<const char*>(bytes.data()), static_cast<std::streamsize>(bytes.size()));
  }
}

static void touch_file(const std::filesystem::path& path) {
  std::ofstream f(path, std::ios::binary | std::ios::out | std::ios::app);
  if (!f) {
    throw std::runtime_error("failed to create file: " + path.string());
  }
}

static std::string run_to_halt(std::unique_ptr<Machine> machine, std::uint64_t max_cycles) {
  machine->bus.reset();
  machine->cpu->reset();

  std::uint64_t cycles = 0;
  while (!machine->cpu->trapped() && cycles < max_cycles) {
    const auto step = machine->cpu->step();
    if (step == 0) {
      break;
    }
    machine->bus.tick(step);
    cycles += step;
    if (machine->cpu->halted()) {
      break;
    }
  }

  if (machine->cpu->trapped()) {
    throw std::runtime_error(std::string("CPU trap: ") + std::string(machine->cpu->trap_reason()));
  }
  return {};
}

static bool contains(const std::string& haystack, const std::string& needle) {
  return haystack.find(needle) != std::string::npos;
}

static int smoke_cpm22(const std::filesystem::path& temp_dir) {
  // Z80 ROM stub:
  // - prints "CPM22 STUB OK\r\n" to UART0 (port 0x00)
  // - HALT
  const std::vector<u8> rom = {
      0x31, 0xFF, 0xFF, 0x21, 0x12, 0x00, 0x7E, 0xB7, 0x28, 0x05, 0xD3, 0x00,
      0x23, 0x18, 0xF7, 0x76, 0x18, 0xFE, 0x43, 0x50, 0x4D, 0x32, 0x32, 0x20,
      0x53, 0x54, 0x55, 0x42, 0x20, 0x4F, 0x4B, 0x0D, 0x0A, 0x00,
  };

  const auto rom_path = temp_dir / "cpm22_stub.rom";
  const auto disk_path = temp_dir / "cpm22_stub.dsk";

  write_file(rom_path, rom);
  touch_file(disk_path);

  SimConfig cfg;
  cfg.platform = "cpm22";
  cfg.rom_path = rom_path.string();
  cfg.disk_paths[0] = disk_path.string();
  cfg.max_cycles = 200000;

  std::ostringstream out;
  auto machine = create_platform_cpm22(cfg, out);
  run_to_halt(std::move(machine), cfg.max_cycles);

  if (!contains(out.str(), "CPM22 STUB OK")) {
    std::cerr << "cpm22 smoke: missing banner\n";
    return 1;
  }
  return 0;
}

static int smoke_romwbw(const std::filesystem::path& temp_dir) {
  // Z80 ROM stub:
  // - prints "RomWBW STUB OK\r\n" to SIO channel A (port 0x80)
  // - HALT
  // Same structure as the cpm22 stub, just OUT to 0x80 and different banner.
  const std::vector<u8> rom = {
      0x31, 0xFF, 0xFF, 0x21, 0x12, 0x00, 0x7E, 0xB7, 0x28, 0x05, 0xD3, 0x80,
      0x23, 0x18, 0xF7, 0x76, 0x18, 0xFE, 0x52, 0x6F, 0x6D, 0x57, 0x42, 0x57,
      0x20, 0x53, 0x54, 0x55, 0x42, 0x20, 0x4F, 0x4B, 0x0D, 0x0A, 0x00,
  };

  const auto rom_path = temp_dir / "romwbw_stub.rom";
  const auto disk_path = temp_dir / "romwbw_stub.img";

  write_file(rom_path, rom);
  touch_file(disk_path);

  SimConfig cfg;
  cfg.platform = "romwbw";
  cfg.rom_path = rom_path.string();
  cfg.disk_paths[0] = disk_path.string();
  cfg.max_cycles = 200000;

  std::ostringstream out;
  auto machine = create_platform_romwbw(cfg, out);
  run_to_halt(std::move(machine), cfg.max_cycles);

  if (!contains(out.str(), "RomWBW STUB OK")) {
    std::cerr << "romwbw smoke: missing banner\n";
    return 1;
  }
  return 0;
}

} // namespace carbon_sim

int main() {
  try {
    const auto temp_dir = std::filesystem::temp_directory_path() / "carbon_sim_smoke";
    std::filesystem::create_directories(temp_dir);

    int rc = 0;
    rc |= carbon_sim::smoke_cpm22(temp_dir);
    rc |= carbon_sim::smoke_romwbw(temp_dir);
    return rc;
  } catch (const std::exception& e) {
    std::cerr << "smoke test error: " << e.what() << "\n";
    return 1;
  }
}

