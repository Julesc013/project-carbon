#include <array>
#include <cstdint>
#include <filesystem>
#include <fstream>
#include <iostream>
#include <sstream>
#include <string>
#include <vector>

#include "carbon_sim/platforms/carbonz.h"
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

static void run_to_halt(Machine& machine, std::uint64_t max_cycles) {
  machine.bus.reset();
  machine.cpu->reset();

  std::uint64_t cycles = 0;
  while (!machine.cpu->trapped() && cycles < max_cycles) {
    const auto step = machine.cpu->step();
    if (step == 0) {
      break;
    }
    machine.bus.tick(step);
    cycles += step;
    if (machine.cpu->halted()) {
      break;
    }
  }

  if (machine.cpu->trapped()) {
    throw std::runtime_error(std::string("CPU trap: ") + std::string(machine.cpu->trap_reason()));
  }
}

static bool contains(const std::string& haystack, const std::string& needle) {
  return haystack.find(needle) != std::string::npos;
}

static void write_u32(Bus& bus, u16 addr, u32 value) {
  bus.mem_write(static_cast<u16>(addr + 0), static_cast<u8>(value & 0xFFu));
  bus.mem_write(static_cast<u16>(addr + 1), static_cast<u8>((value >> 8) & 0xFFu));
  bus.mem_write(static_cast<u16>(addr + 2), static_cast<u8>((value >> 16) & 0xFFu));
  bus.mem_write(static_cast<u16>(addr + 3), static_cast<u8>((value >> 24) & 0xFFu));
}

static u32 read_u32(Bus& bus, u16 addr) {
  const u32 b0 = bus.mem_read(static_cast<u16>(addr + 0));
  const u32 b1 = bus.mem_read(static_cast<u16>(addr + 1));
  const u32 b2 = bus.mem_read(static_cast<u16>(addr + 2));
  const u32 b3 = bus.mem_read(static_cast<u16>(addr + 3));
  return b0 | (b1 << 8) | (b2 << 16) | (b3 << 24);
}

static bool check_signature(Bus& bus, u16 base, const std::array<u8, 4>& sig) {
  for (std::size_t i = 0; i < sig.size(); ++i) {
    if (bus.mem_read(static_cast<u16>(base + i)) != sig[i]) {
      return false;
    }
  }
  return true;
}

static int smoke_cpm22(const std::filesystem::path& temp_dir) {
  // Z80 ROM stub:
  // - prints "CPM22 STUB OK\r\n" to CarbonIO UART (MMIO 0xF100)
  // - HALT
  const std::vector<u8> rom = {
      0x31, 0xFF, 0xFF, 0x21, 0x13, 0x00, 0x7E, 0xB7, 0x28, 0x06, 0x32, 0x00,
      0xF1, 0x23, 0x18, 0xF6, 0x76, 0x18, 0xFE, 0x43, 0x50, 0x4D, 0x32, 0x32,
      0x20, 0x53, 0x54, 0x55, 0x42, 0x20, 0x4F, 0x4B, 0x0D, 0x0A, 0x00,
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
  run_to_halt(*machine, cfg.max_cycles);

  if (!contains(out.str(), "CPM22 STUB OK")) {
    std::cerr << "cpm22 smoke: missing banner\n";
    return 1;
  }

  auto machine2 = create_platform_cpm22(cfg, out);
  machine2->bus.reset();
  const u16 carbonio_base = 0xF100;
  const u32 tick_lo_before = read_u32(machine2->bus, carbonio_base + 0x40);
  const u32 tick_hi_before = read_u32(machine2->bus, carbonio_base + 0x44);
  machine2->bus.tick(1000);
  const u32 tick_lo_after = read_u32(machine2->bus, carbonio_base + 0x40);
  const u32 tick_hi_after = read_u32(machine2->bus, carbonio_base + 0x44);
  const std::uint64_t tick_before = (static_cast<std::uint64_t>(tick_hi_before) << 32) | tick_lo_before;
  const std::uint64_t tick_after = (static_cast<std::uint64_t>(tick_hi_after) << 32) | tick_lo_after;
  if (tick_after <= tick_before) {
    std::cerr << "cpm22 smoke: CarbonIO tick did not advance\n";
    return 1;
  }

  const u16 carbondma_base = 0xF200;
  const u16 dma_src = 0x2000;
  const u16 dma_dst = 0x2100;
  for (u16 i = 0; i < 16; ++i) {
    machine2->bus.mem_write(static_cast<u16>(dma_src + i), static_cast<u8>(0xA0 + i));
    machine2->bus.mem_write(static_cast<u16>(dma_dst + i), 0);
  }
  write_u32(machine2->bus, carbondma_base + 0x08, 0x0000'0001);
  write_u32(machine2->bus, carbondma_base + 0x0C, 0);
  write_u32(machine2->bus, carbondma_base + 0x10, dma_src);
  write_u32(machine2->bus, carbondma_base + 0x18, dma_dst);
  write_u32(machine2->bus, carbondma_base + 0x20, 16);
  write_u32(machine2->bus, carbondma_base + 0x24, 0x0000'0001);
  const u32 dma_status = read_u32(machine2->bus, carbondma_base + 0x28);
  if ((dma_status & (1u << 1)) == 0) {
    std::cerr << "cpm22 smoke: CarbonDMA did not report DONE\n";
    return 1;
  }
  for (u16 i = 0; i < 16; ++i) {
    const u8 v = machine2->bus.mem_read(static_cast<u16>(dma_dst + i));
    if (v != static_cast<u8>(0xA0 + i)) {
      std::cerr << "cpm22 smoke: CarbonDMA copy mismatch at +" << i << "\n";
      return 1;
    }
  }
  return 0;
}

static int smoke_cpm22_memload(const std::filesystem::path& temp_dir) {
  // ROM stub: disable overlay and jump to 0x0100.
  const std::vector<u8> rom = {
      0x3E, 0x00, // MVI A,0
      0xD3, 0x3F, // OUT 0x3F (disable ROM overlay)
      0xC3, 0x00, 0x01 // JMP 0x0100
  };

  // RAM image: program at 0x0100 prints banner via CarbonIO and halts.
  std::vector<u8> mem(65536, 0x00);
  std::size_t pc = 0x0100;
  auto emit = [&](u8 v) { mem[pc++] = v; };
  auto emit_u16 = [&](u16 v) {
    emit(static_cast<u8>(v & 0xFFu));
    emit(static_cast<u8>((v >> 8) & 0xFFu));
  };

  emit(0x31); // LXI SP,0xFFFE
  emit_u16(0xFFFE);
  emit(0x21); // LXI H, msg (patch later)
  const std::size_t msg_addr_pos = pc;
  emit_u16(0x0000);
  const u16 loop_addr = static_cast<u16>(pc);
  emit(0x7E); // MOV A,M
  emit(0xB7); // ORA A
  emit(0xCA); // JZ done (patch later)
  const std::size_t done_addr_pos = pc;
  emit_u16(0x0000);
  emit(0x32); // STA 0xF100
  emit_u16(0xF100);
  emit(0x23); // INX H
  emit(0xC3); // JMP loop
  emit_u16(loop_addr);
  const u16 done_addr = static_cast<u16>(pc);
  emit(0x76); // HALT
  const u16 msg_addr = static_cast<u16>(pc);
  const char* msg = "CPM22 MEM OK\r\n";
  for (const char* p = msg; *p; ++p) {
    emit(static_cast<u8>(*p));
  }
  emit(0x00);
  mem[msg_addr_pos + 0] = static_cast<u8>(msg_addr & 0xFFu);
  mem[msg_addr_pos + 1] = static_cast<u8>((msg_addr >> 8) & 0xFFu);
  mem[done_addr_pos + 0] = static_cast<u8>(done_addr & 0xFFu);
  mem[done_addr_pos + 1] = static_cast<u8>((done_addr >> 8) & 0xFFu);

  const auto rom_path = temp_dir / "cpm22_mem.rom";
  const auto disk_path = temp_dir / "cpm22_mem.dsk";
  const auto mem_path = temp_dir / "cpm22_mem.bin";

  write_file(rom_path, rom);
  touch_file(disk_path);
  write_file(mem_path, mem);

  SimConfig cfg;
  cfg.platform = "cpm22";
  cfg.rom_path = rom_path.string();
  cfg.mem_path = mem_path.string();
  cfg.disk_paths[0] = disk_path.string();
  cfg.max_cycles = 200000;

  std::ostringstream out;
  auto machine = create_platform_cpm22(cfg, out);
  run_to_halt(*machine, cfg.max_cycles);

  if (!contains(out.str(), "CPM22 MEM OK")) {
    std::cerr << "cpm22 memload smoke: missing banner\n";
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
  run_to_halt(*machine, cfg.max_cycles);

  if (!contains(out.str(), "RomWBW STUB OK")) {
    std::cerr << "romwbw smoke: missing banner\n";
    return 1;
  }
  return 0;
}

static int smoke_carbonz80() {
  SimConfig cfg;
  cfg.platform = "carbonz80";
  cfg.max_cycles = 100000;

  std::ostringstream out;
  auto machine = create_platform_carbonz80(cfg, out);
  run_to_halt(*machine, cfg.max_cycles);

  if (!check_signature(machine->bus, 0xF000, {{'Z', '8', '0', '!'}})) {
    std::cerr << "carbonz80 smoke: signature mismatch\n";
    return 1;
  }
  if (machine->mmio != nullptr && !machine->mmio->poweroff()) {
    std::cerr << "carbonz80 smoke: poweroff not latched\n";
    return 1;
  }

  const u16 carbonio_base = 0xF100;
  const u32 tick_lo_before = read_u32(machine->bus, carbonio_base + 0x40);
  const u32 tick_hi_before = read_u32(machine->bus, carbonio_base + 0x44);
  machine->bus.tick(1000);
  const u32 tick_lo_after = read_u32(machine->bus, carbonio_base + 0x40);
  const u32 tick_hi_after = read_u32(machine->bus, carbonio_base + 0x44);
  const std::uint64_t tick_before = (static_cast<std::uint64_t>(tick_hi_before) << 32) | tick_lo_before;
  const std::uint64_t tick_after = (static_cast<std::uint64_t>(tick_hi_after) << 32) | tick_lo_after;
  if (tick_after <= tick_before) {
    std::cerr << "carbonz80 smoke: CarbonIO tick did not advance\n";
    return 1;
  }
  return 0;
}

static int smoke_carbonz90() {
  SimConfig cfg;
  cfg.platform = "carbonz90";
  cfg.max_cycles = 100000;

  std::ostringstream out;
  auto machine = create_platform_carbonz90(cfg, out);
  run_to_halt(*machine, cfg.max_cycles);

  if (!check_signature(machine->bus, 0xF000, {{'Z', '9', '0', '!'}})) {
    std::cerr << "carbonz90 smoke: signature mismatch\n";
    return 1;
  }
  if (machine->mmio != nullptr && !machine->mmio->poweroff()) {
    std::cerr << "carbonz90 smoke: poweroff not latched\n";
    return 1;
  }
  return 0;
}

static int smoke_carbonz380() {
  SimConfig cfg;
  cfg.platform = "carbonz380";
  cfg.max_cycles = 100000;

  std::ostringstream out;
  auto machine = create_platform_carbonz380(cfg, out);
  run_to_halt(*machine, cfg.max_cycles);

  if (!check_signature(machine->bus, 0xF000, {{'Z', '3', '8', '0'}})) {
    std::cerr << "carbonz380 smoke: signature mismatch\n";
    return 1;
  }
  if (machine->mmio != nullptr && !machine->mmio->poweroff()) {
    std::cerr << "carbonz380 smoke: poweroff not latched\n";
    return 1;
  }
  return 0;
}

static int smoke_carbonz480() {
  SimConfig cfg;
  cfg.platform = "carbonz480";
  cfg.max_cycles = 100000;

  std::ostringstream out;
  auto machine = create_platform_carbonz480(cfg, out);
  run_to_halt(*machine, cfg.max_cycles);

  if (!check_signature(machine->bus, 0xF000, {{'Z', '4', '8', '0'}})) {
    std::cerr << "carbonz480 smoke: signature mismatch\n";
    return 1;
  }
  if (machine->mmio != nullptr && !machine->mmio->poweroff()) {
    std::cerr << "carbonz480 smoke: poweroff not latched\n";
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
    rc |= carbon_sim::smoke_cpm22_memload(temp_dir);
    rc |= carbon_sim::smoke_romwbw(temp_dir);
    rc |= carbon_sim::smoke_carbonz80();
    rc |= carbon_sim::smoke_carbonz90();
    rc |= carbon_sim::smoke_carbonz380();
    rc |= carbon_sim::smoke_carbonz480();
    return rc;
  } catch (const std::exception& e) {
    std::cerr << "smoke test error: " << e.what() << "\n";
    return 1;
  }
}
