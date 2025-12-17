#include "carbon_sim/platforms/cpm22.h"

#include <stdexcept>
#include <utility>

#include "carbon_sim/devices/boot_rom.h"
#include "carbon_sim/platforms/machine.h"
#include "carbon_sim/util/file.h"

namespace carbon_sim {

static constexpr u16 kRomDisablePort = 0x003F;
static constexpr u16 kUart0BasePort = 0x0000;
static constexpr u16 kDiskBasePort = 0x0010;
static constexpr u16 kTimerBasePort = 0x0020;

std::unique_ptr<Machine> create_platform_cpm22(const SimConfig& config, std::ostream& console_out) {
  if (config.rom_path.empty()) {
    throw std::runtime_error("--rom is required for platform cpm22");
  }
  if (config.disk_paths[0].empty()) {
    throw std::runtime_error("--disk0 is required for platform cpm22");
  }

  auto rom = read_file_bytes(config.rom_path);
  if (rom.empty()) {
    throw std::runtime_error("ROM is empty");
  }
  if (rom.size() > 16 * 1024) {
    throw std::runtime_error("CP/M platform ROM must be <= 16 KiB");
  }

  auto m = std::make_unique<Machine>();

  // Base memory: 64 KiB RAM. Boot ROM overlays reads at reset until disabled.
  m->bus.map_ram(0x0000, 65536);
  m->bus.add_device<BootRomOverlay>(0x0000, std::move(rom), kRomDisablePort);

  m->irq = &m->bus.add_device<InterruptController>();
  m->timer = &m->bus.add_device<TimerTick>(kTimerBasePort, m->irq, /*cycles_per_tick=*/500000);

  m->uart0 = &m->bus.add_device<UARTConsole>(kUart0BasePort, console_out);
  m->sio0 = nullptr;

  m->cpm_disk = &m->bus.add_device<CpmDiskDevice>(kDiskBasePort);

  m->disks[0] = std::make_unique<BlockDisk>(config.disk_paths[0], /*read_only=*/false);
  if (!m->disks[0]->is_open()) {
    throw std::runtime_error("failed to open disk0: " + config.disk_paths[0]);
  }
  m->cpm_disk->attach_disk(0, m->disks[0].get());

  for (std::size_t i = 1; i < m->disks.size(); ++i) {
    if (config.disk_paths[i].empty()) {
      continue;
    }
    m->disks[i] = std::make_unique<BlockDisk>(config.disk_paths[i], /*read_only=*/false);
    if (!m->disks[i]->is_open()) {
      throw std::runtime_error("failed to open disk: " + config.disk_paths[i]);
    }
    m->cpm_disk->attach_disk(static_cast<int>(i), m->disks[i].get());
  }

  m->cpu = std::make_unique<Z80>(m->bus, m->irq);
  m->cpu->set_trace(config.trace);

  return m;
}

} // namespace carbon_sim
