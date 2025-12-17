#include "carbon_sim/platforms/romwbw.h"

#include <stdexcept>
#include <utility>

#include "carbon_sim/devices/boot_rom.h"
#include "carbon_sim/devices/ide_disk.h"
#include "carbon_sim/devices/zilog_sio.h"
#include "carbon_sim/platforms/machine.h"
#include "carbon_sim/util/file.h"

namespace carbon_sim {

static constexpr u16 kRomDisablePort = 0x003F;
static constexpr u16 kSioBasePort = 0x0080;
static constexpr u16 kIdeBasePort = 0x0010;
static constexpr u16 kTimerBasePort = 0x0020;

std::unique_ptr<Machine> create_platform_romwbw(const SimConfig& config, std::ostream& console_out) {
  if (config.rom_path.empty()) {
    throw std::runtime_error("--rom is required for platform romwbw");
  }
  if (config.disk_paths[0].empty()) {
    throw std::runtime_error("--disk0 is required for platform romwbw");
  }

  auto rom = read_file_bytes(config.rom_path);
  if (rom.empty()) {
    throw std::runtime_error("ROM is empty");
  }
  if (rom.size() > 32 * 1024) {
    throw std::runtime_error("RomWBW platform ROM must be <= 32 KiB (no banking in v1)");
  }

  auto m = std::make_unique<Machine>();

  // Base memory: 64 KiB RAM; ROM overlays reads at 0x0000.. for the provided image.
  m->bus.map_ram(0x0000, 65536);
  m->bus.add_device<BootRomOverlay>(0x0000, std::move(rom), kRomDisablePort);

  m->irq = &m->bus.add_device<InterruptController>();
  m->timer = &m->bus.add_device<TimerTick>(kTimerBasePort, m->irq, /*cycles_per_tick=*/500000);

  // Console: Zilog SIO/2 at ports 0x80-0x83 (channel A used for console).
  // Disk: 8-bit IDE/ATA PIO registers at ports 0x10-0x17.
  auto& sio = m->bus.add_device<ZilogSio>(kSioBasePort, console_out);
  auto& ide = m->bus.add_device<IdeDiskDevice>(kIdeBasePort);

  m->uart0 = nullptr;
  m->sio0 = &sio;

  m->disks[0] = std::make_unique<BlockDisk>(config.disk_paths[0], /*read_only=*/false);
  if (!m->disks[0]->is_open()) {
    throw std::runtime_error("failed to open disk0: " + config.disk_paths[0]);
  }
  ide.attach_disk(0, m->disks[0].get());

  if (!config.disk_paths[1].empty()) {
    m->disks[1] = std::make_unique<BlockDisk>(config.disk_paths[1], /*read_only=*/false);
    if (!m->disks[1]->is_open()) {
      throw std::runtime_error("failed to open disk1: " + config.disk_paths[1]);
    }
    ide.attach_disk(1, m->disks[1].get());
  }

  m->cpu = std::make_unique<Z80>(m->bus, m->irq);
  m->cpu->set_trace(config.trace);

  return m;
}

} // namespace carbon_sim
