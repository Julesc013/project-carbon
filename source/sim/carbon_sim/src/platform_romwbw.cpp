#include "carbon_sim/platforms/romwbw.h"

#include <stdexcept>
#include <utility>

#include "carbon_sim/devices/boot_rom.h"
#include "carbon_sim/devices/caps.h"
#include "carbon_sim/devices/carbondma.h"
#include "carbon_sim/devices/carbonio.h"
#include "carbon_sim/devices/ide_disk.h"
#include "carbon_sim/devices/zilog_sio.h"
#include "carbon_sim/platforms/machine.h"
#include "carbon_sim/util/bdt_builder.h"
#include "carbon_sim/util/bsp_loader.h"
#include "carbon_sim/util/carbon_constants.h"
#include "carbon_sim/util/file.h"
#include "carbon_sim/util/mem_loader.h"

namespace carbon_sim {

static constexpr u16 kRomDisablePort = 0x003F;
static constexpr u16 kSioBasePort = 0x0080;
static constexpr u16 kIdeBasePort = 0x0010;
static constexpr u16 kCapsBasePort = 0xF000;
static constexpr u16 kCarbonIoBasePort = 0xF100;
static constexpr u16 kCarbonDmaBasePort = 0xF200;
static constexpr u16 kBdtBaseAddr = 0xF800;
static constexpr u16 kBdtDisablePort = 0xFFFE;
static constexpr std::size_t kBdtRegionBytes = 1024;

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
  inject_mem_image(m->bus, config.mem_addr, load_mem_image(config.mem_path));
  inject_bsp_blob(m->bus, config.bsp_addr, load_bsp_blob(config.bsp_path));

  m->irq = &m->bus.add_device<InterruptController>();
  m->timer = nullptr;

  // Console: Zilog SIO/2 at ports 0x80-0x83 (channel A used for console).
  // Disk: 8-bit IDE/ATA PIO registers at ports 0x10-0x17.
  auto& sio = m->bus.add_device<ZilogSio>(kSioBasePort, console_out);
  auto& ide = m->bus.add_device<IdeDiskDevice>(kIdeBasePort);

  m->uart0 = nullptr;
  m->sio0 = &sio;
  m->carbonio = &m->bus.add_device<CarbonIO>(kCarbonIoBasePort, console_out);
  m->carbondma = &m->bus.add_device<CarbonDMA>(kCarbonDmaBasePort, &m->bus);

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

  std::vector<DeviceDescriptor> devices;
  DeviceDescriptor carbonio_desc;
  carbonio_desc.class_id = kDevClassUart;
  carbonio_desc.vendor_id = 0;
  carbonio_desc.device_id = 1;
  carbonio_desc.instance_id = 0;
  carbonio_desc.revision_id = 1;
  carbonio_desc.compat_flags = kCompatPolling | kCompatPortIo | kCompatMmio | kCompatWait;
  carbonio_desc.feature_word0 =
      (64u << kFeatWord0RxFifoLsb) |
      (64u << kFeatWord0TxFifoLsb) |
      (2u << kFeatWord0TimerCountLsb);
  carbonio_desc.compat_io_base = kCarbonIoBasePort;
  carbonio_desc.irq_count = 6;
  devices.push_back(carbonio_desc);

  DeviceDescriptor carbondma_desc;
  carbondma_desc.class_id = kDevClassDma;
  carbondma_desc.vendor_id = 0;
  carbondma_desc.device_id = 1;
  carbondma_desc.instance_id = 0;
  carbondma_desc.revision_id = 1;
  carbondma_desc.compat_flags = kCompatPolling | kCompatPortIo | kCompatMmio | kCompatWait;
  carbondma_desc.feature_word0 = (4u << kFeatWord0DmaChannelsLsb);
  carbondma_desc.compat_io_base = kCarbonDmaBasePort;
  devices.push_back(carbondma_desc);

  DeviceDescriptor sio_desc;
  sio_desc.class_id = kDevClassSio;
  sio_desc.vendor_id = 0;
  sio_desc.device_id = 1;
  sio_desc.instance_id = 0;
  sio_desc.revision_id = 1;
  sio_desc.compat_flags = kCompatPolling | kCompatPortIo;
  sio_desc.compat_io_base = kSioBasePort;
  devices.push_back(sio_desc);

  DeviceDescriptor ide_desc;
  ide_desc.class_id = kDevClassBlockStorage;
  ide_desc.vendor_id = 0;
  ide_desc.device_id = 1;
  ide_desc.instance_id = 0;
  ide_desc.revision_id = 1;
  ide_desc.compat_flags = kCompatPolling | kCompatPortIo;
  ide_desc.compat_io_base = kIdeBasePort;
  devices.push_back(ide_desc);

  const auto bdt = build_bdt(devices);
  auto bdt_image = bdt.bytes;
  bdt_image.resize(kBdtRegionBytes, 0x00);
  m->bus.add_device<BootRomOverlay>(kBdtBaseAddr, std::move(bdt_image), kBdtDisablePort);

  BdtCapsInfo caps_info;
  caps_info.base_lo = kBdtBaseAddr;
  caps_info.base_hi = 0;
  caps_info.entry_size = bdt.entry_size;
  caps_info.entry_count = bdt.entry_count;
  caps_info.header_size = bdt.header_size;

  const std::uint32_t features0 =
      kFeatCapsMask | kFeatDeviceModelMask | kFeatBdtMask | kFeatPollingCompleteMask;
  m->caps = &m->bus.add_device<CapsDevice>(kCapsBasePort, caps_info, features0);

  m->cpu = std::make_unique<Z80>(m->bus, m->irq);
  m->cpu->set_trace(config.trace);

  return m;
}

} // namespace carbon_sim
