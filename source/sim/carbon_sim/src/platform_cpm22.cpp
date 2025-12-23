#include "carbon_sim/platforms/cpm22.h"

#include <stdexcept>
#include <utility>

#include "carbon_sim/devices/boot_rom.h"
#include "carbon_sim/devices/caps.h"
#include "carbon_sim/devices/carbondma.h"
#include "carbon_sim/devices/carbonio.h"
#include "carbon_sim/platforms/machine.h"
#include "carbon_sim/util/bdt_builder.h"
#include "carbon_sim/util/bsp_loader.h"
#include "carbon_sim/util/carbon_constants.h"
#include "carbon_sim/util/file.h"

namespace carbon_sim {

static constexpr u16 kRomDisablePort = 0x003F;
static constexpr u16 kDiskBasePort = 0x0010;
static constexpr u16 kCapsBasePort = 0xF000;
static constexpr u16 kCarbonIoBasePort = 0xF100;
static constexpr u16 kCarbonDmaBasePort = 0xF200;
static constexpr u16 kBdtBaseAddr = 0xF800;
static constexpr u16 kBdtDisablePort = 0xFFFE;
static constexpr std::size_t kBdtRegionBytes = 1024;

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
  inject_bsp_blob(m->bus, config.bsp_addr, load_bsp_blob(config.bsp_path));

  m->irq = &m->bus.add_device<InterruptController>();
  m->timer = nullptr;

  m->uart0 = nullptr;
  m->sio0 = nullptr;

  m->carbonio = &m->bus.add_device<CarbonIO>(kCarbonIoBasePort, console_out);
  m->carbondma = &m->bus.add_device<CarbonDMA>(kCarbonDmaBasePort, &m->bus);

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

  DeviceDescriptor disk_desc;
  disk_desc.class_id = kDevClassBlockStorage;
  disk_desc.vendor_id = 0;
  disk_desc.device_id = 1;
  disk_desc.instance_id = 0;
  disk_desc.revision_id = 1;
  disk_desc.compat_flags = kCompatPolling | kCompatPortIo;
  disk_desc.compat_io_base = kDiskBasePort;
  devices.push_back(disk_desc);

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
