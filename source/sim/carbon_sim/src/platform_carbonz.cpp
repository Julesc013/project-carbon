#include "carbon_sim/platforms/carbonz.h"

#include <array>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>

#include "carbon_sim/devices/carbon_mmio.h"
#include "carbon_sim/devices/carbondma.h"
#include "carbon_sim/devices/carbonio.h"
#include "carbon_sim/devices/ide_disk.h"
#include "carbon_sim/devices/interrupt_controller.h"
#include "carbon_sim/devices/tier_host_stub.h"
#include "carbon_sim/platforms/machine.h"
#include "carbon_sim/util/bdt_builder.h"
#include "carbon_sim/util/carbon_constants.h"
#include "carbon_sim/util/file.h"

namespace carbon_sim {

namespace {

static constexpr u16 kSys16RomBase = 0x0000;
static constexpr std::size_t kSys16RomBytes = 256;
static constexpr u16 kMmioBase = 0xF000;
static constexpr u16 kCarbonIoBase = 0xF100;
static constexpr u16 kCarbonDmaBase = 0xF200;
static constexpr u16 kTierHostBase = 0xF300;
static constexpr u16 kBdtBase = 0xF800;
static constexpr std::size_t kBdtRegionBytes = 512;
static constexpr u16 kIdeBase = 0x0010;

std::vector<u8> build_signature_rom(const std::array<u8, 4>& sig) {
  std::vector<u8> rom(kSys16RomBytes, 0x00);
  std::size_t idx = 0;

  auto emit = [&](u8 v) {
    if (idx < rom.size()) {
      rom[idx++] = v;
    }
  };

  auto emit_store = [&](u16 addr, u8 v) {
    emit(0x3E);
    emit(v);
    emit(0x32);
    emit(static_cast<u8>(addr & 0xFFu));
    emit(static_cast<u8>((addr >> 8) & 0xFFu));
  };

  emit_store(static_cast<u16>(kMmioBase + 0), sig[0]);
  emit_store(static_cast<u16>(kMmioBase + 1), sig[1]);
  emit_store(static_cast<u16>(kMmioBase + 2), sig[2]);
  emit_store(static_cast<u16>(kMmioBase + 3), sig[3]);
  emit_store(static_cast<u16>(kMmioBase + 4), 0x01);
  emit(0x76); // HALT

  return rom;
}

std::vector<u8> load_or_default_rom(const SimConfig& config,
                                    const std::vector<u8>& default_rom,
                                    const char* platform_name) {
  if (config.rom_path.empty()) {
    return default_rom;
  }
  auto rom = read_file_bytes(config.rom_path);
  if (rom.empty()) {
    throw std::runtime_error(std::string(platform_name) + " ROM is empty");
  }
  if (rom.size() > kSys16RomBytes) {
    throw std::runtime_error(std::string(platform_name) + " ROM must be <= 256 bytes");
  }
  rom.resize(kSys16RomBytes, 0x00);
  return rom;
}

void attach_ide_disks(Machine& m, const SimConfig& config) {
  m.ide_disk = &m.bus.add_device<IdeDiskDevice>(kIdeBase);
  for (std::size_t i = 0; i < 2; ++i) {
    if (config.disk_paths[i].empty()) {
      continue;
    }
    m.disks[i] = std::make_unique<BlockDisk>(config.disk_paths[i], /*read_only=*/false);
    if (!m.disks[i]->is_open()) {
      throw std::runtime_error("failed to open disk: " + config.disk_paths[i]);
    }
    m.ide_disk->attach_disk(static_cast<int>(i), m.disks[i].get());
  }
}

void add_fpu_desc(std::vector<DeviceDescriptor>& devices) {
  DeviceDescriptor fpu;
  fpu.class_id = kDevClassFpu;
  fpu.vendor_id = 0;
  fpu.device_id = 0x9513;
  fpu.revision_id = 1;
  fpu.compat_flags = kCompatPolling;
  fpu.turbo_flags = kTurboQueue;
  fpu.queue_count = 1;
  devices.push_back(fpu);
}

void add_carbonio_desc(std::vector<DeviceDescriptor>& devices) {
  DeviceDescriptor carbonio_desc;
  carbonio_desc.class_id = kDevClassUart;
  carbonio_desc.vendor_id = 0;
  carbonio_desc.device_id = 1;
  carbonio_desc.revision_id = 1;
  carbonio_desc.compat_flags = kCompatPolling | kCompatPortIo | kCompatMmio | kCompatWait;
  carbonio_desc.feature_word0 =
      (64u << kFeatWord0RxFifoLsb) |
      (64u << kFeatWord0TxFifoLsb) |
      (2u << kFeatWord0TimerCountLsb);
  carbonio_desc.compat_io_base = kCarbonIoBase;
  carbonio_desc.irq_count = 6;
  devices.push_back(carbonio_desc);
}

void add_carbondma_desc(std::vector<DeviceDescriptor>& devices) {
  DeviceDescriptor carbondma_desc;
  carbondma_desc.class_id = kDevClassDma;
  carbondma_desc.vendor_id = 0;
  carbondma_desc.device_id = 1;
  carbondma_desc.revision_id = 1;
  carbondma_desc.compat_flags = kCompatPolling | kCompatPortIo | kCompatMmio | kCompatWait;
  carbondma_desc.turbo_flags = kTurboQueue | kTurboDma;
  carbondma_desc.feature_word0 = (4u << kFeatWord0DmaChannelsLsb);
  carbondma_desc.feature_word1 = (1u << kFeatWord1QueueCountLsb);
  carbondma_desc.compat_io_base = kCarbonDmaBase;
  carbondma_desc.queue_count = 1;
  devices.push_back(carbondma_desc);
}

std::vector<u8> build_bdt_image(const std::vector<DeviceDescriptor>& devices) {
  const auto bdt = build_bdt(devices);
  if (bdt.bytes.size() > kBdtRegionBytes) {
    throw std::runtime_error("BDT image does not fit in 512-byte region");
  }
  auto image = bdt.bytes;
  image.resize(kBdtRegionBytes, 0x00);
  return image;
}

std::unique_ptr<Machine> create_carbonz_platform(const SimConfig& config,
                                                 std::ostream& console_out,
                                                 const std::vector<u8>& rom_image,
                                                 const std::vector<DeviceDescriptor>& devices,
                                                 bool with_tier_host) {
  auto m = std::make_unique<Machine>();

  m->bus.map_rom(kSys16RomBase, rom_image);
  m->bus.map_rom(kBdtBase, build_bdt_image(devices));
  m->bus.map_ram(0x0000, 65536);

  m->mmio = &m->bus.add_device<CarbonMmioRegs>(kMmioBase, 0u, &console_out);
  m->carbonio = &m->bus.add_device<CarbonIO>(kCarbonIoBase, console_out);
  m->carbondma = &m->bus.add_device<CarbonDMA>(kCarbonDmaBase, &m->bus);

  if (with_tier_host) {
    m->tier_host = &m->bus.add_device<TierHostStub>(kTierHostBase);
  } else {
    m->tier_host = nullptr;
  }

  m->irq = &m->bus.add_device<InterruptController>();
  m->timer = nullptr;
  m->uart0 = nullptr;
  m->sio0 = nullptr;
  m->caps = nullptr;
  m->cpm_disk = nullptr;

  attach_ide_disks(*m, config);

  m->cpu = std::make_unique<Z80>(m->bus, m->irq);
  m->cpu->set_trace(config.trace);

  return m;
}

} // namespace

std::unique_ptr<Machine> create_platform_carbonz80(const SimConfig& config, std::ostream& console_out) {
  std::vector<DeviceDescriptor> devices;
  DeviceDescriptor cpu;
  cpu.class_id = kDevClassCpu;
  cpu.vendor_id = 0;
  cpu.device_id = 0x0085;
  cpu.revision_id = 1;
  devices.push_back(cpu);

  add_fpu_desc(devices);
  add_carbonio_desc(devices);
  add_carbondma_desc(devices);

  const auto default_rom = build_signature_rom({{'Z', '8', '0', '!'}});
  const auto rom = load_or_default_rom(config, default_rom, "CarbonZ80");
  return create_carbonz_platform(config, console_out, rom, devices, /*with_tier_host=*/false);
}

std::unique_ptr<Machine> create_platform_carbonz90(const SimConfig& config, std::ostream& console_out) {
  std::vector<DeviceDescriptor> devices;
  DeviceDescriptor cpu;
  cpu.class_id = kDevClassCpu;
  cpu.vendor_id = 0;
  cpu.device_id = 0x0090;
  cpu.revision_id = 1;
  devices.push_back(cpu);

  add_fpu_desc(devices);
  add_carbonio_desc(devices);
  add_carbondma_desc(devices);

  const auto default_rom = build_signature_rom({{'Z', '9', '0', '!'}});
  const auto rom = load_or_default_rom(config, default_rom, "CarbonZ90");
  return create_carbonz_platform(config, console_out, rom, devices, /*with_tier_host=*/false);
}

std::unique_ptr<Machine> create_platform_carbonz380(const SimConfig& config, std::ostream& console_out) {
  std::vector<DeviceDescriptor> devices;
  DeviceDescriptor cpu;
  cpu.class_id = kDevClassCpu;
  cpu.vendor_id = 0;
  cpu.device_id = 0x0380;
  cpu.revision_id = 1;
  devices.push_back(cpu);

  add_fpu_desc(devices);
  add_carbonio_desc(devices);
  add_carbondma_desc(devices);

  const auto default_rom = build_signature_rom({{'Z', '3', '8', '0'}});
  const auto rom = load_or_default_rom(config, default_rom, "CarbonZ380");
  return create_carbonz_platform(config, console_out, rom, devices, /*with_tier_host=*/false);
}

std::unique_ptr<Machine> create_platform_carbonz480(const SimConfig& config, std::ostream& console_out) {
  std::vector<DeviceDescriptor> devices;
  DeviceDescriptor cpu_z85;
  cpu_z85.class_id = kDevClassCpu;
  cpu_z85.vendor_id = 0;
  cpu_z85.device_id = 0x0085;
  cpu_z85.instance_id = 0;
  cpu_z85.revision_id = 1;
  devices.push_back(cpu_z85);

  DeviceDescriptor cpu_z90 = cpu_z85;
  cpu_z90.device_id = 0x0090;
  cpu_z90.instance_id = 1;
  devices.push_back(cpu_z90);

  DeviceDescriptor cpu_z380 = cpu_z85;
  cpu_z380.device_id = 0x0380;
  cpu_z380.instance_id = 2;
  devices.push_back(cpu_z380);

  DeviceDescriptor cpu_z480 = cpu_z85;
  cpu_z480.device_id = 0x0480;
  cpu_z480.instance_id = 3;
  devices.push_back(cpu_z480);

  add_fpu_desc(devices);
  add_carbonio_desc(devices);
  add_carbondma_desc(devices);

  const auto default_rom = build_signature_rom({{'Z', '4', '8', '0'}});
  const auto rom = load_or_default_rom(config, default_rom, "CarbonZ480");
  return create_carbonz_platform(config, console_out, rom, devices, /*with_tier_host=*/true);
}

} // namespace carbon_sim
