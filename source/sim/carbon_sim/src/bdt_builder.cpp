#include "carbon_sim/util/bdt_builder.h"

#include <cstddef>
#include <cstdint>

#include "carbon_sim/util/carbon_constants.h"

namespace carbon_sim {

static void write_u16(std::vector<std::uint8_t>& bytes, std::size_t off, std::uint16_t value) {
  bytes.at(off + 0) = static_cast<std::uint8_t>(value & 0xFFu);
  bytes.at(off + 1) = static_cast<std::uint8_t>((value >> 8) & 0xFFu);
}

static void write_u32(std::vector<std::uint8_t>& bytes, std::size_t off, std::uint32_t value) {
  bytes.at(off + 0) = static_cast<std::uint8_t>(value & 0xFFu);
  bytes.at(off + 1) = static_cast<std::uint8_t>((value >> 8) & 0xFFu);
  bytes.at(off + 2) = static_cast<std::uint8_t>((value >> 16) & 0xFFu);
  bytes.at(off + 3) = static_cast<std::uint8_t>((value >> 24) & 0xFFu);
}

static void write_u64(std::vector<std::uint8_t>& bytes, std::size_t off, std::uint64_t value) {
  write_u32(bytes, off, static_cast<std::uint32_t>(value & 0xFFFF'FFFFu));
  write_u32(bytes, off + 4, static_cast<std::uint32_t>((value >> 32) & 0xFFFF'FFFFu));
}

BdtImage build_bdt(const std::vector<DeviceDescriptor>& devices) {
  BdtImage image;
  image.header_size = kBdtHeaderSizeBytes;
  image.entry_size = kBdtEntrySizeBytes;
  image.entry_count = static_cast<std::uint16_t>(devices.size());
  image.total_size = static_cast<std::uint32_t>(image.header_size +
                                                image.entry_count * image.entry_size);

  image.bytes.assign(image.total_size, 0x00);

  write_u32(image.bytes, 0, kBdtSignature);
  write_u16(image.bytes, 4, kBdtHeaderVersion);
  write_u16(image.bytes, 6, image.header_size);
  write_u16(image.bytes, 8, image.entry_size);
  write_u16(image.bytes, 10, image.entry_count);
  write_u32(image.bytes, 12, image.total_size);

  for (std::size_t i = 0; i < devices.size(); ++i) {
    const auto& dev = devices[i];
    const std::size_t base = image.header_size + i * image.entry_size;

    write_u16(image.bytes, base + 0, 1); // desc_version
    write_u16(image.bytes, base + 2, image.entry_size);
    write_u16(image.bytes, base + 4, dev.class_id);
    write_u16(image.bytes, base + 6, dev.subclass_id);
    write_u16(image.bytes, base + 8, dev.vendor_id);
    write_u16(image.bytes, base + 10, dev.device_id);
    write_u16(image.bytes, base + 12, dev.instance_id);
    write_u16(image.bytes, base + 14, dev.revision_id);
    write_u32(image.bytes, base + 16, dev.compat_flags);
    write_u32(image.bytes, base + 20, dev.turbo_flags);
    write_u32(image.bytes, base + 24, dev.feature_word0);
    write_u32(image.bytes, base + 28, dev.feature_word1);
    write_u64(image.bytes, base + 32, dev.csr_base);
    write_u64(image.bytes, base + 40, dev.compat_io_base);
    write_u64(image.bytes, base + 48, dev.mmio_base);
    write_u32(image.bytes, base + 56, dev.mmio_size);
    write_u16(image.bytes, base + 60, dev.queue_count);
    write_u16(image.bytes, base + 62, dev.irq_count);
  }

  return image;
}

} // namespace carbon_sim
