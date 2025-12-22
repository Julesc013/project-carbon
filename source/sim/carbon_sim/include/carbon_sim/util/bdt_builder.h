#pragma once

#include <cstdint>
#include <vector>

namespace carbon_sim {

struct DeviceDescriptor {
  std::uint16_t class_id = 0;
  std::uint16_t subclass_id = 0;
  std::uint16_t vendor_id = 0;
  std::uint16_t device_id = 0;
  std::uint16_t instance_id = 0;
  std::uint16_t revision_id = 0;
  std::uint32_t compat_flags = 0;
  std::uint32_t turbo_flags = 0;
  std::uint32_t feature_word0 = 0;
  std::uint32_t feature_word1 = 0;
  std::uint64_t csr_base = 0;
  std::uint64_t compat_io_base = 0;
  std::uint64_t mmio_base = 0;
  std::uint32_t mmio_size = 0;
  std::uint16_t queue_count = 0;
  std::uint16_t irq_count = 0;
};

struct BdtImage {
  std::vector<std::uint8_t> bytes;
  std::uint16_t entry_size = 0;
  std::uint16_t entry_count = 0;
  std::uint16_t header_size = 0;
  std::uint32_t total_size = 0;
};

BdtImage build_bdt(const std::vector<DeviceDescriptor>& devices);

} // namespace carbon_sim
