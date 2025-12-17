#pragma once

#include <array>
#include <cstdint>
#include <string_view>
#include <vector>

#include "carbon_sim/bus.h"
#include "carbon_sim/devices/block_disk.h"

namespace carbon_sim {

class CpmDiskDevice final : public Device {
public:
  static constexpr std::size_t kSectorSize = 128;

  explicit CpmDiskDevice(u16 base_port);

  std::string_view name() const override { return "CpmDiskDevice"; }
  std::vector<IoRange> io_ranges() const override;

  u8 io_read(u16 port) override;
  void io_write(u16 port, u8 value) override;

  void attach_disk(int drive, BlockDisk* disk);

private:
  enum class Mode { Idle, Read, Write };

  u16 base_port_ = 0;
  std::array<BlockDisk*, 4> disks_ = {nullptr, nullptr, nullptr, nullptr};
  u8 drive_ = 0;

  std::array<u8, 4> lba_ = {0, 0, 0, 0};

  Mode mode_ = Mode::Idle;
  bool drq_ = false;
  bool err_ = false;
  std::array<u8, kSectorSize> buffer_ = {};
  std::size_t index_ = 0;

  u32 lba_u32() const;
  BlockDisk* current_disk() const;
  void start_read();
  void start_write();
  void finish_write_if_ready();
};

} // namespace carbon_sim

