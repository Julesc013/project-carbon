#pragma once

#include <array>
#include <cstddef>
#include <cstdint>
#include <string_view>
#include <vector>

#include "carbon_sim/bus.h"
#include "carbon_sim/devices/block_disk.h"

namespace carbon_sim {

class IdeDiskDevice final : public Device {
public:
  static constexpr std::size_t kSectorSize = 512;

  explicit IdeDiskDevice(u16 base_port);

  std::string_view name() const override { return "IdeDiskDevice"; }
  std::vector<IoRange> io_ranges() const override;

  u8 io_read(u16 port) override;
  void io_write(u16 port, u8 value) override;

  void attach_disk(int unit, BlockDisk* disk);

private:
  enum class Mode { None, PioRead, PioWrite };

  u16 base_port_ = 0;
  std::array<BlockDisk*, 2> disks_ = {nullptr, nullptr};

  u8 features_ = 0;
  u8 error_ = 0;
  u8 sector_count_ = 0;
  u8 sector_number_ = 0;
  u8 cylinder_low_ = 0;
  u8 cylinder_high_ = 0;
  u8 drive_head_ = 0xE0;

  bool bsy_ = false;
  bool drq_ = false;
  bool err_ = false;

  Mode mode_ = Mode::None;
  std::array<u8, kSectorSize> buffer_ = {};
  std::size_t index_ = 0;
  u16 sectors_remaining_ = 0;

  BlockDisk* current_disk() const;
  u32 current_lba28() const;
  void set_error(u8 err);
  u8 status() const;

  void cmd_identify();
  void cmd_read_sectors();
  void cmd_write_sectors();

  void load_sector();
  void commit_sector();
  void advance_lba();
};

} // namespace carbon_sim

