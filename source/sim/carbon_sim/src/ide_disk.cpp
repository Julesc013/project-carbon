#include "carbon_sim/devices/ide_disk.h"

#include <algorithm>
#include <cstdio>
#include <cstring>

namespace carbon_sim {

static constexpr u8 ATA_STS_ERR = 0x01;
static constexpr u8 ATA_STS_DRQ = 0x08;
static constexpr u8 ATA_STS_DSC = 0x10;
static constexpr u8 ATA_STS_DRDY = 0x40;
static constexpr u8 ATA_STS_BSY = 0x80;

IdeDiskDevice::IdeDiskDevice(u16 base_port) : base_port_(base_port) {
  buffer_.fill(0);
}

std::vector<IoRange> IdeDiskDevice::io_ranges() const {
  return {{base_port_, static_cast<u16>(base_port_ + 7)}};
}

void IdeDiskDevice::attach_disk(int unit, BlockDisk* disk) {
  if (unit < 0 || unit >= static_cast<int>(disks_.size())) {
    return;
  }
  disks_[static_cast<std::size_t>(unit)] = disk;
}

BlockDisk* IdeDiskDevice::current_disk() const {
  const int unit = (drive_head_ & 0x10) ? 1 : 0;
  return disks_[static_cast<std::size_t>(unit)];
}

u32 IdeDiskDevice::current_lba28() const {
  const bool lba = (drive_head_ & 0x40) != 0;
  if (!lba) {
    return 0;
  }
  const u32 lba0 = sector_number_;
  const u32 lba1 = static_cast<u32>(cylinder_low_) << 8;
  const u32 lba2 = static_cast<u32>(cylinder_high_) << 16;
  const u32 lba3 = static_cast<u32>(drive_head_ & 0x0F) << 24;
  return lba0 | lba1 | lba2 | lba3;
}

void IdeDiskDevice::set_error(u8 err) {
  err_ = true;
  error_ = err;
  drq_ = false;
  bsy_ = false;
  mode_ = Mode::None;
}

u8 IdeDiskDevice::status() const {
  u8 s = 0;
  if (err_) {
    s |= ATA_STS_ERR;
  }
  if (drq_) {
    s |= ATA_STS_DRQ;
  }
  s |= ATA_STS_DSC;
  s |= ATA_STS_DRDY;
  if (bsy_) {
    s |= ATA_STS_BSY;
  }
  return s;
}

void IdeDiskDevice::cmd_identify() {
  err_ = false;
  bsy_ = false;
  drq_ = true;
  mode_ = Mode::PioRead;
  index_ = 0;
  sectors_remaining_ = 1;
  buffer_.fill(0);

  // Minimal IDENTIFY DEVICE response (words, little-endian).
  auto put_word = [&](int word, u16 v) {
    const std::size_t i = static_cast<std::size_t>(word) * 2;
    buffer_[i + 0] = static_cast<u8>(v & 0xFF);
    buffer_[i + 1] = static_cast<u8>(v >> 8);
  };

  put_word(0, 0x0040);  // fixed disk
  put_word(49, 0x0200); // LBA supported

  // Total 28-bit sectors: report 16 MiB / 512 = 32768 sectors by default.
  const u32 sectors = 32768;
  put_word(60, static_cast<u16>(sectors & 0xFFFF));
  put_word(61, static_cast<u16>((sectors >> 16) & 0xFFFF));

  auto put_str = [&](int start_word, int words, const char* s) {
    std::array<char, 40> buf{};
    std::snprintf(buf.data(), buf.size(), "%s", s);
    for (int i = 0; i < words; ++i) {
      const char a = buf[static_cast<std::size_t>(i * 2)];
      const char b = buf[static_cast<std::size_t>(i * 2 + 1)];
      put_word(start_word + i, static_cast<u16>((static_cast<u8>(a) << 8) | static_cast<u8>(b)));
    }
  };

  put_str(10, 10, "CARBON-SIM0001");
  put_str(23, 4, "1.0");
  put_str(27, 20, "CARBON SIM IDE DISK");
}

void IdeDiskDevice::load_sector() {
  auto* disk = current_disk();
  if (disk == nullptr || !disk->is_open()) {
    set_error(0x04);
    return;
  }
  const bool lba = (drive_head_ & 0x40) != 0;
  if (!lba) {
    set_error(0x04);
    return;
  }
  const u64 offset = static_cast<u64>(current_lba28()) * kSectorSize;
  if (!disk->read_bytes(offset, buffer_.data(), buffer_.size())) {
    set_error(0x04);
    return;
  }
}

void IdeDiskDevice::commit_sector() {
  auto* disk = current_disk();
  if (disk == nullptr || !disk->is_open() || disk->read_only()) {
    set_error(0x04);
    return;
  }
  const bool lba = (drive_head_ & 0x40) != 0;
  if (!lba) {
    set_error(0x04);
    return;
  }
  const u64 offset = static_cast<u64>(current_lba28()) * kSectorSize;
  if (!disk->write_bytes(offset, buffer_.data(), buffer_.size())) {
    set_error(0x04);
    return;
  }
}

void IdeDiskDevice::advance_lba() {
  const u32 lba = current_lba28();
  const u32 next = lba + 1;
  sector_number_ = static_cast<u8>(next & 0xFF);
  cylinder_low_ = static_cast<u8>((next >> 8) & 0xFF);
  cylinder_high_ = static_cast<u8>((next >> 16) & 0xFF);
  drive_head_ = static_cast<u8>((drive_head_ & 0xF0) | ((next >> 24) & 0x0F));
}

void IdeDiskDevice::cmd_read_sectors() {
  err_ = false;
  bsy_ = false;
  const u16 count = sector_count_ == 0 ? 256 : sector_count_;
  sectors_remaining_ = count;

  load_sector();
  if (err_) {
    return;
  }

  mode_ = Mode::PioRead;
  drq_ = true;
  index_ = 0;
}

void IdeDiskDevice::cmd_write_sectors() {
  err_ = false;
  bsy_ = false;
  const u16 count = sector_count_ == 0 ? 256 : sector_count_;
  sectors_remaining_ = count;
  mode_ = Mode::PioWrite;
  drq_ = true;
  index_ = 0;
  buffer_.fill(0);
}

u8 IdeDiskDevice::io_read(u16 port) {
  const u16 reg = static_cast<u16>(port - base_port_);
  switch (reg) {
    case 0: // DATA
      if (!drq_ || mode_ != Mode::PioRead) {
        return 0x00;
      }
      if (index_ >= buffer_.size()) {
        return 0x00;
      }
      {
        const u8 v = buffer_[index_++];
        if (index_ >= buffer_.size()) {
          index_ = 0;
          if (sectors_remaining_ > 0) {
            --sectors_remaining_;
          }
          if (sectors_remaining_ > 0) {
            advance_lba();
            load_sector();
          } else {
            drq_ = false;
            mode_ = Mode::None;
          }
        }
        return v;
      }
    case 1: // ERROR
      return error_;
    case 2: // SECTOR COUNT
      return sector_count_;
    case 3: // SECTOR NUMBER / LBA0
      return sector_number_;
    case 4: // CYL LOW / LBA1
      return cylinder_low_;
    case 5: // CYL HIGH / LBA2
      return cylinder_high_;
    case 6: // DRIVE/HEAD
      return drive_head_;
    case 7: // STATUS
      return status();
    default:
      return 0x00;
  }
}

void IdeDiskDevice::io_write(u16 port, u8 value) {
  const u16 reg = static_cast<u16>(port - base_port_);
  switch (reg) {
    case 0: // DATA
      if (!drq_ || mode_ != Mode::PioWrite) {
        return;
      }
      buffer_[index_++] = value;
      if (index_ >= buffer_.size()) {
        index_ = 0;
        commit_sector();
        if (err_) {
          return;
        }
        if (sectors_remaining_ > 0) {
          --sectors_remaining_;
        }
        if (sectors_remaining_ > 0) {
          advance_lba();
          drq_ = true;
          mode_ = Mode::PioWrite;
        } else {
          drq_ = false;
          mode_ = Mode::None;
        }
      }
      return;

    case 1: // FEATURES
      features_ = value;
      (void)features_;
      return;
    case 2: // SECTOR COUNT
      sector_count_ = value;
      return;
    case 3: // SECTOR NUMBER / LBA0
      sector_number_ = value;
      return;
    case 4: // CYL LOW / LBA1
      cylinder_low_ = value;
      return;
    case 5: // CYL HIGH / LBA2
      cylinder_high_ = value;
      return;
    case 6: // DRIVE/HEAD
      drive_head_ = static_cast<u8>(value | 0xA0);
      return;
    case 7: // COMMAND
      switch (value) {
        case 0xEC:
          cmd_identify();
          break;
        case 0x20:
          cmd_read_sectors();
          break;
        case 0x30:
          cmd_write_sectors();
          break;
        default:
          set_error(0x04);
          break;
      }
      return;
    default:
      return;
  }
}

} // namespace carbon_sim
