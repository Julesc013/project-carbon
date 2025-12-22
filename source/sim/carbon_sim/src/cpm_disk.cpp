#include "carbon_sim/devices/cpm_disk.h"

#include <algorithm>

namespace carbon_sim {

static constexpr u8 STATUS_READY = 0x01;
static constexpr u8 STATUS_ERR = 0x02;
static constexpr u8 STATUS_DRQ = 0x80;

CpmDiskDevice::CpmDiskDevice(u16 base_port) : base_port_(base_port) {
  buffer_.fill(0xE5);
}

std::vector<IoRange> CpmDiskDevice::io_ranges() const {
  return {{base_port_, static_cast<u16>(base_port_ + 7)}};
}

void CpmDiskDevice::attach_disk(int drive, BlockDisk* disk) {
  if (drive < 0 || drive >= static_cast<int>(disks_.size())) {
    return;
  }
  disks_[static_cast<std::size_t>(drive)] = disk;
}

u32 CpmDiskDevice::lba_u32() const {
  return static_cast<u32>(lba_[0]) | (static_cast<u32>(lba_[1]) << 8) |
         (static_cast<u32>(lba_[2]) << 16) | (static_cast<u32>(lba_[3]) << 24);
}

BlockDisk* CpmDiskDevice::current_disk() const {
  const auto idx = static_cast<std::size_t>(drive_ & 0x03);
  return disks_[idx];
}

void CpmDiskDevice::start_read() {
  err_ = false;
  auto* disk = current_disk();
  if (disk == nullptr || !disk->is_open()) {
    err_ = true;
    drq_ = false;
    mode_ = Mode::Idle;
    return;
  }
  const u64 offset = static_cast<u64>(lba_u32()) * kSectorSize;
  if (!disk->read_bytes(offset, buffer_.data(), buffer_.size())) {
    err_ = true;
    drq_ = false;
    mode_ = Mode::Idle;
    return;
  }
  index_ = 0;
  mode_ = Mode::Read;
  drq_ = true;
}

void CpmDiskDevice::start_write() {
  err_ = false;
  auto* disk = current_disk();
  if (disk == nullptr || !disk->is_open() || disk->read_only()) {
    err_ = true;
    drq_ = false;
    mode_ = Mode::Idle;
    return;
  }
  index_ = 0;
  mode_ = Mode::Write;
  drq_ = true;
}

void CpmDiskDevice::finish_write_if_ready() {
  if (mode_ != Mode::Write || index_ < buffer_.size()) {
    return;
  }
  auto* disk = current_disk();
  if (disk == nullptr || !disk->is_open() || disk->read_only()) {
    err_ = true;
  } else {
    const u64 offset = static_cast<u64>(lba_u32()) * kSectorSize;
    if (!disk->write_bytes(offset, buffer_.data(), buffer_.size())) {
      err_ = true;
    }
  }
  drq_ = false;
  mode_ = Mode::Idle;
}

u8 CpmDiskDevice::io_read(u16 port) {
  const u16 reg = static_cast<u16>(port - base_port_);
  switch (reg) {
    case 0: // CMD (reads as 0)
      return 0x00;
    case 1: { // STATUS
      u8 st = 0;
      if (current_disk() != nullptr) {
        st |= STATUS_READY;
      }
      if (err_) {
        st |= STATUS_ERR;
      }
      if (drq_) {
        st |= STATUS_DRQ;
      }
      return st;
    }
    case 2:
    case 3:
    case 4:
    case 5:
      return lba_[static_cast<std::size_t>(reg - 2)];
    case 6: { // DATA
      if (mode_ != Mode::Read || !drq_) {
        return 0xFF;
      }
      const u8 v = buffer_[index_++];
      if (index_ >= buffer_.size()) {
        drq_ = false;
        mode_ = Mode::Idle;
      }
      return v;
    }
    case 7: // DRIVE
      return drive_;
    default:
      return 0xFF;
  }
}

void CpmDiskDevice::io_write(u16 port, u8 value) {
  const u16 reg = static_cast<u16>(port - base_port_);
  switch (reg) {
    case 0: // CMD
      if (value == 0x01) {
        start_read();
      } else if (value == 0x02) {
        start_write();
      } else {
        mode_ = Mode::Idle;
        drq_ = false;
      }
      return;
    case 2:
    case 3:
    case 4:
    case 5:
      lba_[static_cast<std::size_t>(reg - 2)] = value;
      return;
    case 6: // DATA
      if (mode_ != Mode::Write || !drq_) {
        return;
      }
      buffer_[index_++] = value;
      if (index_ >= buffer_.size()) {
        finish_write_if_ready();
      }
      return;
    case 7: // DRIVE
      drive_ = static_cast<u8>(value & 0x03);
      return;
    default:
      return;
  }
}

} // namespace carbon_sim
