#include "carbon_sim/devices/block_disk.h"

#include <algorithm>
#include <vector>

namespace carbon_sim {

static constexpr u8 kFillByte = 0xE5;

BlockDisk::BlockDisk(std::string path, bool read_only) : path_(std::move(path)), read_only_(read_only) {
  std::ios::openmode mode = std::ios::binary | std::ios::in;
  if (!read_only_) {
    mode |= std::ios::out;
  }
  file_.open(path_, mode);
  if (!file_.is_open() && !read_only_) {
    // Create the file if it doesn't exist yet.
    std::ofstream create(path_, std::ios::binary | std::ios::out);
    create.close();
    file_.open(path_, mode);
  }
}

BlockDisk::~BlockDisk() {
  if (file_.is_open()) {
    file_.flush();
    file_.close();
  }
}

u64 BlockDisk::size_bytes() {
  if (!file_.is_open()) {
    return 0;
  }
  const auto cur = file_.tellg();
  file_.seekg(0, std::ios::end);
  const auto end = file_.tellg();
  file_.seekg(cur, std::ios::beg);
  if (end < 0) {
    return 0;
  }
  return static_cast<u64>(end);
}

bool BlockDisk::ensure_size(u64 size) {
  if (!file_.is_open() || read_only_) {
    return false;
  }
  const u64 cur_size = size_bytes();
  if (size <= cur_size) {
    return true;
  }

  file_.seekp(0, std::ios::end);
  const u64 missing = size - cur_size;
  std::vector<u8> pad(static_cast<std::size_t>(std::min<u64>(missing, 4096)), kFillByte);
  u64 remaining = missing;
  while (remaining != 0) {
    const auto chunk = static_cast<std::size_t>(std::min<u64>(remaining, pad.size()));
    file_.write(reinterpret_cast<const char*>(pad.data()), static_cast<std::streamsize>(chunk));
    if (!file_) {
      return false;
    }
    remaining -= chunk;
  }
  file_.flush();
  return true;
}

bool BlockDisk::read_bytes(u64 offset, u8* dst, std::size_t len) {
  if (!file_.is_open()) {
    return false;
  }

  const u64 end = offset + static_cast<u64>(len);
  const u64 cur_size = size_bytes();

  std::fill(dst, dst + len, kFillByte);
  if (offset >= cur_size) {
    return true;
  }

  const u64 readable = std::min<u64>(cur_size - offset, len);
  file_.seekg(static_cast<std::streamoff>(offset), std::ios::beg);
  file_.read(reinterpret_cast<char*>(dst), static_cast<std::streamsize>(readable));
  return true;
}

bool BlockDisk::write_bytes(u64 offset, const u8* src, std::size_t len) {
  if (!file_.is_open() || read_only_) {
    return false;
  }
  const u64 end = offset + static_cast<u64>(len);
  if (!ensure_size(end)) {
    return false;
  }
  file_.seekp(static_cast<std::streamoff>(offset), std::ios::beg);
  file_.write(reinterpret_cast<const char*>(src), static_cast<std::streamsize>(len));
  file_.flush();
  return static_cast<bool>(file_);
}

} // namespace carbon_sim
