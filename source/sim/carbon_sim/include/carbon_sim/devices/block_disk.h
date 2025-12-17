#pragma once

#include <cstddef>
#include <cstdint>
#include <fstream>
#include <string>
#include <string_view>

#include "carbon_sim/bus.h"

namespace carbon_sim {

class BlockDisk {
public:
  explicit BlockDisk(std::string path, bool read_only = false);
  ~BlockDisk();

  BlockDisk(const BlockDisk&) = delete;
  BlockDisk& operator=(const BlockDisk&) = delete;

  const std::string& path() const { return path_; }
  bool read_only() const { return read_only_; }

  bool is_open() const { return file_.is_open(); }

  bool read_bytes(u64 offset, u8* dst, std::size_t len);
  bool write_bytes(u64 offset, const u8* src, std::size_t len);

private:
  u64 size_bytes();
  bool ensure_size(u64 size);

  std::string path_;
  bool read_only_ = false;
  std::fstream file_;
};

} // namespace carbon_sim

