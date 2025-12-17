#pragma once

#include <cstddef>
#include <fstream>
#include <stdexcept>
#include <string>
#include <vector>

#include "carbon_sim/bus.h"

namespace carbon_sim {

inline std::vector<u8> read_file_bytes(const std::string& path) {
  std::ifstream file(path, std::ios::binary);
  if (!file) {
    throw std::runtime_error("failed to open file: " + path);
  }
  file.seekg(0, std::ios::end);
  const auto size = static_cast<std::size_t>(file.tellg());
  file.seekg(0, std::ios::beg);
  std::vector<u8> data(size);
  if (size != 0) {
    file.read(reinterpret_cast<char*>(data.data()), static_cast<std::streamsize>(size));
    if (!file) {
      throw std::runtime_error("failed to read file: " + path);
    }
  }
  return data;
}

} // namespace carbon_sim

