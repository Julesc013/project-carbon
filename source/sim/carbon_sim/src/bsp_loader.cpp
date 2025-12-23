#include "carbon_sim/util/bsp_loader.h"

#include <stdexcept>

#include "carbon_sim/util/file.h"

namespace carbon_sim {

std::vector<u8> load_bsp_blob(const std::string& path) {
  if (path.empty()) {
    return {};
  }
  auto blob = read_file_bytes(path);
  if (blob.empty()) {
    throw std::runtime_error("BSP blob is empty: " + path);
  }
  return blob;
}

void inject_bsp_blob(Bus& bus, u16 base_addr, const std::vector<u8>& blob) {
  if (blob.empty()) {
    return;
  }
  for (std::size_t i = 0; i < blob.size(); ++i) {
    const u16 addr = static_cast<u16>(base_addr + i);
    bus.mem_write(addr, blob[i]);
  }
}

} // namespace carbon_sim
