#include "carbon_sim/util/mem_loader.h"

#include <stdexcept>

#include "carbon_sim/util/file.h"

namespace carbon_sim {

std::vector<u8> load_mem_image(const std::string& path) {
  if (path.empty()) {
    return {};
  }
  auto image = read_file_bytes(path);
  if (image.empty()) {
    throw std::runtime_error("memory image is empty: " + path);
  }
  return image;
}

void inject_mem_image(Bus& bus, u16 base_addr, const std::vector<u8>& image) {
  if (image.empty()) {
    return;
  }
  for (std::size_t i = 0; i < image.size(); ++i) {
    const u16 addr = static_cast<u16>(base_addr + i);
    bus.mem_write(addr, image[i]);
  }
}

} // namespace carbon_sim
