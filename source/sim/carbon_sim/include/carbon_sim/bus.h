#pragma once

#include <array>
#include <cstddef>
#include <cstdint>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

namespace carbon_sim {

using u8 = std::uint8_t;
using u16 = std::uint16_t;
using u32 = std::uint32_t;
using u64 = std::uint64_t;

struct IoRange {
  u16 start = 0;
  u16 end = 0; // inclusive
};

class Device {
public:
  virtual ~Device() = default;

  virtual std::string_view name() const = 0;
  virtual void reset() {}

  virtual std::vector<IoRange> io_ranges() const { return {}; }

  virtual u8 io_read(u16 /*port*/) { return 0xFF; }
  virtual void io_write(u16 /*port*/, u8 /*value*/) {}

  virtual std::optional<u8> mem_read(u16 /*addr*/) { return std::nullopt; }
  virtual bool mem_write(u16 /*addr*/, u8 /*value*/) { return false; }

  virtual void tick(u64 /*cycles*/) {}
};

struct MemRegion {
  u16 start = 0;
  bool readonly = false;
  std::vector<u8> data;

  bool contains(u16 addr) const {
    if (data.empty()) {
      return false;
    }
    const u16 end = static_cast<u16>(start + data.size() - 1);
    return addr >= start && addr <= end;
  }

  u8 read(u16 addr) const {
    return data.at(static_cast<std::size_t>(addr - start));
  }

  void write(u16 addr, u8 value) {
    if (readonly) {
      return;
    }
    data.at(static_cast<std::size_t>(addr - start)) = value;
  }
};

class Bus {
public:
  Bus() { io_map_.fill(nullptr); }

  Bus(const Bus&) = delete;
  Bus& operator=(const Bus&) = delete;

  void reset() {
    for (auto& dev : devices_) {
      dev->reset();
    }
  }

  template <typename T, typename... Args>
  T& add_device(Args&&... args) {
    auto device = std::make_unique<T>(std::forward<Args>(args)...);
    auto* raw = device.get();
    register_io_ranges(*raw);
    devices_.push_back(std::move(device));
    return *raw;
  }

  void map_ram(u16 start, std::size_t size) {
    MemRegion region;
    region.start = start;
    region.readonly = false;
    region.data.resize(size, 0x00);
    regions_.push_back(std::move(region));
  }

  void map_rom(u16 start, std::vector<u8> image) {
    MemRegion region;
    region.start = start;
    region.readonly = true;
    region.data = std::move(image);
    regions_.push_back(std::move(region));
  }

  u8 mem_read(u16 addr) {
    for (auto& dev : devices_) {
      if (auto hooked = dev->mem_read(addr); hooked.has_value()) {
        return *hooked;
      }
    }
    for (auto& region : regions_) {
      if (region.contains(addr)) {
        return region.read(addr);
      }
    }
    return 0xFF;
  }

  void mem_write(u16 addr, u8 value) {
    for (auto& dev : devices_) {
      if (dev->mem_write(addr, value)) {
        return;
      }
    }
    for (auto& region : regions_) {
      if (region.contains(addr)) {
        region.write(addr, value);
        return;
      }
    }
  }

  u8 io_read(u16 port) {
    if (auto* dev = io_map_[port]; dev != nullptr) {
      return dev->io_read(port);
    }
    return 0xFF;
  }

  void io_write(u16 port, u8 value) {
    if (auto* dev = io_map_[port]; dev != nullptr) {
      dev->io_write(port, value);
    }
  }

  void tick(u64 cycles) {
    for (auto& dev : devices_) {
      dev->tick(cycles);
    }
  }

private:
  void register_io_ranges(Device& device) {
    for (const auto& range : device.io_ranges()) {
      if (range.end < range.start) {
        throw std::runtime_error("invalid IO range on device");
      }
      for (u32 port = range.start; port <= range.end; ++port) {
        if (io_map_[port] != nullptr) {
          throw std::runtime_error("IO port conflict registering device");
        }
        io_map_[port] = &device;
      }
    }
  }

  std::vector<std::unique_ptr<Device>> devices_;
  std::vector<MemRegion> regions_;
  std::array<Device*, 65536> io_map_;
};

} // namespace carbon_sim
