#include "carbon_sim/devices/caps.h"

#include <array>

#include "carbon_sim/util/carbon_constants.h"

namespace carbon_sim {

static constexpr std::uint32_t kMaxStandardLeaf = 4;
static constexpr std::uint32_t kDiscoveryFormatVersion = 1;

static constexpr std::uint8_t kTierLadderZ80 = 0;
static constexpr std::uint8_t kTierCurrent = 2; // P2 Z80
static constexpr std::uint8_t kTierMax = 7;     // P7 Z480

static std::uint32_t pack_chars(const char* s) {
  return static_cast<std::uint32_t>(static_cast<std::uint8_t>(s[0])) |
         (static_cast<std::uint32_t>(static_cast<std::uint8_t>(s[1])) << 8) |
         (static_cast<std::uint32_t>(static_cast<std::uint8_t>(s[2])) << 16) |
         (static_cast<std::uint32_t>(static_cast<std::uint8_t>(s[3])) << 24);
}

CapsDevice::CapsDevice(u16 base_port, BdtCapsInfo bdt_info, std::uint32_t features0)
    : base_port_(base_port), bdt_info_(bdt_info), features0_(features0) {}

std::vector<IoRange> CapsDevice::io_ranges() const {
  return {{base_port_, static_cast<u16>(base_port_ + 0x13)}};
}

u8 CapsDevice::io_read(u16 port) {
  const u16 off = static_cast<u16>(port - base_port_);
  return read_byte(off);
}

void CapsDevice::io_write(u16 port, u8 value) {
  const u16 off = static_cast<u16>(port - base_port_);
  write_byte(off, value);
}

u8 CapsDevice::read_byte(u16 offset) const {
  const u16 reg = static_cast<u16>(offset & 0xFFFC);
  const std::uint32_t value = read_reg(reg);
  const unsigned shift = static_cast<unsigned>((offset & 0x3) * 8);
  return static_cast<u8>((value >> shift) & 0xFFu);
}

void CapsDevice::write_byte(u16 offset, u8 value) {
  const u16 reg = static_cast<u16>(offset & 0xFFFC);
  const unsigned shift = static_cast<unsigned>((offset & 0x3) * 8);
  const std::uint32_t mask = 0xFFu << shift;

  if (reg == 0x0000) { // CAPS_INDEX
    leaf_id_ = (leaf_id_ & ~mask) | (static_cast<std::uint32_t>(value) << shift);
  }
}

std::uint32_t CapsDevice::read_reg(u16 reg) const {
  if (reg == 0x0000) { // CAPS_INDEX
    return leaf_id_;
  }
  const std::array<std::uint32_t, 4> leaf = read_leaf(leaf_id_);
  switch (reg) {
    case 0x0004:
      return leaf[0];
    case 0x0008:
      return leaf[1];
    case 0x000C:
      return leaf[2];
    case 0x0010:
      return leaf[3];
    default:
      return 0;
  }
}

std::array<std::uint32_t, 4> CapsDevice::read_leaf(std::uint32_t leaf) const {
  std::array<std::uint32_t, 4> out = {0, 0, 0, 0};
  switch (leaf) {
    case 0x00000000: {
      out[0] = (kMaxStandardLeaf & 0xFFFFu) |
               ((kDiscoveryFormatVersion & 0xFFFFu) << 16);
      out[1] = pack_chars("CARB");
      out[2] = pack_chars("ON_S");
      out[3] = pack_chars("IM  ");
      break;
    }
    case 0x00000001: {
      out[0] = 0;
      out[1] = 0;
      break;
    }
    case 0x00000002: {
      out[0] = static_cast<std::uint32_t>(kTierLadderZ80) |
               (static_cast<std::uint32_t>(kTierCurrent) << 8) |
               (static_cast<std::uint32_t>(kTierMax) << 16);
      out[1] = 0;
      break;
    }
    case 0x00000003: {
      out[0] = features0_;
      break;
    }
    case 0x00000004: {
      out[0] = (static_cast<std::uint32_t>(kBdtHeaderVersion) & 0xFFFFu) |
               (static_cast<std::uint32_t>(bdt_info_.entry_size) << 16);
      out[1] = (static_cast<std::uint32_t>(bdt_info_.entry_count) & 0xFFFFu) |
               (static_cast<std::uint32_t>(bdt_info_.header_size) << 16);
      out[2] = bdt_info_.base_lo;
      out[3] = bdt_info_.base_hi;
      break;
    }
    default:
      break;
  }
  return out;
}

} // namespace carbon_sim
