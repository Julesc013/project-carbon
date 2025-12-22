#include "carbon_sim/devices/carbondma.h"

namespace carbon_sim {

static constexpr u16 kCompatWindowSize = 0x0100;

static constexpr u16 kIdOff = 0x0000;
static constexpr u16 kStatusOff = 0x0004;
static constexpr u16 kCtrlOff = 0x0008;
static constexpr u16 kChSelOff = 0x000C;
static constexpr u16 kChSrcLoOff = 0x0010;
static constexpr u16 kChSrcHiOff = 0x0014;
static constexpr u16 kChDstLoOff = 0x0018;
static constexpr u16 kChDstHiOff = 0x001C;
static constexpr u16 kChLenOff = 0x0020;
static constexpr u16 kChCtrlOff = 0x0024;
static constexpr u16 kChStatusOff = 0x0028;
static constexpr u16 kChAttrOff = 0x002C;
static constexpr u16 kChFillOff = 0x0030;

static constexpr std::uint32_t kCtrlEnableBit = 0;
static constexpr std::uint32_t kCtrlClrErrBit = 1;

static constexpr std::uint32_t kChCtrlStartBit = 0;
static constexpr std::uint32_t kChCtrlFillBit = 1;

static constexpr std::uint32_t kChStatusBusyBit = 0;
static constexpr std::uint32_t kChStatusDoneBit = 1;
static constexpr std::uint32_t kChStatusErrBit = 2;

CarbonDMA::CarbonDMA(u16 base_port, Bus* bus) : base_port_(base_port), bus_(bus) {}

std::vector<IoRange> CarbonDMA::io_ranges() const {
  return {{base_port_, static_cast<u16>(base_port_ + kCompatWindowSize - 1)}};
}

u8 CarbonDMA::io_read(u16 port) {
  const u16 off = static_cast<u16>(port - base_port_);
  return read_byte(off);
}

void CarbonDMA::io_write(u16 port, u8 value) {
  const u16 off = static_cast<u16>(port - base_port_);
  write_byte(off, value);
}

std::optional<u8> CarbonDMA::mem_read(u16 addr) {
  if (addr < base_port_ || addr >= static_cast<u16>(base_port_ + kCompatWindowSize)) {
    return std::nullopt;
  }
  return read_byte(static_cast<u16>(addr - base_port_));
}

bool CarbonDMA::mem_write(u16 addr, u8 value) {
  if (addr < base_port_ || addr >= static_cast<u16>(base_port_ + kCompatWindowSize)) {
    return false;
  }
  write_byte(static_cast<u16>(addr - base_port_), value);
  return true;
}

u8 CarbonDMA::read_byte(u16 offset) {
  const u16 reg = static_cast<u16>(offset & 0xFFFC);
  const std::uint32_t value = read_reg(reg);
  const unsigned shift = static_cast<unsigned>((offset & 0x3) * 8);
  return static_cast<u8>((value >> shift) & 0xFFu);
}

void CarbonDMA::write_byte(u16 offset, u8 value) {
  const u16 reg = static_cast<u16>(offset & 0xFFFC);
  const unsigned shift = static_cast<unsigned>((offset & 0x3) * 8);
  write_reg_byte(reg, value, shift);
}

std::uint32_t CarbonDMA::read_reg(u16 reg) {
  const auto& ch = channels_.at(ch_sel_ & 0x3);
  switch (reg) {
    case kIdOff:
      return 0x0001'0001u;
    case kStatusOff: {
      std::uint32_t status = 0;
      for (const auto& entry : channels_) {
        if (entry.busy) {
          status |= 0x1u;
        }
        if (entry.err) {
          status |= 0x2u;
        }
      }
      return status;
    }
    case kCtrlOff:
      return (cfg_enable_ & 0x1u);
    case kChSelOff:
      return ch_sel_;
    case kChSrcLoOff:
      return static_cast<std::uint32_t>(ch.src & 0xFFFF'FFFFu);
    case kChSrcHiOff:
      return static_cast<std::uint32_t>((ch.src >> 32) & 0xFFFF'FFFFu);
    case kChDstLoOff:
      return static_cast<std::uint32_t>(ch.dst & 0xFFFF'FFFFu);
    case kChDstHiOff:
      return static_cast<std::uint32_t>((ch.dst >> 32) & 0xFFFF'FFFFu);
    case kChLenOff:
      return ch.len;
    case kChCtrlOff:
      return ch.ctrl;
    case kChStatusOff: {
      std::uint32_t st = 0;
      if (ch.busy) {
        st |= (1u << kChStatusBusyBit);
      }
      if (ch.done) {
        st |= (1u << kChStatusDoneBit);
      }
      if (ch.err) {
        st |= (1u << kChStatusErrBit);
      }
      return st;
    }
    case kChAttrOff:
      return ch.attr;
    case kChFillOff:
      return ch.fill;
    default:
      return 0;
  }
}

void CarbonDMA::write_reg_byte(u16 reg, u8 value, unsigned shift) {
  const std::uint32_t mask = 0xFFu << shift;
  auto& ch = channels_.at(ch_sel_ & 0x3);

  switch (reg) {
    case kCtrlOff: {
      cfg_enable_ = (cfg_enable_ & ~mask) | (static_cast<std::uint32_t>(value) << shift);
      if (cfg_enable_ & (1u << kCtrlClrErrBit)) {
        for (auto& entry : channels_) {
          entry.err = false;
          entry.done = false;
        }
        cfg_enable_ &= ~(1u << kCtrlClrErrBit);
      }
      break;
    }
    case kChSelOff:
      ch_sel_ = (ch_sel_ & ~mask) | (static_cast<std::uint32_t>(value) << shift);
      break;
    case kChSrcLoOff:
      ch.src = (ch.src & ~static_cast<std::uint64_t>(mask)) |
               (static_cast<std::uint64_t>(value) << shift);
      break;
    case kChSrcHiOff: {
      const std::uint64_t shifted = static_cast<std::uint64_t>(value) << shift;
      const std::uint64_t mask64 = static_cast<std::uint64_t>(mask) << 32;
      ch.src = (ch.src & ~mask64) | (shifted << 32);
      break;
    }
    case kChDstLoOff:
      ch.dst = (ch.dst & ~static_cast<std::uint64_t>(mask)) |
               (static_cast<std::uint64_t>(value) << shift);
      break;
    case kChDstHiOff: {
      const std::uint64_t shifted = static_cast<std::uint64_t>(value) << shift;
      const std::uint64_t mask64 = static_cast<std::uint64_t>(mask) << 32;
      ch.dst = (ch.dst & ~mask64) | (shifted << 32);
      break;
    }
    case kChLenOff:
      ch.len = (ch.len & ~mask) | (static_cast<std::uint32_t>(value) << shift);
      break;
    case kChCtrlOff: {
      ch.ctrl = (ch.ctrl & ~mask) | (static_cast<std::uint32_t>(value) << shift);
      if (ch.ctrl & (1u << kChCtrlStartBit)) {
        ch.ctrl &= ~(1u << kChCtrlStartBit);
        start_transfer(ch);
      }
      break;
    }
    case kChStatusOff:
      ch.done = false;
      ch.err = false;
      break;
    case kChAttrOff:
      ch.attr = (ch.attr & ~mask) | (static_cast<std::uint32_t>(value) << shift);
      break;
    case kChFillOff:
      ch.fill = (ch.fill & ~mask) | (static_cast<std::uint32_t>(value) << shift);
      break;
    default:
      break;
  }
}

void CarbonDMA::start_transfer(Channel& ch) {
  if (bus_ == nullptr || (cfg_enable_ & (1u << kCtrlEnableBit)) == 0) {
    ch.err = true;
    ch.done = true;
    return;
  }

  ch.busy = true;
  ch.done = false;
  ch.err = false;

  const bool fill = (ch.ctrl & (1u << kChCtrlFillBit)) != 0;
  std::uint64_t src = ch.src;
  std::uint64_t dst = ch.dst;
  std::uint32_t remaining = ch.len;

  while (remaining != 0) {
    u8 byte = 0;
    if (fill) {
      const unsigned shift = static_cast<unsigned>((dst & 0x3) * 8);
      byte = static_cast<u8>((ch.fill >> shift) & 0xFFu);
    } else {
      byte = bus_->mem_read(static_cast<u16>(src));
    }
    bus_->mem_write(static_cast<u16>(dst), byte);
    if (!fill) {
      src += 1;
    }
    dst += 1;
    remaining -= 1;
  }

  ch.src = src;
  ch.dst = dst;
  ch.busy = false;
  ch.done = true;
}

} // namespace carbon_sim
