#include "carbon_sim/devices/tier_host_stub.h"

namespace carbon_sim {

TierHostStub::TierHostStub(u16 base_addr) : base_addr_(base_addr) {}

void TierHostStub::reset() {
  req_ = 0;
  active_tier_ = 0;
  active_core_ = tier_to_core(active_tier_);
  stack_depth_ = 0;
  err_invalid_ = false;
  err_overflow_ = false;
  err_underflow_ = false;
  entry_lo_ = 0;
  entry_hi_ = 0;
}

bool TierHostStub::in_range(u16 addr) const {
  return addr >= base_addr_ && addr < static_cast<u16>(base_addr_ + kWindowBytes);
}

u8 TierHostStub::tier_to_core(u8 tier) const {
  if (tier <= 2) {
    return 0;
  }
  if (tier == 3) {
    return 1;
  }
  if (tier <= 6) {
    return 2;
  }
  return 3;
}

std::uint32_t TierHostStub::status_word() const {
  std::uint32_t status = 0;
  status |= static_cast<std::uint32_t>(active_tier_);
  status |= static_cast<std::uint32_t>(stack_depth_) << 8;
  status |= static_cast<std::uint32_t>(active_core_ & 0x3u) << 16;
  if (err_invalid_) {
    status |= (1u << 24);
  }
  if (err_overflow_) {
    status |= (1u << 25);
  }
  if (err_underflow_) {
    status |= (1u << 26);
  }
  return status;
}

void TierHostStub::handle_request(u8 req) {
  const bool retmd = (req & 0x80u) != 0;
  if (retmd) {
    if (stack_depth_ == 0) {
      err_underflow_ = true;
      return;
    }
    stack_depth_--;
    active_tier_ = stack_[stack_depth_];
    active_core_ = tier_to_core(active_tier_);
    return;
  }

  const u8 target = static_cast<u8>(req & 0x7Fu);
  if (target <= active_tier_) {
    err_invalid_ = true;
    return;
  }
  if (stack_depth_ >= kStackDepth) {
    err_overflow_ = true;
    return;
  }
  stack_[stack_depth_] = active_tier_;
  stack_depth_++;
  active_tier_ = target;
  active_core_ = tier_to_core(active_tier_);
}

std::optional<u8> TierHostStub::mem_read(u16 addr) {
  if (!in_range(addr)) {
    return std::nullopt;
  }
  const u16 off = static_cast<u16>(addr - base_addr_);
  if (off >= kStatusOff && off < static_cast<u16>(kStatusOff + 4)) {
    const std::uint32_t status = status_word();
    const unsigned shift = static_cast<unsigned>((off - kStatusOff) * 8);
    return static_cast<u8>((status >> shift) & 0xFFu);
  }
  if (off >= kEntryLoOff && off < static_cast<u16>(kEntryLoOff + 4)) {
    const unsigned shift = static_cast<unsigned>((off - kEntryLoOff) * 8);
    return static_cast<u8>((entry_lo_ >> shift) & 0xFFu);
  }
  if (off >= kEntryHiOff && off < static_cast<u16>(kEntryHiOff + 4)) {
    const unsigned shift = static_cast<unsigned>((off - kEntryHiOff) * 8);
    return static_cast<u8>((entry_hi_ >> shift) & 0xFFu);
  }
  if (off == kReqOff) {
    return req_;
  }
  return 0x00;
}

bool TierHostStub::mem_write(u16 addr, u8 value) {
  if (!in_range(addr)) {
    return false;
  }
  const u16 off = static_cast<u16>(addr - base_addr_);
  if (off == kReqOff) {
    req_ = value;
    handle_request(value);
    return true;
  }
  if (off >= kEntryLoOff && off < static_cast<u16>(kEntryLoOff + 4)) {
    const unsigned shift = static_cast<unsigned>((off - kEntryLoOff) * 8);
    const std::uint32_t mask = 0xFFu << shift;
    entry_lo_ = (entry_lo_ & ~mask) | (static_cast<std::uint32_t>(value) << shift);
    return true;
  }
  if (off >= kEntryHiOff && off < static_cast<u16>(kEntryHiOff + 4)) {
    const unsigned shift = static_cast<unsigned>((off - kEntryHiOff) * 8);
    const std::uint32_t mask = 0xFFu << shift;
    entry_hi_ = (entry_hi_ & ~mask) | (static_cast<std::uint32_t>(value) << shift);
    return true;
  }
  if (off == kCtrlOff) {
    if (value & 0x1u) {
      err_invalid_ = false;
      err_overflow_ = false;
      err_underflow_ = false;
    }
    return true;
  }
  return true;
}

} // namespace carbon_sim
