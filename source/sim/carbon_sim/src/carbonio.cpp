#include "carbon_sim/devices/carbonio.h"

namespace carbon_sim {

static constexpr u16 kCompatWindowSize = 0x0100;

static constexpr u16 kUartDataOff = 0x0000;
static constexpr u16 kUartStatusOff = 0x0004;
static constexpr u16 kUartCtrlOff = 0x0008;
static constexpr u16 kUartRxCountOff = 0x000C;
static constexpr u16 kUartTxCountOff = 0x0010;
static constexpr u16 kUartTsLoOff = 0x0014;
static constexpr u16 kUartTsHiOff = 0x0018;
static constexpr u16 kUartWatermarksOff = 0x001C;

static constexpr u16 kPioInOff = 0x0020;
static constexpr u16 kPioOutOff = 0x0024;
static constexpr u16 kPioDirOff = 0x0028;
static constexpr u16 kPioEdgeRdataOff = 0x002C;
static constexpr u16 kPioEdgeCountOff = 0x0030;
static constexpr u16 kPioFilterCfgOff = 0x0034;
static constexpr u16 kPioMatchCfgOff = 0x0038;

static constexpr u16 kTickLoOff = 0x0040;
static constexpr u16 kTickHiOff = 0x0044;
static constexpr u16 kTimer0LoadOff = 0x0048;
static constexpr u16 kTimer0ValueOff = 0x004C;
static constexpr u16 kTimer0CtrlOff = 0x0050;
static constexpr u16 kTimer0StatusOff = 0x0054;
static constexpr u16 kTimer1LoadOff = 0x0058;
static constexpr u16 kTimer1ValueOff = 0x005C;
static constexpr u16 kTimer1CtrlOff = 0x0060;
static constexpr u16 kTimer1StatusOff = 0x0064;

static constexpr u16 kIrqEnableOff = 0x0070;
static constexpr u16 kIrqPendingOff = 0x0074;
static constexpr u16 kIrqMaskOff = 0x0078;

static constexpr std::uint32_t kUartCtrlEnableBit = 0;
static constexpr std::uint32_t kUartCtrlTsEnBit = 3;
static constexpr std::uint32_t kUartCtrlClrErrBit = 4;

CarbonIO::CarbonIO(u16 base_port, std::ostream& out) : base_port_(base_port), out_(&out) {}

std::vector<IoRange> CarbonIO::io_ranges() const {
  return {{base_port_, static_cast<u16>(base_port_ + kCompatWindowSize - 1)}};
}

u8 CarbonIO::io_read(u16 port) {
  const u16 off = static_cast<u16>(port - base_port_);
  return read_byte(off);
}

void CarbonIO::io_write(u16 port, u8 value) {
  const u16 off = static_cast<u16>(port - base_port_);
  write_byte(off, value);
}

std::optional<u8> CarbonIO::mem_read(u16 addr) {
  if (addr < base_port_ || addr >= static_cast<u16>(base_port_ + kCompatWindowSize)) {
    return std::nullopt;
  }
  return read_byte(static_cast<u16>(addr - base_port_));
}

bool CarbonIO::mem_write(u16 addr, u8 value) {
  if (addr < base_port_ || addr >= static_cast<u16>(base_port_ + kCompatWindowSize)) {
    return false;
  }
  write_byte(static_cast<u16>(addr - base_port_), value);
  return true;
}

void CarbonIO::tick(u64 cycles) {
  tick_counter_ += cycles;

  for (auto& timer : timers_) {
    if ((timer.ctrl & 0x1u) == 0) {
      continue;
    }
    for (u64 i = 0; i < cycles; ++i) {
      if (timer.value == 0) {
        timer.expired = true;
        if (timer.ctrl & 0x2u) {
          timer.value = timer.load;
        } else {
          timer.ctrl &= ~0x1u;
          break;
        }
      } else {
        timer.value -= 1;
      }
    }
  }
}

void CarbonIO::feed_input(std::string_view bytes) {
  for (unsigned char c : bytes) {
    if (rx_fifo_.size() >= 64) {
      rx_overflow_ = true;
      continue;
    }
    rx_fifo_.push_back(static_cast<u8>(c));
    if (uart_ctrl_ & (1u << kUartCtrlTsEnBit)) {
      rx_timestamp_ = tick_counter_;
    }
  }
}

u8 CarbonIO::read_byte(u16 offset) {
  const u16 reg = static_cast<u16>(offset & 0xFFFC);
  const unsigned shift = static_cast<unsigned>((offset & 0x3) * 8);

  if (reg == kUartDataOff) {
    if (shift != 0) {
      return 0x00;
    }
    if (rx_fifo_.empty()) {
      return 0x00;
    }
    const u8 v = rx_fifo_.front();
    rx_fifo_.pop_front();
    return v;
  }

  std::uint32_t value = read_reg(reg);
  return static_cast<u8>((value >> shift) & 0xFFu);
}

void CarbonIO::write_byte(u16 offset, u8 value) {
  const u16 reg = static_cast<u16>(offset & 0xFFFC);
  const unsigned shift = static_cast<unsigned>((offset & 0x3) * 8);

  if (reg == kUartDataOff) {
    if (shift != 0) {
      return;
    }
    if ((uart_ctrl_ & (1u << kUartCtrlEnableBit)) == 0) {
      return;
    }
    if (out_ != nullptr) {
      out_->put(static_cast<char>(value));
      out_->flush();
    }
    return;
  }

  write_reg_byte(reg, value, shift);
}

std::uint32_t CarbonIO::read_reg(u16 reg) {
  switch (reg) {
    case kUartStatusOff: {
      std::uint32_t status = 0;
      if (!rx_fifo_.empty()) {
        status |= 0x1u;
      }
      status |= 0x2u;
      if (rx_overflow_) {
        status |= 0x4u;
      }
      if (tx_overflow_) {
        status |= 0x8u;
      }
      return status;
    }
    case kUartCtrlOff:
      return uart_ctrl_;
    case kUartRxCountOff:
      return static_cast<std::uint32_t>(rx_fifo_.size());
    case kUartTxCountOff:
      return 0;
    case kUartTsLoOff:
      return static_cast<std::uint32_t>(rx_timestamp_ & 0xFFFF'FFFFu);
    case kUartTsHiOff:
      return static_cast<std::uint32_t>((rx_timestamp_ >> 32) & 0xFFFF'FFFFu);
    case kUartWatermarksOff:
      return uart_watermarks_;
    case kPioInOff:
      return 0;
    case kPioOutOff:
      return pio_out_;
    case kPioDirOff:
      return pio_dir_;
    case kPioEdgeRdataOff:
      return 0;
    case kPioEdgeCountOff:
      return 0;
    case kPioFilterCfgOff:
      return 0;
    case kPioMatchCfgOff:
      return 0;
    case kTickLoOff:
      return static_cast<std::uint32_t>(tick_counter_ & 0xFFFF'FFFFu);
    case kTickHiOff:
      return static_cast<std::uint32_t>((tick_counter_ >> 32) & 0xFFFF'FFFFu);
    case kTimer0LoadOff:
      return timers_[0].load;
    case kTimer0ValueOff:
      return timers_[0].value;
    case kTimer0CtrlOff:
      return timers_[0].ctrl;
    case kTimer0StatusOff:
      return timers_[0].expired ? 1u : 0u;
    case kTimer1LoadOff:
      return timers_[1].load;
    case kTimer1ValueOff:
      return timers_[1].value;
    case kTimer1CtrlOff:
      return timers_[1].ctrl;
    case kTimer1StatusOff:
      return timers_[1].expired ? 1u : 0u;
    case kIrqEnableOff:
      return irq_enable_;
    case kIrqPendingOff:
      return pending_irq_bits();
    case kIrqMaskOff:
      return irq_mask_;
    default:
      return 0;
  }
}

void CarbonIO::write_reg_byte(u16 reg, u8 value, unsigned shift) {
  const std::uint32_t mask = 0xFFu << shift;
  switch (reg) {
    case kUartCtrlOff: {
      uart_ctrl_ = (uart_ctrl_ & ~mask) | (static_cast<std::uint32_t>(value) << shift);
      if (uart_ctrl_ & (1u << kUartCtrlClrErrBit)) {
        rx_overflow_ = false;
        tx_overflow_ = false;
        uart_ctrl_ &= ~(1u << kUartCtrlClrErrBit);
      }
      break;
    }
    case kUartWatermarksOff:
      uart_watermarks_ = (uart_watermarks_ & ~mask) | (static_cast<std::uint32_t>(value) << shift);
      break;
    case kPioOutOff:
      pio_out_ = (pio_out_ & ~mask) | (static_cast<std::uint32_t>(value) << shift);
      break;
    case kPioDirOff:
      pio_dir_ = (pio_dir_ & ~mask) | (static_cast<std::uint32_t>(value) << shift);
      break;
    case kTimer0LoadOff:
      timers_[0].load = (timers_[0].load & ~mask) | (static_cast<std::uint32_t>(value) << shift);
      break;
    case kTimer0CtrlOff: {
      if (shift == 0) {
        timers_[0].ctrl = (timers_[0].ctrl & ~0x3u) | (value & 0x3u);
        if (value & 0x4u) {
          timers_[0].value = timers_[0].load;
        }
      }
      break;
    }
    case kTimer0StatusOff:
      timers_[0].expired = false;
      break;
    case kTimer1LoadOff:
      timers_[1].load = (timers_[1].load & ~mask) | (static_cast<std::uint32_t>(value) << shift);
      break;
    case kTimer1CtrlOff: {
      if (shift == 0) {
        timers_[1].ctrl = (timers_[1].ctrl & ~0x3u) | (value & 0x3u);
        if (value & 0x4u) {
          timers_[1].value = timers_[1].load;
        }
      }
      break;
    }
    case kTimer1StatusOff:
      timers_[1].expired = false;
      break;
    case kIrqEnableOff:
      irq_enable_ = (irq_enable_ & ~mask) | (static_cast<std::uint32_t>(value) << shift);
      break;
    case kIrqMaskOff:
      irq_mask_ = (irq_mask_ & ~mask) | (static_cast<std::uint32_t>(value) << shift);
      break;
    default:
      break;
  }
}

std::uint32_t CarbonIO::pending_irq_bits() const {
  std::uint32_t pending = 0;
  const std::uint32_t rx_wm = uart_watermarks_ & 0xFFu;
  const std::uint32_t tx_wm = (uart_watermarks_ >> 8) & 0xFFu;
  const std::size_t rx_count = rx_fifo_.size();
  const std::uint32_t tx_count = 0;

  if (rx_wm != 0 && rx_count >= rx_wm) {
    pending |= (1u << 0);
  }
  if (tx_wm != 0 && tx_count <= tx_wm) {
    pending |= (1u << 1);
  }
  if (timers_[0].expired) {
    pending |= (1u << 4);
  }
  if (timers_[1].expired) {
    pending |= (1u << 5);
  }
  return pending;
}

} // namespace carbon_sim
