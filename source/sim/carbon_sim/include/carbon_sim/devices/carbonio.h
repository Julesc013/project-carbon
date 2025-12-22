#pragma once

#include <array>
#include <cstdint>
#include <deque>
#include <ostream>
#include <string_view>
#include <vector>

#include "carbon_sim/bus.h"

namespace carbon_sim {

class CarbonIO final : public Device {
public:
  CarbonIO(u16 base_port, std::ostream& out);

  std::string_view name() const override { return "CarbonIO"; }
  std::vector<IoRange> io_ranges() const override;

  u8 io_read(u16 port) override;
  void io_write(u16 port, u8 value) override;

  std::optional<u8> mem_read(u16 addr) override;
  bool mem_write(u16 addr, u8 value) override;

  void tick(u64 cycles) override;
  void feed_input(std::string_view bytes);

private:
  struct Timer {
    std::uint32_t load = 0;
    std::uint32_t value = 0;
    std::uint32_t ctrl = 0;
    bool expired = false;
  };

  u16 base_port_ = 0;
  std::ostream* out_ = nullptr;

  std::deque<u8> rx_fifo_;
  std::uint32_t uart_ctrl_ = 0x0000'0001;
  std::uint32_t uart_watermarks_ = 0x0000'0101;
  bool rx_overflow_ = false;
  bool tx_overflow_ = false;
  std::uint64_t rx_timestamp_ = 0;

  std::uint32_t pio_out_ = 0;
  std::uint32_t pio_dir_ = 0;

  std::array<Timer, 2> timers_ = {};
  std::uint64_t tick_counter_ = 0;

  std::uint32_t irq_enable_ = 0;
  std::uint32_t irq_mask_ = 0;

  u8 read_byte(u16 offset);
  void write_byte(u16 offset, u8 value);
  std::uint32_t read_reg(u16 reg);
  void write_reg_byte(u16 reg, u8 value, unsigned shift);
  std::uint32_t pending_irq_bits() const;
};

} // namespace carbon_sim
