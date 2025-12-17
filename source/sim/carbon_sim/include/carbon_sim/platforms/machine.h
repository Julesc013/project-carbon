#pragma once

#include <array>
#include <cstdint>
#include <memory>
#include <ostream>
#include <string>

#include "carbon_sim/bus.h"
#include "carbon_sim/cpu/z80.h"
#include "carbon_sim/devices/block_disk.h"
#include "carbon_sim/devices/cpm_disk.h"
#include "carbon_sim/devices/interrupt_controller.h"
#include "carbon_sim/devices/timer_tick.h"
#include "carbon_sim/devices/uart_console.h"
#include "carbon_sim/devices/zilog_sio.h"

namespace carbon_sim {

struct Machine {
  Bus bus;

  InterruptController* irq = nullptr;
  TimerTick* timer = nullptr;
  UARTConsole* uart0 = nullptr;
  ZilogSio* sio0 = nullptr;
  CpmDiskDevice* cpm_disk = nullptr;

  std::array<std::unique_ptr<BlockDisk>, 4> disks;
  std::unique_ptr<Z80> cpu;
};

} // namespace carbon_sim
