#pragma once

#include <array>
#include <cstdint>
#include <memory>
#include <ostream>
#include <string>

#include "carbon_sim/bus.h"
#include "carbon_sim/cpu/z80.h"
#include "carbon_sim/devices/block_disk.h"
#include "carbon_sim/devices/caps.h"
#include "carbon_sim/devices/carbon_mmio.h"
#include "carbon_sim/devices/carbondma.h"
#include "carbon_sim/devices/carbonio.h"
#include "carbon_sim/devices/cpm_disk.h"
#include "carbon_sim/devices/ide_disk.h"
#include "carbon_sim/devices/tier_host_stub.h"
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
  CarbonIO* carbonio = nullptr;
  CarbonDMA* carbondma = nullptr;
  CapsDevice* caps = nullptr;
  CpmDiskDevice* cpm_disk = nullptr;
  IdeDiskDevice* ide_disk = nullptr;
  CarbonMmioRegs* mmio = nullptr;
  TierHostStub* tier_host = nullptr;

  std::array<std::unique_ptr<BlockDisk>, 4> disks;
  std::unique_ptr<Z80> cpu;
};

} // namespace carbon_sim
