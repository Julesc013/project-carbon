# Platform Profiles

Profiles describe SoC composition targets; they are not CPU tiers.

## PROFILE_CPU_ONLY (0)

- Description: CPU-only target with minimal uncore blocks.
- Required blocks: CPU, CSR, IRQ, DBG.
- Required discovery tables: DISCOVERY_TABLE.
- Required minimum devices: none.
- Legacy Z80 bus adapter: no.
- Safe mode: presented tier forced to P0; MODEFLAGS reset to architectural defaults.

## PROFILE_MCU (1)

- Description: Microcontroller profile with basic I/O and timers.
- Required blocks: CPU, KIO, TIMER, IRQ, CSR, DBG.
- Required discovery tables: DISCOVERY_TABLE, BDT.
- Required minimum devices: UART, TIMER.
- Legacy Z80 bus adapter: no.
- Safe mode: UART console enabled; caches disabled/bypassed; presented tier forced to P0.

## PROFILE_SOC_RETRO (2)

- Description: Retro SoC profile with legacy Z80 bus adapter.
- Required blocks: CPU, KIO, TIMER, IRQ, DMA, STORAGE, CSR, DBG.
- Required discovery tables: DISCOVERY_TABLE, TOPOLOGY_TABLE, BDT.
- Required minimum devices: UART, TIMER.
- Legacy Z80 bus adapter: yes.
- Safe mode: UART console enabled; caches disabled/bypassed; presented tier forced to P0.

## PROFILE_SOC_WORKSTATION (3)

- Description: Workstation SoC profile with storage, DMA, and CAI accelerators.
- Required blocks: CPU, KIO, TIMER, IRQ, DMA, STORAGE, CAI, CSR, DBG.
- Required discovery tables: DISCOVERY_TABLE, TOPOLOGY_TABLE, BDT, LIMITS_TABLE.
- Required minimum devices: UART, TIMER.
- Legacy Z80 bus adapter: no.
- Safe mode: UART console enabled; caches disabled/bypassed; presented tier forced to P0.

## Reserved Ranges

- 4..127: reserved for future standard profiles.
- 128..255: reserved for vendor-specific profiles.
