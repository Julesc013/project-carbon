# CarbonX96 — Memory Map (v1)

This system instantiates:
- `cpu_8096` with P7 turbo enabled via `MODEUP` (CarbonX96 integration contract)
- `fpu_8097` configured to tier P7 (turbo) via CSR
- `carbonio` (UART/PIO/Timers/IRQ router)
- `carbondma` (4-channel DMA engine)
- Common ROM/RAM/MMIO devices on the fabric

## Fabric address space (20-bit real-mode window)

- **Boot ROM**: `0x0000_0000`–`0x0000_0FFF` (4 KiB, read-only)
- **MMIO (system regs)**: `0x000F_0000`–`0x000F_0FFF` (4 KiB)
- **CarbonIO compat**: `0x000F_1000`–`0x000F_1FFF` (4 KiB)
- **CarbonDMA compat**: `0x000F_2000`–`0x000F_2FFF` (4 KiB)
- **Fast SRAM window (reserved)**: `0x0008_0000`–`0x0008_FFFF` (v1 maps to default RAM)
- **RAM (default)**: all other addresses within the instantiated SRAM size

## MMIO registers (`carbon_mmio_regs`)

Base: `0x000F_0000`

- `+0x00` **SIGNATURE** (RW, 32-bit; byte writes supported)
- `+0x04` **POWEROFF** (WO)
- `+0x08` **UART_TX** (WO)

## CarbonIO compatibility window

Base: `0x000F_1000` (see `hdl/cores/CarbonIO/docs/CarbonIO_v1.md` for register offsets)

## CarbonDMA compatibility window

Base: `0x000F_2000` (see `hdl/cores/CarbonDMA/docs/CarbonDMA_v1.md` for register offsets)

## Notes / v1 integration choices

- The 8096 boot stub performs:
  - `DS=0xF000` for MMIO addressing,
  - `MODEUP` to tier P7 (entry = next instruction),
  - a single turbo-prefixed instruction (`0x63` page) to prove gating works,
  - MMIO signature write + poweroff.
- `MODEFLAGS.STRICT` is cleared in hardware via CSR init so the turbo page is permitted.
- The 8097 is configured to tier P7 and `MODEFLAGS.STRICT=0` via CSR init, but it is not driven by the 8096 in this v1 system top.
- CarbonIO IRQ outputs are not wired to the CPU interrupt sink in this v1 integration (polling only).
- Compatibility windows must be accessed as ordered I/O (8096 `io_if` asserts ordered attributes).
