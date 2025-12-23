# CarbonZ380 — Memory Map (v1)

This system instantiates:
- `z380_core` (P6 native core)
- `am9513_accel` (P2 default mode, CAI connected)
- Z380 platform glue (chip-selects, waitgen, refresh)
- `carbonio` (UART/PIO/Timers/IRQ router)
- `carbondma` (4-channel DMA engine)
- Common ROM/RAM/MMIO devices on the fabric

## Fabric address space (SYS16)

Address decode is **priority-based** (MMIO and ROM override the RAM default mapping).

- **Boot ROM**: `0x0000`–`0x00FF` (256 B, read-only)
- **MMIO (system regs)**: `0xF000`–`0xF0FF` (256 B)
- **CarbonIO compat**: `0xF100`–`0xF1FF` (256 B)
- **CarbonDMA compat**: `0xF200`–`0xF2FF` (256 B)
- **BDT ROM**: `0xF800`–`0xF9FF` (512 B, read-only)
- **RAM (default)**: all other `0x0000`–`0xFFFF` addresses not claimed by ROM/MMIO

### RAM conventions (BIOS/DOS placeholders)

These ranges are **conventional reservations** within RAM for JC-BIOS/JC-DOS:

- **BIOS RAM**: `0x0100`–`0x01FF` (scratch/stack)
- **DOS/OS resident**: `0x0200`–`0x1FFF` (placeholder)
- **TPA (Transient Program Area)**: `0x2000`–`0xEFFF` (placeholder)
- **Banked RAM window (optional)**: `0x8000`–`0xBFFF` (overlay, if implemented)

## MMIO registers (`carbon_mmio_regs`)

Base: `0xF000`

- `+0x00` **SIGNATURE** (RW, 32-bit; byte writes supported)
- `+0x04` **POWEROFF** (WO; any write latches `poweroff=1`)
- `+0x08` **UART_TX** (WO; low byte is emitted as a 1-cycle `uart_tx_valid` pulse)

## CarbonIO compatibility window

Base: `0xF100` (see `hdl/cores/CarbonIO/docs/CarbonIO_v1.md` for register offsets)

## CarbonDMA compatibility window

Base: `0xF200` (see `hdl/cores/CarbonDMA/docs/CarbonDMA_v1.md` for register offsets)

## BDT region (BSP)

Base: `0xF800` (read-only BDT image generated from `BDT.yaml`)

## CAI rings (v1 integration choices)

Static configuration (used by the CAI router + Am9513 init logic):

- **Submit descriptor base (host→device)**: forced to `0x0400` (RAM) by `carbon_cai_router`
- **Submit ring mask**: `0x0000_0000` (single-entry ring)
- **Completion base (device CSR)**: `0x0500` (RAM) via `CARBON_CSR_AM9513_CAI_COMP_BASE_*`
- **Completion ring mask (device CSR)**: `0x0000_0000` (single-entry ring)

## Notes

- Z380 `MODEFLAGS` are initialized by a small CSR sequencer before releasing the core.
- CarbonIO IRQ outputs are not wired to the CPU in this v1 integration (polling only).
- Compatibility windows must be accessed as ordered I/O (Z380 `io_if` asserts ordered attributes).
