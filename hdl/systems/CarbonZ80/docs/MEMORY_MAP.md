# CarbonZ80 — Memory Map (v1)

This system instantiates:
- `z85_core` (Z80-derived, strict)
- `am9513_accel` configured as an Am9511-compatible personality by default (P0)
- `carbonio` (UART/PIO/Timers/IRQ router)
- `carbondma` (4-channel DMA engine)
- Common ROM/RAM/MMIO devices on the fabric

## Fabric address space (SYS16)

Address decode is **priority-based** (MMIO and ROM override the RAM default mapping).

- **Boot ROM**: `0x0000`–`0x00FF` (256 B, read-only)
- **MMIO (system regs)**: `0xF000`–`0xF0FF` (256 B)
- **CarbonIO compat**: `0xF100`–`0xF1FF` (256 B)
- **CarbonDMA compat**: `0xF200`–`0xF2FF` (256 B)
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

## CAI ring region (reserved)

The Am9513 is present but CAI submission is disabled in this system stub. The
following RAM locations are reserved for future CAI rings:

- **Submit ring base**: `0x0400`
- **Completion ring base**: `0x0500`

## Notes

- Am9513 control/status is via its `csr_if` port (not memory-mapped in this v1 system top).
- CarbonIO IRQ outputs are not wired to the CPU in this v1 integration (polling only).
- Compatibility windows must be accessed as ordered I/O (Z85 `io_if` asserts ordered attributes).
