# CarbonZ80 — Memory Map (v1)

This system instantiates:
- `z85_core` (Z80-derived, strict)
- `am9513_accel` configured as an Am9511-compatible personality by default (P0)
- Common ROM/RAM/MMIO devices on the fabric

## Fabric address space (16-bit window)

Address decode is **priority-based** (MMIO and ROM override the RAM default mapping).

- **Boot ROM**: `0x0000`–`0x00FF` (256 B, read-only)
- **MMIO**: `0xF000`–`0xF0FF` (256 B)
- **RAM (default)**: all other `0x0000`–`0xFFFF` addresses not claimed by ROM/MMIO

## MMIO registers (`carbon_mmio_regs`)

Base: `0xF000`

- `+0x00` **SIGNATURE** (RW, 32-bit; byte writes supported)
- `+0x04` **POWEROFF** (WO; any write latches `poweroff=1`)
- `+0x08` **UART_TX** (WO; low byte is emitted as a 1-cycle `uart_tx_valid` pulse)

## Notes

- Am9513 control/status is via its `csr_if` port (not memory-mapped in this v1 system top).
- IRQ delivery is tied off (no interrupt sources in this v1 integration).

