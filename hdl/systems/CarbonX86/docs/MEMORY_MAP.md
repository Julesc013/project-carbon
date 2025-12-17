# CarbonX86 — Memory Map (v1)

This system instantiates:
- `cpu_8096` in P0 mode (8086-compatible subset)
- `fpu_8097` in P0 mode (x87-like CSR shell; left idle in this system stub)
- Common ROM/RAM/MMIO devices on the fabric

## Fabric address space (20-bit real-mode window)

This v1 integration uses a 1 MiB physical window (20-bit wrap is core-defined):

- **Boot ROM**: `0x0000_0000`–`0x0000_0FFF` (4 KiB, read-only)
- **MMIO**: `0x000F_0000`–`0x000F_0FFF` (4 KiB)
- **RAM (default)**: all other addresses within the instantiated SRAM size

## MMIO registers (`carbon_mmio_regs`)

Base: `0x000F_0000`

- `+0x00` **SIGNATURE** (RW, 32-bit; byte writes supported)
- `+0x04` **POWEROFF** (WO)
- `+0x08` **UART_TX** (WO)

## Notes

- The 8096 boot ROM stub sets `DS=0xF000` so that `DS:0000` targets MMIO at physical `0xF0000`.
- The 8097 CSR window is present but not exercised by the v1 system boot stub.

