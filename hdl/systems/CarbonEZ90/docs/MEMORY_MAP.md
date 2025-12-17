# CarbonEZ90 — Memory Map (v1)

This system instantiates:
- `ez90_core` (P7 scaffold; fabric interface is idle in v1)
- `am9513_accel` (P7 default mode enabled in this system)
- Common ROM/RAM/MMIO devices on the fabric

## Fabric address space (bring-up map)

For v1 bring-up this system reuses the **x86-class** 1 MiB map from `carbon_memmap_pkg`:

- **Boot ROM**: `0x0000_0000`–`0x0000_0FFF` (4 KiB, read-only)
- **MMIO**: `0x000F_0000`–`0x000F_0FFF` (4 KiB)
- **RAM (default)**: all other addresses within the instantiated SRAM size

## MMIO registers (`carbon_mmio_regs`)

Base: `0x000F_0000`

- `+0x00` **SIGNATURE** (RW, 32-bit)
- `+0x04` **POWEROFF** (WO)
- `+0x08` **UART_TX** (WO)

## Notes / v1 limitations

- The eZ90 v1 core scaffold does not execute from ROM yet; the smoke test uses a small fabric boot master that writes the signature and powers off the simulation.
- Am9513 is enabled and placed in P7 default mode; CAI host signals are tied off in v1 (plumbing exists but is not exercised by the scaffold).

