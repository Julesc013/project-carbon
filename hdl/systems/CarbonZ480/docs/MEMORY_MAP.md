# CarbonZ480 — Memory Map (v1)

This system instantiates:
- `z480_core` (P7 scaffold; fabric interface is idle in v1)
- `am9513_accel` (P7 default mode enabled in this system)
- `carbonio` (UART/PIO/Timers/IRQ router)
- `carbondma` (4-channel DMA engine)
- Common ROM/RAM/MMIO devices on the fabric

## Fabric address space (bring-up map)

For v1 bring-up this system reuses the **x86-class** 1 MiB map from `carbon_memmap_pkg`:

- **Boot ROM**: `0x0000_0000`–`0x0000_0FFF` (4 KiB, read-only)
- **MMIO (system regs)**: `0x000F_0000`–`0x000F_0FFF` (4 KiB)
- **CarbonIO compat**: `0x000F_1000`–`0x000F_1FFF` (4 KiB)
- **CarbonDMA compat**: `0x000F_2000`–`0x000F_2FFF` (4 KiB)
- **Fast SRAM window (reserved)**: `0x0008_0000`–`0x0008_FFFF` (v1 maps to default RAM)
- **RAM (default)**: all other addresses within the instantiated SRAM size

## MMIO registers (`carbon_mmio_regs`)

Base: `0x000F_0000`

- `+0x00` **SIGNATURE** (RW, 32-bit)
- `+0x04` **POWEROFF** (WO)
- `+0x08` **UART_TX** (WO)

## CarbonIO compatibility window

Base: `0x000F_1000` (see `hdl/cores/CarbonIO/docs/CarbonIO_v1.md` for register offsets)

## CarbonDMA compatibility window

Base: `0x000F_2000` (see `hdl/cores/CarbonDMA/docs/CarbonDMA_v1.md` for register offsets)

## Notes / v1 limitations

- The Z480 v1 core scaffold does not execute from ROM yet; the smoke test uses a small fabric boot master that writes the signature and powers off the simulation.
- Am9513 is enabled and placed in its native default mode; CAI host signals are tied off in v1 (plumbing exists but is not exercised by the scaffold).
- CarbonIO IRQ outputs are not wired to a CPU interrupt sink in this v1 scaffold (polling only).
- Compatibility windows must be accessed as ordered I/O (future Z480 io fabric hooks will honor this contract).
