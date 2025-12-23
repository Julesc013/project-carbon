# CarbonZ480 — Memory Map (v1)

This system instantiates:
- `z480_core` (P7 native core)
- Compatibility cores: `z85_core`, `z90_core`, `z380_core`
- `tier_host_ctrl` (MODEUP/RETMD controller)
- `am9513_accel` (P2 default mode, CAI connected)
- `carbonio` (UART/PIO/Timers/IRQ router)
- `carbondma` (4-channel DMA engine)
- Common ROM/RAM/MMIO devices on the fabric

## Fabric address space (SYS16 compatibility map)

CarbonZ480 uses the 64 KiB SYS16 layout, with **low 16-bit decode** for compatibility:

- **Boot ROM**: `0x0000_0000`–`0x0000_00FF` (256 B, read-only)
- **MMIO (system regs)**: `0x0000_F000`–`0x0000_F0FF` (256 B)
- **CarbonIO compat**: `0x0000_F100`–`0x0000_F1FF` (256 B)
- **CarbonDMA compat**: `0x0000_F200`–`0x0000_F2FF` (256 B)
- **Tier host**: `0x0000_F300`–`0x0000_F3FF` (256 B)
- **RAM (default)**: 64 KiB SRAM

Upper address bits are ignored for decode so that sign-extended addresses from Z480
still resolve to the SYS16 compatibility windows.

### RAM conventions (BIOS/DOS placeholders)

These ranges are **conventional reservations** within SYS16 RAM for JC-BIOS/JC-DOS:

- **BIOS RAM**: `0x0000_0100`–`0x0000_01FF` (scratch/stack)
- **DOS/OS resident**: `0x0000_0200`–`0x0000_1FFF` (placeholder)
- **TPA (Transient Program Area)**: `0x0000_2000`–`0x0000_EFFF` (placeholder)
- **Banked RAM window (optional)**: `0x0000_8000`–`0x0000_BFFF` (overlay, if implemented)

## Boot ROM contents

- `0x0000`: Z85 stub writes `MODEUP` request (P7) to the tier host window, then halts.
- `0x0040`: Z480 monitor stub writes the signature, polls UART status, then powers off.

## MMIO registers (`carbon_mmio_regs`)

Base: `0x0000_F000`

- `+0x00` **SIGNATURE** (RW, 32-bit)
- `+0x04` **POWEROFF** (WO)
- `+0x08` **UART_TX** (WO)

## CarbonIO compatibility window

Base: `0x0000_F100` (see `hdl/cores/CarbonIO/docs/CarbonIO_v1.md` for offsets)

## CarbonDMA compatibility window

Base: `0x0000_F200` (see `hdl/cores/CarbonDMA/docs/CarbonDMA_v1.md` for offsets)

## Tier host window

Base: `0x0000_F300` (see `docs/platform/TIER_HOSTING.md` for registers)

## CAI rings (v1 integration choices)

- **Submit descriptor base (host-programmed)**: recommended `0x0000_2000`
- **Submit ring mask**: host-programmed
- **Completion base (device CSR)**: `0x0000_4000`
- **Completion ring mask (device CSR)**: `0x0000_00FF` (256-entry ring)

## Notes / v1 limitations

- CarbonIO IRQ outputs are not wired to a CPU interrupt sink yet (polling only).
- Compatibility windows must be accessed as ordered I/O.
