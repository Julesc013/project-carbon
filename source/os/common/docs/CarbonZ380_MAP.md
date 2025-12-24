# CarbonZ380 BSP/BDT Map

## Memory Map (SYS16)

- ROM boot stub: `0x0000..0x00FF`
- RAM: `0x0000..0xFFFF` (ROM/MMIO windows overlay)
- Discovery ROM: `0xF400..0xF4FF` (256 bytes)
- BDT ROM: `0xF800..0xFBFF` (1 KiB)
- BSP blob: `0xFF00..0xFF1F` (32 bytes, RAM)

## Console (BSP)

- Kind: `CARBONIO_UART`
- I/O base: `0xF100`
- UART data register: base + `0x00`
- UART status register: base + `0x04`

## Block Device (BSP)

- Kind: `CPMDISK`
- I/O base: `0x10`
- Logical block size: 512 bytes

## Timer (BSP)

- Kind: `CARBONIO_TICK`
- I/O base: `0xF140` (CarbonIO base + 0x40)
