# Platforms

## CarbonCPM22 (`--platform cpm22`)

### Memory map

- 64 KiB RAM at `0x0000..0xFFFF`
- Boot ROM overlays *reads* at `0x0000..0x0000+ROM_SIZE-1` on reset
- ROM overlay enable latch at I/O port `0x3F`:
  - write `0` to disable ROM overlay (reads fall through to RAM)
  - write `1` to enable ROM overlay
- BDT overlay (read-only) at `0xF800` (1 KiB, device table for discovery)
- Optional BSP blob loaded into RAM at `0xFF00` via `--bsp`

### I/O map

- CAPS (CPUID/CAPS transport) base `0xF000`
  - `+0x00` INDEX (RW, 32-bit via 4 bytes)
  - `+0x04` DATA0 (RO, 32-bit)
  - `+0x08` DATA1 (RO, 32-bit)
  - `+0x0C` DATA2 (RO, 32-bit)
  - `+0x10` DATA3 (RO, 32-bit)
- CarbonIO base `0xF100` (compat window)
  - `+0x00` UART_DATA, `+0x04` UART_STATUS
  - `+0x40` TICK_LO, `+0x44` TICK_HI
- CarbonDMA base `0xF200` (compat window)
  - `+0x00` ID, `+0x04` STATUS, `+0x08` CTRL
- Disk (`CpmDiskDevice`) base `0x10`
  - `0x10` CMD (WO): `0x01` read sector, `0x02` write sector
  - `0x11` STATUS (RO): bit0 READY, bit1 ERR, bit7 DRQ
  - `0x12..0x15` LBA (RW): 32-bit little-endian sector index
  - `0x16` DATA (RW): 128-byte sector data port
  - `0x17` DRIVE (RW): 0..3

### Limitations

- CP/M requires a ROM/BIOS built for this I/O map; no CP/M binaries are included.

## CarbonCPM1 (`--platform cpm1`)

CarbonCPM1 reuses the CarbonCPM22 hardware map and devices, but is intended for
8080/8085-tier software (P0/P1). Provide a ROM/BIOS built for the same I/O map.

## CarbonCPM3 (`--platform cpm3`)

CarbonCPM3 currently reuses the CarbonCPM22 hardware map and devices. Banked
memory support is a TODO; use this platform with a flat memory image for now.

## CarbonRomWBW (`--platform romwbw`)

### Memory map

- 64 KiB RAM at `0x0000..0xFFFF`
- ROM overlays *reads* at `0x0000..0x0000+ROM_SIZE-1` on reset (max 32 KiB in v1)
- ROM overlay enable latch at I/O port `0x3F` (same behavior as `cpm22`)
- BDT overlay (read-only) at `0xF800` (1 KiB, device table for discovery)
- Optional BSP blob loaded into RAM at `0xFF00` via `--bsp`

### I/O map

- Zilog SIO/2 (`ZilogSio`) base `0x80`
  - Channel A: `0x80` DATA, `0x81` CTRL/STATUS
  - Channel B: `0x82` DATA, `0x83` CTRL/STATUS
  - Status returns RR0 subset: bit0 RX ready, bit2 TX ready
- CAPS (CPUID/CAPS transport) base `0xF000` (same register layout as `cpm22`)
- CarbonIO base `0xF100` (compat window)
  - `+0x00` UART_DATA, `+0x04` UART_STATUS
  - `+0x40` TICK_LO, `+0x44` TICK_HI
- CarbonDMA base `0xF200` (compat window)
  - `+0x00` ID, `+0x04` STATUS, `+0x08` CTRL
- IDE/ATA PIO (`IdeDiskDevice`) base `0x10`
  - `+0` DATA (PIO 8-bit stream, 512 bytes per sector)
  - `+1` ERROR (RO) / FEATURES (WO)
  - `+2` SECTOR COUNT
  - `+3` LBA0
  - `+4` LBA1
  - `+5` LBA2
  - `+6` DRIVE/HEAD (bit6 LBA, bit4 SLAVE)
  - `+7` STATUS (RO) / COMMAND (WO)
  - Implemented commands: IDENTIFY `0xEC`, READ SECTORS `0x20`, WRITE SECTORS `0x30`

### Supported RomWBW target

v1 expects a RomWBW build that uses:

- Zilog SIO for console at ports `0x80..0x83`
- 8-bit IDE/ATA PIO at ports `0x10..0x17`
- A ROM image that fits in 32 KiB (no banking in v1)

### Limitations

- No ROM/RAM banking and no CTC/PIO emulation beyond CarbonIO compat stubs.
- SIO register programming is minimally modeled (sufficient for polled console).
- ATA emulation is minimal and correctness-first (PIO only).

## CarbonZ80 (`--platform carbonz80`)

### Memory map (SYS16)

- Boot ROM at `0x0000..0x00FF` (256 B, read-only)
- MMIO (system regs) at `0xF000..0xF0FF`
- CarbonIO compat window at `0xF100..0xF1FF`
- CarbonDMA compat window at `0xF200..0xF2FF`
- BDT ROM at `0xF800..0xFBFF` (read-only)
- RAM covers `0x0000..0xFFFF` excluding ROM/MMIO windows
- Optional BSP blob loaded into RAM at `0xFF00` via `--bsp`

### I/O map

- Disk (`CpmDiskDevice`) base `0x10` (512-byte sectors)

### Notes

- If `--rom` is omitted, a built-in stub writes the signature and powers off.
- The simulator uses the Z80 execution model for the CarbonZ* platforms.
- The CpmDisk device is advertised in the BDT; it is present only when a disk image is attached.

## CarbonZ90 (`--platform carbonz90`)

### Memory map (SYS16)

- Boot ROM at `0x0000..0x00FF` (256 B, read-only)
- MMIO (system regs) at `0xF000..0xF0FF`
- CarbonIO compat window at `0xF100..0xF1FF`
- CarbonDMA compat window at `0xF200..0xF2FF`
- BDT ROM at `0xF800..0xFBFF` (read-only)
- RAM covers `0x0000..0xFFFF` excluding ROM/MMIO windows
- Optional BSP blob loaded into RAM at `0xFF00` via `--bsp`

### I/O map

- Disk (`CpmDiskDevice`) base `0x10` (512-byte sectors)

### Notes

- If `--rom` is omitted, a built-in stub writes the signature and powers off.
- The simulator uses the Z80 execution model for the CarbonZ* platforms.

## CarbonZ380 (`--platform carbonz380`)

### Memory map (SYS16)

- Boot ROM at `0x0000..0x00FF` (256 B, read-only)
- MMIO (system regs) at `0xF000..0xF0FF`
- CarbonIO compat window at `0xF100..0xF1FF`
- CarbonDMA compat window at `0xF200..0xF2FF`
- BDT ROM at `0xF800..0xFBFF` (read-only)
- RAM covers `0x0000..0xFFFF` excluding ROM/MMIO windows
- Optional BSP blob loaded into RAM at `0xFF00` via `--bsp`

### I/O map

- Disk (`CpmDiskDevice`) base `0x10` (512-byte sectors)

### Notes

- If `--rom` is omitted, a built-in stub writes the signature and powers off.
- The simulator uses the Z80 execution model for the CarbonZ* platforms.

## CarbonZ480 (`--platform carbonz480`)

### Memory map (SYS16 compatibility)

- Boot ROM at `0x0000..0x00FF` (256 B, read-only)
- MMIO (system regs) at `0xF000..0xF0FF`
- CarbonIO compat window at `0xF100..0xF1FF`
- CarbonDMA compat window at `0xF200..0xF2FF`
- Tier host window at `0xF300..0xF3FF`
- BDT ROM at `0xF800..0xFBFF` (read-only)
- RAM covers `0x0000..0xFFFF` excluding ROM/MMIO windows
- Optional BSP blob loaded into RAM at `0xFF00` via `--bsp`

### I/O map

- Disk (`CpmDiskDevice`) base `0x10` (512-byte sectors)

### Notes

- If `--rom` is omitted, a built-in stub writes the signature and powers off.
- The tier host window is modeled as a minimal MMIO stub.
