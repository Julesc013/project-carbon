# Platforms

## CarbonCPM22 (`--platform cpm22`)

### Memory map

- 64 KiB RAM at `0x0000..0xFFFF`
- Boot ROM overlays *reads* at `0x0000..0x0000+ROM_SIZE-1` on reset
- ROM overlay enable latch at I/O port `0x3F`:
  - write `0` to disable ROM overlay (reads fall through to RAM)
  - write `1` to enable ROM overlay

### I/O map

- UART0 (`UARTConsole`)
  - `0x00` DATA (RW): write outputs a byte, read returns next RX byte (0 if empty)
  - `0x01` STATUS (RO): bit0 RX ready, bit1 TX ready
- Disk (`CpmDiskDevice`) base `0x10`
  - `0x10` CMD (WO): `0x01` read sector, `0x02` write sector
  - `0x11` STATUS (RO): bit0 READY, bit1 ERR, bit7 DRQ
  - `0x12..0x15` LBA (RW): 32-bit little-endian sector index
  - `0x16` DATA (RW): 128-byte sector data port
  - `0x17` DRIVE (RW): 0..3
- Timer (`TimerTick`) base `0x20`
  - `0x20..0x23` TICKS (RO): 32-bit little-endian tick counter
  - `0x24` CTRL (RW): bit0 enables IRQ generation (vector byte is the written value)

### Limitations

- CP/M requires a ROM/BIOS built for this I/O map; no CP/M binaries are included.

## CarbonRomWBW (`--platform romwbw`)

### Memory map

- 64 KiB RAM at `0x0000..0xFFFF`
- ROM overlays *reads* at `0x0000..0x0000+ROM_SIZE-1` on reset (max 32 KiB in v1)
- ROM overlay enable latch at I/O port `0x3F` (same behavior as `cpm22`)

### I/O map

- Zilog SIO/2 (`ZilogSio`) base `0x80`
  - Channel A: `0x80` DATA, `0x81` CTRL/STATUS
  - Channel B: `0x82` DATA, `0x83` CTRL/STATUS
  - Status returns RR0 subset: bit0 RX ready, bit2 TX ready
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
- Timer (`TimerTick`) base `0x20` (same as `cpm22`)

### Supported RomWBW target

v1 expects a RomWBW build that uses:

- Zilog SIO for console at ports `0x80..0x83`
- 8-bit IDE/ATA PIO at ports `0x10..0x17`
- A ROM image that fits in 32 KiB (no banking in v1)

### Limitations

- No ROM/RAM banking and no CTC/PIO emulation beyond the simple timer.
- SIO register programming is minimally modeled (sufficient for polled console).
- ATA emulation is minimal and correctness-first (PIO only).

