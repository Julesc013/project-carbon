# BSP + BDT Handoff Model (SYS16)

Project Carbon OS bring-up uses two discovery artifacts:

- **BDT** (Board Device Table): a binary table at a fixed ROM address describing
  devices, classes, and base addresses.
- **BSP** (Board Support Parameters): a small binary blob in RAM that points to
  the BDT and provides the minimum I/O bases needed for early boot.

This document defines the BSP blob format used by the CP/M and RomWBW loaders.

## BSP Location (v1 SYS16)

- Default BSP base address: `0xFF00` (RAM)
- Size: 32 bytes
- Endianness: little-endian

## BSP Header Layout (v1)

| Offset | Size | Field | Description |
|---:|---:|---|---|
| `0x00` | 4 | `signature` | ASCII `"CBSP"` (0x50534243) |
| `0x04` | 2 | `version` | BSP format version (v1 = `1`) |
| `0x06` | 2 | `size` | Blob size in bytes (v1 = `32`) |
| `0x08` | 2 | `bdt_base` | BDT base address (ROM) |
| `0x0A` | 2 | `bdt_size` | BDT size in bytes |
| `0x0C` | 2 | `console_io_base` | Base I/O port for console device |
| `0x0E` | 2 | `block_io_base` | Base I/O port for block device |
| `0x10` | 2 | `timer_io_base` | Base I/O port for tick source |
| `0x12` | 1 | `fpu_present` | `1` if Am9513 is present |
| `0x13` | 1 | `reserved0` | Reserved (0) |
| `0x14` | 1 | `console_kind` | Console device kind (see below) |
| `0x15` | 1 | `block_kind` | Block device kind (see below) |
| `0x16` | 1 | `timer_kind` | Timer device kind (see below) |
| `0x17` | 1 | `reserved1` | Reserved (0) |
| `0x18` | 2 | `block_sector_bytes` | Logical block size (v1 = `512`) |
| `0x1A` | 2 | `flags` | Reserved (0) |
| `0x1C` | 4 | `reserved2` | Reserved (0) |

## Device Kind IDs

Console kinds:
- `1` = `CARBONIO_UART`
- `2` = `SIO`

Block kinds:
- `1` = `IDE` (8-bit PIO)
- `2` = `CPMDISK`
- `3` = `RAMDISK`

Timer kinds:
- `0` = `NONE`
- `1` = `CARBONIO_TICK`

## Generation

Use `source/os/common/loader/mk_bsp_blob.py` to generate a BSP blob from a
YAML spec:

```bash
python source/os/common/loader/mk_bsp_blob.py \
  --spec source/os/common/bsp/CarbonZ80.yaml \
  --out build/CarbonZ80.bsp
```
