# RomWBW Bring-up

This directory holds RomWBW bring-up notes and build artifacts. No RomWBW
binaries are shipped in the repo.

## Supported target (v1)

- CPU: Z80-class (P2)
- Console: Zilog SIO channel A at ports `0x80..0x81`
- Disk: 8-bit IDE/ATA PIO at ports `0x10..0x17` (512-byte sectors)
- ROM size: <= 32 KiB (no ROM banking in v1)
- BSP: `source/os/romwbw/RomWBW.bsp` (load at `0xFF00`)

## BSP blob

```bash
python source/os/common/loader/mk_bsp_blob.py \
  --spec source/os/romwbw/RomWBW.yaml \
  --out build/RomWBW.bsp
```

## Run (carbon-sim)

```bash
carbon-sim --platform romwbw \
  --rom path/to/romwbw.bin \
  --disk0 path/to/romwbw_disk0.img \
  --bsp build/RomWBW.bsp
```
