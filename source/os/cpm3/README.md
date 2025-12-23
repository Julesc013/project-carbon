# CP/M 3+ Bring-up

This directory holds CP/M 3+ bring-up notes and helper scripts. No CP/M
binaries are shipped in the repo.

## Memory image builder

```bash
python source/os/cpm3/mk_cpm3_image.py \
  --system path/to/CPM3_SYS.bin \
  --bsp build/CarbonZ80.bsp \
  --out build/cpm3_mem.bin
```

## Boot ROM stub

```bash
python source/os/cpm3/mk_cpm3_bootrom.py --out build/cpm3_boot.rom
```

## Notes

- Banked memory support is a TODO in v1; this script builds a flat 64 KiB image.
