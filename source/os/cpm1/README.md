# CP/M 1.x Bring-up

This directory holds CP/M 1.x bring-up notes and helper scripts. No CP/M
binaries are shipped in the repo.

## Memory image builder

```bash
python source/os/cpm1/mk_cpm1_image.py \
  --system path/to/CPM1_SYS.bin \
  --bsp build/CarbonZ80.bsp \
  --out build/cpm1_mem.bin
```

## Boot ROM stub

```bash
python source/os/cpm1/mk_cpm1_bootrom.py --out build/cpm1_boot.rom
```
