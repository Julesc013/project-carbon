# CP/M 2.2 Bring-up

This directory holds CP/M 2.2 bring-up notes and helper scripts. No CP/M
binaries are shipped in the repo.

## Memory image builder

Use `mk_cpm22_image.py` to compose a 64 KiB RAM image from a user-supplied
system binary (CCP+BDOS+BIOS):

```bash
python source/os/cpm22/mk_cpm22_image.py \
  --system path/to/CPM22_SYS.bin \
  --bsp build/CarbonZ80.bsp \
  --out build/cpm22_mem.bin
```

Load the resulting `cpm22_mem.bin` with `carbon-sim --load`.

## Boot ROM stub

The CP/M simulator platform expects a small ROM stub to disable the overlay:

```bash
python source/os/cpm22/mk_cpm22_bootrom.py --out build/cpm22_boot.rom
```

## BIOS stub

`bios_carbon_stub.asm` is a minimal BIOS skeleton intended as a starting point.
Console I/O is sketched; disk operations are TODO and must be implemented for
real CP/M use.
