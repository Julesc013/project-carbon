# CP/M Support Summary

This project provides a deterministic bring-up path for CP/M 1.x, 2.2, and 3+.
No CP/M binaries are shipped in the repo; users supply their own images.

## Supported tiers

- CP/M 1.x: P0/P1 (8080/8085)
- CP/M 2.2: P2 (Z80)
- CP/M 3+: P2/P3 with BIOS-controlled banked memory

## Required artifacts (user-supplied)

- ROM image (boot stub or system ROM)
- Disk image (raw 512-byte LBA sectors)
- Optional CCP/BDOS/BIOS system image for RAM load

## Loader scripts

Use the scripts under `source/os/cpm*` to build RAM images and minimal boot ROMs:

- `source/os/cpm1/mk_cpm1_image.py`
- `source/os/cpm1/mk_cpm1_bootrom.py`
- `source/os/cpm22/mk_cpm22_image.py`
- `source/os/cpm22/mk_cpm22_bootrom.py`
- `source/os/cpm3/mk_cpm3_image.py`
- `source/os/cpm3/mk_cpm3_bootrom.py`

Each script accepts a BSP blob so the BIOS can read device bases through the
BDT/BSP contract. See `source/os/common/docs/BDT_BSP_MODEL.md` for details.

## Disk mapping policy

All CP/M variants map 128-byte sectors onto the 512-byte block device:

- `LBA = sector >> 2`
- `offset = (sector & 3) * 128`

The BIOS shim is expected to perform the copy and preserve deterministic
ordering (polling is allowed).

## Deterministic smoke path

The simulator smoke tests (`source/sim/carbon_sim/tests/smoke.cpp`) can boot
without user binaries by loading a tiny RAM image that prints a banner and
halts. This validates the loader path and BSP/BDT exposure only.

For real CP/M boots, use `scripts/run_os_boot.sh` with your ROM and disk
artifacts.
