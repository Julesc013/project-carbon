# Boot Workflows (CP/M + RomWBW)

This document describes the reproducible boot workflows for CP/M and RomWBW.
All OS binaries are user-supplied.

## Common inputs

- ROM image: CPU reset vector stub or full system ROM
- Disk image: raw 512-byte LBA file
- BSP blob: `source/os/common/loader/mk_bsp_blob.py` output

## carbon-sim flags

The simulator uses consistent arguments across platforms:

```
carbon-sim --platform <cpm1|cpm22|cpm3|romwbw> \
  --rom path/to/rom.bin \
  --disk0 path/to/disk.img \
  --bsp path/to/board.bsp \
  [--load path/to/mem.bin] \
  [--max-cycles N]
```

`--load` injects a RAM image at address 0x0000 before reset. This is optional
for ROM-only flows.

## CP/M workflow (recommended)

1) Build a BSP blob for the target platform.
2) Generate a boot ROM stub with the `mk_cpm*_bootrom.py` script.
3) Generate a RAM image with the `mk_cpm*_image.py` script.
4) Run `carbon-sim` with `--rom`, `--disk0`, `--bsp`, and `--load`.

Use the OS-specific READMEs in `source/os/cpm1`, `source/os/cpm22`, and
`source/os/cpm3` for exact command lines.

## RomWBW workflow (single target)

RomWBW uses a single supported target (see `source/os/romwbw/README.md`).
Provide the RomWBW ROM and disk images, then run:

```
carbon-sim --platform romwbw --rom path/to/romwbw.bin \
  --disk0 path/to/romwbw_disk0.img --bsp path/to/RomWBW.bsp
```

## Automated runner

Use `scripts/run_os_boot.sh` for repeatable smoke runs. It accepts environment
variables to point at your ROM/disk/BSP paths and checks for a banner string:

```
scripts/run_os_boot.sh --os cpm22
```

The script writes logs to `build/os_boot_logs` and reports PASS/FAIL.

## Determinism notes

- All device bases are sourced from the BSP/BDT contract.
- Polling-based I/O is allowed and deterministic.
- Banner detection is used for smoke validation; it is not a full conformance
  test.
