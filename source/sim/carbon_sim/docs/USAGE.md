# carbon-sim usage

## Build

From the repository root:

```sh
cmake -S source/sim/carbon_sim -B build/sim
cmake --build build/sim
```

## Run CP/M 2.2 (CarbonCPM22)

You must supply your own CP/M 2.2 boot ROM and disk image (no copyrighted ROMs are included).

```sh
carbon-sim --platform cpm22 --rom path/to/cpm22_boot.rom --disk0 path/to/cpm22.dsk --bsp path/to/BSP.bsp
```

Useful flags:

```sh
carbon-sim --platform cpm22 --rom ... --disk0 ... --trace
carbon-sim --platform cpm22 --rom ... --disk0 ... --max-cycles 5000000
```

## Run RomWBW (CarbonRomWBW)

You must supply a RomWBW ROM image that matches this simulator's v1 I/O map.

```sh
carbon-sim --platform romwbw --rom path/to/romwbw.bin --disk0 path/to/romwbw_disk0.img --bsp path/to/BSP.bsp
```

Notes:

- This v1 simulator supports only ROM images that fit in a 32 KiB window (no ROM banking yet).
- `--disk1` is supported as an IDE slave; `--disk2`/`--disk3` are ignored in v1.

## Run CarbonZ systems (CarbonZ80/90/380/480)

These platforms provide SYS16-compatible memory maps and a built-in ROM stub that
writes a signature to MMIO and powers off. You can override the stub with `--rom`
(ROM size must be <= 256 bytes).

```sh
carbon-sim --platform carbonz80
carbon-sim --platform carbonz90
carbon-sim --platform carbonz380
carbon-sim --platform carbonz480
```

Attach an optional 512-byte block device (IDE/ATA PIO at `0x10`) with `--disk0`.
You can also inject a BSP blob at `0xFF00` (default) via `--bsp`:

```sh
carbon-sim --platform carbonz80 --disk0 path/to/disk.img --bsp path/to/BSP.bsp
```

## Disk images

All disks are raw files.

- `cpm22` uses a 128-byte sector device abstraction (the ROM/BIOS decides layout).
- `romwbw` uses 512-byte ATA PIO sectors (IDE register model).
- `carbonz*` platforms use 512-byte ATA PIO sectors (IDE register model).

Create a blank image:

```sh
python tools/mk_disk.py --out disk.img --size-bytes 8388608
```

## Verilator backend (preview)

The Verilator backend is optional and currently scaffold-only.

To enable it at build time:

```sh
set VERILATOR_ROOT=C:\path\to\verilator
cmake -S source/sim/carbon_sim -B build/sim -DCARBON_SIM_ENABLE_VERILATOR=ON
cmake --build build/sim
```

At runtime:

```sh
carbon-sim --verilator --platform cpm22 --rom ... --disk0 ...
```
