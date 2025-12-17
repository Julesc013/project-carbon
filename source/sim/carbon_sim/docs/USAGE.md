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
carbon-sim --platform cpm22 --rom path/to/cpm22_boot.rom --disk0 path/to/cpm22.dsk
```

Useful flags:

```sh
carbon-sim --platform cpm22 --rom ... --disk0 ... --trace
carbon-sim --platform cpm22 --rom ... --disk0 ... --max-cycles 5000000
```

## Run RomWBW (CarbonRomWBW)

You must supply a RomWBW ROM image that matches this simulator's v1 I/O map.

```sh
carbon-sim --platform romwbw --rom path/to/romwbw.bin --disk0 path/to/romwbw_disk0.img
```

Notes:

- This v1 simulator supports only ROM images that fit in a 32 KiB window (no ROM banking yet).
- `--disk1` is supported as an IDE slave; `--disk2`/`--disk3` are ignored in v1.

## Disk images

All disks are raw files.

- `cpm22` uses a 128-byte sector device abstraction (the ROM/BIOS decides layout).
- `romwbw` uses 512-byte ATA PIO sectors (IDE register model).

Create a blank image:

```sh
python tools/mk_disk.py --out disk.img --size-bytes 8388608
```

