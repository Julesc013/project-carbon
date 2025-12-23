# ROM assets

This repository does **not** include copyrighted ROM images (CP/M, RomWBW, etc).

Place your own ROM images anywhere and pass them to `carbon-sim` with `--rom`.

Suggested layout for local usage:

- `source/sim/carbon_sim/roms/cpm22_boot.rom`
- `source/sim/carbon_sim/roms/romwbw.bin`

CarbonZ platforms ship with a built-in ROM stub; pass `--rom` only if you want
to override the default (ROM size must be <= 256 bytes).
