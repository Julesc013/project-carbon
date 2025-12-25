# Z80 Boot Paths

Location
- Boot helpers live under `source/platform/z80/boot/`.

Serial loader
- Entry: `jc_z80_serial_loader()` in `serial_loader.c`.
- Protocol: host sends 16-bit little-endian length, followed by payload bytes.
- Loader copies payload to `load_addr` and returns `JC_E_OK` on success.
- This is C89 logic; a monitor or ROM must provide serial hooks.

CP/M-style disk boot
- Entry: `jc_z80_disk_boot()` in `disk_boot.c`.
- Reads `sectors` 512-byte blocks from LBA0 into `load_addr`.
- Intended for CP/M-style boot tracks and simple stage2 loaders.
- Requires block I/O hooks from the board.

ROMWBW chainload
- Entry: `jc_z80_romwbw_chainload()` in `romwbw_chainload.c`.
- Calls a board-provided `jump` hook to the ROMWBW entry address.

Hooks
- All boot functions accept `jc_z80_boot_ops` from `z80_boot.h`.
- Hooks provide serial I/O, block I/O, and an optional jump routine.
