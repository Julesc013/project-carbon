# IBM PC BIOS Boot

Location
- Boot helpers live under `source/platform/pcbios/boot/`.

Stage1
- Entry: `jc_pcbios_stage1_load()` in `stage1.c`.
- Reads a contiguous stage2 image from disk (LBA start + count) into RAM.
- Requires `jc_pcbios_boot_ops.read_sectors`.
- This is C89 logic; a BIOS build must place it into a boot sector.

Stage2
- Entry: `jc_pcbios_stage2_handoff()` in `stage2.c`.
- Calls `jc_pal_init()`, builds `jc_dos_handoff_v1`, and calls kernel entry.
- `jc_pcbios_stage2_prepare()` fills the handoff block using PAL CAPSET/BDT.
- BIOS INT wiring is provided via `jc_pcbios_boot_ops`.

Disk layout
- LBA0: stage1 boot sector.
- LBA1..N: stage2 loader image.
- Remaining LBAs: JC-BIOS/JC-DOS image + data.

Installer
- No installer script is provided in-tree.
- Write stage1 to LBA0 and stage2 to LBA1..N using a raw disk tool.
