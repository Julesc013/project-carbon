# Legacy Support Summary

PAL coverage
- Carbon-native: `pal_carbon` (BDT/CAPSET from JC-BIOS discovery).
- Z80 static boards: `pal_z80_static` with board packs:
  - `rc2014`, `s100_ref`, `generic_z80`.
- ROMWBW machines: `pal_romwbw` (hooked to ROMWBW services).
- IBM PC BIOS: `pal_pcbios` (hooked BIOS INT services, virtual BDT).
- UEFI: `pal_uefi` stub (returns unsupported).

Execution environments
- CP/M binaries: `ee_cpm80` (stub, deterministic).
- MS-DOS binaries: `ee_dos86` (stub, deterministic).
- GEM/Windows 1/2/3 are treated as DOS application sets.

Boot paths
- Z80: serial loader, CP/M-style disk boot, ROMWBW chainload.
- PC BIOS: stage1 loader + stage2 PAL handoff.

Capabilities
- CAP_HAS_V86, CAP_HAS_ROMWBW, CAP_HAS_LOCAL_VIDEO,
  CAP_HAS_PAGING, CAP_HAS_IRQ.
- Features activate only when capability + config are both present.
