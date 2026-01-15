# Firmware Architecture

Purpose
- Describe firmware layering and boot responsibilities for JC-BIOS and PAL.

Scope
- Boot ROM responsibilities, BIOS services, PAL binding, and board packs.

Firmware layers
- JC-BIOS is responsible for discovery, BDT synthesis, and service vtables.
- PAL adapts platform-specific boot and devices into JC-BIOS contracts.
- Board packs (source/platform/boards/*) provide static platform descriptors.

Boot models
- Carbon native boot: ROM discovery -> BDT/CAPSET -> BIOS services -> OS handoff.
- Z80 legacy boot: board pack or ROMWBW hooks; see docs/boot_z80.md.
- PC BIOS boot: PAL hooks with BIOS services; see docs/boot_pcbios.md.

Interfaces and contracts
- PAL ABI: source/common/include/jc_pal.h and source/common/spec/SPEC_PAL.md.
- BIOS service contracts: source/common/include/jc_bios_services.h.
- OS handoff contracts: source/common/include/jc_dos_handoff.h.

Determinism expectations
- Boot outputs must be deterministic for identical inputs.
- See docs/DETERMINISM.md and source/common/spec/SPEC_CONFORMANCE.md.
