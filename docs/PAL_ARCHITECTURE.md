# PAL Architecture

Purpose
- Provide a strict, versioned Platform Adapter Layer (PAL) that hides boot details.
- Produce canonical BDT and CAPSET structures for JC-DOS and guests.

ABI surface
- `source/common/include/jc_pal.h` defines `jc_pal_desc` and service vtables.
- `source/common/util/jc_pal.c` provides `jc_pal_register()` and `jc_pal_init()`.
- ABI version is `JC_PAL_ABI_MAJOR`/`JC_PAL_ABI_MINOR`.

Required services
- Console: text/VT100 write, optional read/flush.
- Block: LBA read/write (512B sectors) + params query.
- Timer: monotonic ticks + tick rate.
- Memmap: pointer to a JC_MEM_REGION_TABLE_V1.

Optional services
- Keyboard, local video, RTC, DMA cache sync hooks.
- Optional services must be gated by capability + config.

BDT/CAPSET synthesis
- PAL produces a valid BDT (SPEC_BDT) and CAPSET (SPEC_CAPSET).
- `jc_pal_desc.bdt` and `jc_pal_desc.capset` are authoritative.
- CAPSET `periph_features[0]` includes CAP_HAS_* bits for platform features.

Binding model
- PAL selection is explicit via `jc_pal_register()` plus a PAL-specific bind:
  - `pal_carbon`: `jc_pal_carbon_bind()`
  - `pal_z80_static`: `jc_pal_z80_static_bind()`
  - `pal_romwbw`: `jc_pal_romwbw_bind()` (hooks required)
  - `pal_pcbios`: `jc_pal_pcbios_bind()` (hooks required)
  - `pal_uefi`: `jc_pal_uefi_bind()` (stub)

Implementations
- `source/platform/pal_carbon/`: wraps JC-BIOS discovery/BDT and forwards
  console/block/timer.
- `source/platform/pal_z80_static/`: board-pack driven, no probing.
- `source/platform/pal_romwbw/`: ROMWBW hooks map services into PAL ops.
- `source/platform/pal_pcbios/`: BIOS-int style hooks with virtual BDT.
- `source/platform/pal_uefi/`: stub that returns unsupported.
- Each PAL exports `JC_COMPONENT_DESC` for dependency metadata.

Board packs (Z80)
- Located under `source/platform/boards/`.
- Each pack exports `JC_PAL_BOARD_PACK` (see `pal_z80_board.h`).
- Pack includes static device list, memmap table, and service vtables.

Determinism
- `JC_PAL_FLAG_DETERMINISTIC` indicates deterministic PAL behavior.
- PAL output must be identical for identical inputs.

Error mapping
- Unsupported platform/service: `JC_E_DEV_UNSUPPORTED`.
- Missing device: `JC_E_DEV_NOT_FOUND`.
- I/O errors: `JC_E_DEV_IO_TIMEOUT` or `JC_E_DEV_IO_ERROR`.

Fault injection (sim-only)
- `source/common/include/jc_fault.h` defines fault masks for timeouts,
  partial reads, spurious IRQs, bad sectors, and MODEUP failure.
- Board-pack stubs consume these masks to simulate errors deterministically.
