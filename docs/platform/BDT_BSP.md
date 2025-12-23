# Board Device Table (BDT) + BSP Stub Convention

This document defines the minimal BSP scaffolding used by Carbon systems to boot
JC-BIOS/JC-DOS-compatible software without hardcoding device addresses.

## BDT region (fixed)

The BDT is exposed as a read-only ROM image in the BSP region:

- **SYS16 systems (CarbonZ80/Z90/Z380/Z480)**: `0xF800`–`0xF9FF` (512 B)
- **SYSX86 systems**: `0x000F_8000`–`0x000F_81FF` (512 B)

The BDT format is `BDT_HEADER_V1` + `DEVICE_CAP_DESC_V1` entries (see
`hdl/spec/device_model.yaml`).

## BSP region (fixed)

The BSP region is the fixed top-of-memory window used before parsing the BDT.
System ROM stubs should **only** access devices inside this region until the BDT
is parsed:

- `carbon_mmio_regs` (signature/poweroff/uart_tx)
- CarbonIO compat window
- CarbonDMA compat window
- Tier host window (if present)
- BDT ROM window

## BSP stub convention (minimal)

Boot ROMs should implement the following deterministic steps:

1. Read and validate the BDT header at the fixed BDT base.
2. Locate the console device (CarbonIO UART-class) and initialize it.
3. Locate a block device (if present) and initialize the first unit.
4. Locate a deterministic tick source (CarbonIO timer/tick) for timekeeping.

If a required device is absent, the stub should fail deterministically (halt or
trap).

## BDT manifests and generation

Each system provides a machine-readable BDT manifest:

- `hdl/systems/CarbonZ80/docs/BDT.yaml`
- `hdl/systems/CarbonZ90/docs/BDT.yaml`
- `hdl/systems/CarbonZ380/docs/BDT.yaml`
- `hdl/systems/CarbonZ480/docs/BDT.yaml`

Generate ROM images and C constants with:

- `scripts/gen_bdt.sh`
- `scripts/gen_bdt.ps1`

The generator produces:

- `hdl/systems/<System>/rtl/bdt_image.svh` (ROM contents)
- `source/sim/carbon_sim/include/carbon_sim/util/carbon_constants.h`

## Notes

- The BDT tables are authoritative for BSP discovery; avoid hardcoded ports
  outside the BSP region.
- The boot ROM stubs in v1 are minimal smoke tests and do not yet parse the BDT.
