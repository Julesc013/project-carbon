# Tier Hosting (Option A)

Option A hosting runs each legacy personality on a dedicated compatibility core and
switches **which core is active** at the system level. The Z480 core does not emulate
legacy tiers internally.

## Overview

- P0–P2: Z85 compatibility core
- P3: Z90 compatibility core (Z180-class)
- P4–P6: Z380 compatibility core
- P7: Z480 native core

The active core is controlled by `tier_host_ctrl.sv`, which exposes a small MMIO window
used by firmware to issue `MODEUP`/`RETMD` requests.

## Memory map

The tier host window is defined in `carbon_memmap_pkg.sv`:

- SYS16: `CARBON_SYS16_TIER_HOST_BASE` (0x0000_F300), 256 B window
- SYSX86: `CARBON_SYSX86_TIER_HOST_BASE` (0x000F_3000), 4 KiB window

## Register interface (MMIO)

All offsets are byte offsets from the base address.

| Offset | Name | Description |
|---:|---|---|
| 0x00 | REQ | write target tier (bit7=1 for RETMD, bit7=0 for MODEUP) |
| 0x04 | STATUS | active tier/core + stack depth + error flags |
| 0x08 | ENTRY_LO | entry address (low 32, reserved in v1) |
| 0x0C | ENTRY_HI | entry address (high 32, reserved in v1) |
| 0x10 | CTRL | write bit0 to clear error flags |

`STATUS` fields:
- `[7:0]` active tier
- `[15:8]` mode stack depth
- `[17:16]` active core index
- `[24]` invalid request
- `[25]` stack overflow
- `[26]` stack underflow

## Behavior

- Reset starts in P0 (active core = Z85).
- `MODEUP(target)` is **monotonic** (target must be higher than current tier).
- `RETMD` returns to the previous tier stored on the mode stack.
- Errors set status flags but do not change the active tier.
- When the active core changes, a one-cycle `core_run_pulse` is asserted and
  `core_halt_req` is asserted for all other cores.

`ENTRY_LO/HI` are latched for future use (entry-point handoff); they are not consumed
by v1 cores.
