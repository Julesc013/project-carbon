# Z380 Platform Glue Blocks

This document describes the Z380 platform/uncore blocks used by CarbonZ380.
These blocks are optional and intended for compatibility adapters (chip selects,
wait-state insertion, and refresh timing). They do not alter core datapath
semantics.

## Modules

### z380_chipselect

Programmable address range decoder with per-range wait profile metadata.

Inputs/outputs:
- `addr_valid`, `addr` drive decode.
- `cs_match` is a per-range hit vector.
- `cs_any`, `cs_index`, and `cs_wait_profile` report the first matching range.

CSR map (base `0x00A21000`, 16-byte stride per range):
- `+0x00`: BASE (address base)
- `+0x04`: MASK (address mask)
- `+0x08`: WAIT (low 4 bits = wait profile index)

Ranges with mask = 0 are treated as disabled.

### z380_waitgen

Wait-state generator with programmable profiles.

Inputs/outputs:
- `req_valid`/`req_profile` start a wait profile.
- `wait_active` stays high while wait cycles are consumed.
- `wait_done` pulses when the wait profile completes.

CSR map (base `0x00A22000`, 4-byte stride per profile):
- `+0x00 + i*4`: WAIT_COUNT for profile `i` (low bits used)

### z380_dram_refresh

Refresh tick generator with a placeholder CAS-before-RAS model.

Outputs:
- `refresh_tick` pulses when a refresh is issued.
- `refresh_active` stays high for the programmed pulse width.

CSR map (base `0x00A23000`):
- `+0x00`: CTRL (bit 0 = enable)
- `+0x04`: PERIOD (refresh interval in cycles)
- `+0x08`: PULSE (active width in cycles)
- `+0x0C`: STATUS (active/tick + counters)

## Integration notes

- The blocks are instantiated in `hdl/systems/CarbonZ380/rtl/carbonz380_top.sv`.
- They are wired to a CSR tieoff by default; systems may attach a CSR master
  for runtime configuration.
- The current CarbonZ380 fabric does not consume wait/refresh signals yet.
