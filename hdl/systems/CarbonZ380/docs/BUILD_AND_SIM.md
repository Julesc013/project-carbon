# CarbonZ380 — Build & Sim (v1)

This directory provides the system top and a smoke test.

## Run (Icarus Verilog)

From `hdl/sim`:

```sh
make tb_carbonz380_smoke
```

The smoke test waits for the MMIO `POWEROFF` register to be written and checks
the MMIO `SIGNATURE` value plus the trap cause/EPC from the core.
