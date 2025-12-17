# CarbonEZ90 — Build & Sim (v1)

This directory provides the system top and a smoke test.

## Run (Icarus Verilog)

From `hdl/sim`:

```sh
make tb_carbonez90
```

The smoke test checks the MMIO `SIGNATURE` written by the fabric boot master and then observes `POWEROFF`.

