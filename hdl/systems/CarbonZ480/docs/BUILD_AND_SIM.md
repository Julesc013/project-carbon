# CarbonZ480 — Build & Sim (v1)

This directory provides the system top and a smoke test.

## Run (Icarus Verilog)

From `hdl/sim`:

```sh
make tb_carbonz480
```

The smoke test checks the MMIO `SIGNATURE` written by the fabric boot master and then observes `POWEROFF`.
