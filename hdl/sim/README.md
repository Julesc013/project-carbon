# HDL Simulation (v1.0)

Project Carbon uses a small set of SystemVerilog smoke tests and contract tests under `hdl/sim/`.

## Prerequisites

- Python (for `scripts/gen_arch.*`)
- `make`
- Simulator: Verilator or Icarus Verilog (`iverilog` + `vvp`)

## Quick start

- Generate architecture constants: `scripts/gen_arch.sh` (Linux/macOS) or `scripts/gen_arch.ps1` (Windows)
- Run the default smoke suite: `scripts/run_sim.sh` or `scripts/run_sim.ps1`
- Run all regression tests: `scripts/run_sim.sh --all` or `scripts/run_sim.ps1 -All`
- Run all contract tests: `scripts/run_sim.sh --suite contract` or `scripts/run_sim.ps1 -Suite contract`
- Run a single test by Make target: `make -C hdl/sim tb_carbonz80`

## Regression manifest

`hdl/sim/tests/regress.yaml` defines the default ordered set of tests executed by `scripts/run_sim.*`.
See `hdl/sim/docs/USAGE.md` for full usage and extension notes.

## Notes

- The simulation Makefile supports Verilator and Icarus Verilog.
- If a simulator is missing, `scripts/run_sim.*` fails with a clear dependency message.
