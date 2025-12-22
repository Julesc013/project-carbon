# Project Carbon v1.0 Release

Project Carbon v1.0 is a coherent HDL platform with:

- Generated architecture constants (`hdl/gen/`) from YAML specs
- Common fabric/CSR/IRQ/CAI infrastructure with contract tests
- Core/accelerator scaffolds and five integrated Carbon* system simulation tops
- A unified regression runner and CI configuration

## Quick start (simulation)

- Generate constants: `scripts/gen_arch.sh` or `scripts/gen_arch.ps1`
- Run all regressions: `scripts/run_sim.sh --all` or `scripts/run_sim.ps1 -All`
- Run one test directly: `make -C hdl/sim tb_carbonz80`

See `hdl/sim/README.md` for simulator prerequisites and details.

## What v1.0 includes

- Cores: Z85, Z90, Z480 (P7 scaffold), 8096, 8097
- Accelerator: Am9513 with legacy (9511/9512) personalities and native CAI path
- Systems: CarbonZ80/CarbonZ90/CarbonZ480/CarbonX86/CarbonX96 simulation tops, RAM/ROM/MMIO, and smoke TBs
- Verification: contract tests for `fabric_if`, CAI descriptor/completion handling, and basic CSR privilege gating plumbing

## Deferred features (explicit)

See `docs/DEFERRED.md` for the project-wide deferred list, organized by subsystem.

## Extending the platform

- Specs live in `hdl/spec/*.yaml`; regenerate constants via `scripts/gen_arch.*`
- New cores should land under `hdl/cores/<name>/rtl` with TBs under `hdl/cores/<name>/tb`
- New systems should land under `hdl/systems/<name>/rtl` with smoke TBs under `hdl/systems/<name>/tb`
- Add new regression entries to `hdl/sim/tests/regress.yaml` and a Make target under `hdl/sim/Makefile`
