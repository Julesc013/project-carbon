# Project Carbon v1.0 Release

Project Carbon v1.0 is a coherent HDL platform with:

- Generated architecture constants (`hdl/gen/`) from YAML specs
- Common fabric/CSR/IRQ/CAI infrastructure with contract tests
- CPU cores through Z480 and Am95xx accelerators through Am9515
- Integrated CarbonZ80/Z90/Z380/Z480 system tops with smoke tests
- A unified regression runner and consistency checks

## Quick start (simulation)

- Generate constants: `scripts/gen_arch.sh` or `scripts/gen_arch.ps1`
- Run all regressions: `scripts/run_sim.sh --all` or `scripts/run_sim.ps1 -All`
- Run one test directly: `make -C hdl/sim tb_carbonz80`
- Run host sim: `source/sim/carbon_sim` (see `source/sim/carbon_sim/docs/USAGE.md`)

See `hdl/sim/README.md` for simulator prerequisites and details.

## What v1.0 includes

- CPU tiers: Z85 (P2), Z90 (P3), Z380 (P6), Z480 (P7)
- FPU tiers: Am9513 (P2), Am9514 (P3), Am9515 (P4), plus Am9511/Am9512 personalities
- Systems: CarbonZ80/Z90/Z380/Z480 system tops with SYS16 memory maps and smoke/tier tests
- Platform glue: CarbonIO/CarbonDMA, BDT/BSP scaffolding, tier host controller
- Verification: contract tests for `fabric_if`, CAI descriptor/completion handling, and CSR plumbing

## Deferred features (explicit)

- x86/x87 lineage and CarbonX86/CarbonX96 system validation
- Full CP/M or RomWBW OS integration beyond current sim hooks/stubs
- Unimplemented opcode coverage where deterministic traps remain

See `docs/DEFERRED.md` for the project-wide deferred list, organized by subsystem.

## Extending the platform

- Specs live in `hdl/spec/*.yaml`; regenerate constants via `scripts/gen_arch.*`
- New cores should land under `hdl/cores/<name>/rtl` with TBs under `hdl/cores/<name>/tb`
- New systems should land under `hdl/systems/<name>/rtl` with smoke TBs under `hdl/systems/<name>/tb`
- Add new regression entries to `hdl/sim/tests/regress.yaml` and a Make target under `hdl/sim/Makefile`
