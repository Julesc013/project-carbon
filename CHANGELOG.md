# Changelog

## 1.0.0

### Architecture + Infrastructure
- Generated architecture constants in `hdl/gen/` (via `scripts/gen_arch.*`)
- Common interfaces (`fabric_if`, `csr_if`, `cai_if`, `irq_if`, `dbg_if`) and BFMs
- Contract tests for fabric/IRQ/CAI plumbing

### Cores / Accelerators
- Z85: strict Z80-derived core + reference-model TB
- Z90: Z90 core scaffold with mode ladder + CAI host hooks
- eZ90: P7 scaffold with modular split, CSRs, and CPUID window
- Am9513: fabric-attached accelerator with legacy (9511/9512) shells + CAI ring engine
- 8096/8097: 8086/8087-compatible v1 subsets with P7 turbo gating hooks

### Systems
- CarbonZ80, CarbonZ90, CarbonEZ90, CarbonX86, CarbonX96 system tops
- Memory maps + boot ROM stubs + smoke TBs per system

### Simulation + CI
- `hdl/sim/Makefile` targets for smoke/contract/core/system tests
- `scripts/run_sim.*` regression runner using `hdl/sim/tests/regress.yaml`
- GitHub Actions CI running generator + regression suite

Notes:
- This changelog is curated; see git history for detailed per-commit context.

