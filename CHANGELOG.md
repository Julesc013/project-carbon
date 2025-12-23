# Changelog

## 1.0.0

### Architecture + Infrastructure
- Generated architecture constants in `hdl/gen/` (via `scripts/gen_arch.*`)
- Finalized tier ladders for the 8080-derived CPUs and Am95xx lineage
- Common interfaces (`fabric_if`, `csr_if`, `cai_if`, `irq_if`, `dbg_if`) and BFMs
- CAI descriptor contracts, CSR map, and BDT/BSP scaffolding for system discovery
- Contract tests for fabric/IRQ/CSR/CAI plumbing

### Cores / Accelerators
- Z85: strict Z80-derived core (P2 presentation, undocumented feature bit)
- Z90: Z180-class core (P3 presentation, strict P0–P3 gating)
- Z380: P6 core with native/extended scaffolding and deterministic traps
- Z480: P7 native core subset with privilege/CSR/trap framework
- Am9513/Am9514/Am9515: Am95xx accelerator tiers with scalar/vector/tensor paths
- Am9511/Am9512 personalities hosted via legacy shells

### Systems
- CarbonZ80/CarbonZ90/CarbonZ380/CarbonZ480 system tops
- Z380 platform glue blocks (chip-selects, waitgen, refresh) integrated in CarbonZ380
- Tier hosting controller for CarbonZ480 compatibility clustering
- Memory maps + boot ROM stubs + smoke/tier TBs per system

### Simulation + CI
- `hdl/sim/Makefile` targets for smoke/contract/core/system tests
- `scripts/run_sim.*` regression runner using `hdl/sim/tests/regress.yaml`
- `carbon-sim` C++ platforms for CP/M, RomWBW, and CarbonZ systems (ROMs not included)
- CI hooks for generator + consistency checks + core regression subset

### Deferred (explicit)
- x86/x87 lineage and CarbonX86/CarbonX96 system validation
- Full OS integration beyond current stubs (CP/M, RomWBW)
- Unimplemented opcodes that are currently trapped

Notes:
- This changelog is curated; see git history for detailed per-commit context.
