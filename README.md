# Project Carbon

A family of retro-style computer designs (hardware code, simulators, and schematics) built around shared specifications so different implementations stay compatible.

## 2. High-level overview (non-technical)

Project Carbon is a repository for designing and testing classic-style computers: it includes hardware design files, code that describes CPUs and systems, and simulators that let you run small programs without building physical hardware.

What makes it distinct is its **contract-first** approach: the architecture is defined as machine-readable specifications, and the project generates shared constants and documentation from those specs so every core, system, and test agrees on the same rules.

This reduces the chance that cores, tests, docs, and tools quietly diverge over time.

What it is **not**:
- A complete, end-user computer kit or a polished emulator distribution.
- A repository of copyrighted ROMs or operating system images (you must supply your own).
- A cycle-accurate reproduction of legacy buses and full peripheral ecosystems (many peripherals and timing models are explicitly deferred).

## 3. Key features (at a glance)

- Frozen v1.0 architecture contracts in `hdl/spec/*.yaml` with generated SystemVerilog/C constants.
- Compatibility tier ladders and a single mode-switching contract (`MODEUP`/`RETMD`).
- Shared HDL interfaces (fabric/CSR/IRQ/debug/accelerator) plus contract tests.
- SystemVerilog cores: Z85, Z90, Z480 (P7 scaffold), 8096, 8097, Am9513.
- Integrated system simulation tops and regression runner targeting Icarus Verilog.
- `carbon-sim` C++ simulator for CP/M 2.2 and RomWBW-style platforms (ROMs not included).
- KiCad hardware: a Carbon_Z80 project plus a KiCad 9 schematic skeleton generator.

## 4. Architecture overview (mid-level technical)

### Layering (source-of-truth → generated → implementations)

- **Docs & contracts**
  - `docs/ARCHITECTURE_OVERVIEW.md`: human overview of the v1.0 contract freeze.
  - `hdl/spec/*.yaml`: machine-readable source of truth.
  - `hdl/tools/gen_specs.py` → generates `hdl/gen/*` and renders `docs/ARCH_CONTRACTS.md`.
- **HDL cores (CPU/accelerators)**
  - `hdl/cores/*`: CPU families and accelerators (RTL + testbenches + per-core docs).
- **HDL systems (integrations)**
  - `hdl/systems/*`: integrated "tops" (core + ROM/RAM + memory-mapped I/O + wiring) with smoke tests and memory maps.
- **HDL simulation & verification**
  - `hdl/sim/*`: Makefile-based smoke/contract/system tests (Icarus Verilog), driven by `hdl/sim/tests/regress.yaml`.
- **Host-level simulator(s)**
  - `source/sim/carbon_sim`: `carbon-sim` (C++17) with CP/M 2.2 and RomWBW platform models; optional Verilator backend is scaffolding.
- **OS/software/firmware (repository content)**
  - `source/`: currently includes `carbon-sim`, a bundled Small Computer Workshop tool under `source/SCM/`, and placeholder directories (e.g., `source/JC-BIOS`, `source/JC-DOS`).
- **Schematics**
  - `schem/Carbon_Z80`: a KiCad project with exported PDFs/PNGs/SVGs under `schem/Carbon_Z80/export/`.
  - `schem/kicad9`: generator-owned schematic skeletons (`generated/`) plus hand-edited space (`manual/`) driven by mapping specs (`spec/`).

### Design philosophy (as implemented in v1)

- **Determinism & reproducibility**: generators are deterministic; CI verifies generated outputs are committed.
- **Explicit contracts**: shared enums/bitfields/opcode pages/queue formats live in specs, not ad-hoc RTL.
- **Portability-minded tooling**: scripts exist for POSIX shell and PowerShell; generators avoid third-party dependencies.
- **Long-term maintainability**: clean module boundaries (notably the Z480 scaffold) so implementations can evolve behind stable interfaces.

## 5. Supported platforms (summary)

Primary (actively used by the repo and CI):
- **HDL regression**: Icarus Verilog (`iverilog`/`vvp`) + `make` via `hdl/sim/`.
- **Spec/code generation**: Python via `scripts/gen_arch.*`.

Secondary / experimental:
- **`carbon-sim` desktop simulator**: CMake build (`source/sim/carbon_sim`); optional Verilator backend is preview scaffolding.
- **KiCad schematics**: Carbon_Z80 KiCad project and KiCad 9 generated skeletons under `schem/kicad9/generated/`.

## 6. Intended audience & use cases

This project is for:
- RTL/hardware engineers exploring CPU, accelerator, and system integration patterns with explicit contracts.
- Retrocomputing hobbyists who want a testable platform (simulation + schematics) for “small computer” designs.
- Contributors who prefer deterministic generators and contract tests over hand-maintained duplicated constants.

Example use cases:
- Implement a new core or accelerator that conforms to the v1 contract layer.
- Run contract/system smoke tests to validate integration plumbing.
- Use `carbon-sim` to bring up ROM-based environments you supply (e.g., CP/M or RomWBW variants).

Not a fit if you need:
- Turn-key ROMs/OS images or full software distributions.
- Full instruction/peripheral coverage and cycle-accurate platform timing (see deferred lists and per-core docs).

## 7. Design constraints & philosophy

- **Contracts are the source of truth**: `hdl/spec/*.yaml` drives generated headers/packages and the rendered contract reference.
- **Generated outputs are treated as artifacts**: `hdl/gen/*` and `docs/ARCH_CONTRACTS.md` are generated and committed (verified in CI).
- **Minimal dependency stance**: key tooling is dependency-light (e.g., a deterministic, stdlib-only spec generator; a simple regression manifest; JSON-in-YAML KiCad mapping specs).
- **Compatibility and gating are explicit**: tier ladders, `MODEUP`/`RETMD`, and strict-mode extension gating are architectural concepts, not local hacks.
- **Generated vs hand-edited separation**: `schem/kicad9/generated/` is safe to overwrite; `schem/kicad9/manual/` is not.

## 8. Repository structure (map)

- `docs/`: architecture/contracts docs plus legacy design notes, manuals, datasheets, and images.
- `hdl/`: HDL contract layer and implementations.
  - `hdl/spec/`: v1.0 specs (source of truth).
  - `hdl/gen/`: generated constants (committed; do not hand-edit).
  - `hdl/common/`: shared interfaces/utilities.
  - `hdl/cores/`: CPU/accelerator RTL + TBs.
  - `hdl/systems/`: integrated system tops + TBs.
  - `hdl/sim/`: regression harness and tests.
- `schem/`: KiCad projects and schematic generation.
  - `schem/Carbon_Z80/`: board-level KiCad project + exports.
  - `schem/kicad9/`: generated/manual schematic trees + mapping specs.
- `source/`: software and simulator sources (notably `source/sim/carbon_sim`).
- `scripts/`: wrappers for regenerating specs, running HDL regressions, and regenerating KiCad skeletons.
- `tools/`: utilities (`tools/kicadgen` and `tools/mk_disk.py`).

## 9. Documentation map

- Architecture contracts overview: `docs/ARCHITECTURE_OVERVIEW.md`
- Frozen contract reference (generated): `docs/ARCH_CONTRACTS.md`
- Compatibility ladders (CPU/FPU tiers): `docs/COMPAT_LADDERS.md`
- System memory map index: `docs/platform/SYSTEM_MEMORY_MAPS.md`
- CPU core docs:
  - `hdl/cores/Z85/docs/Z85_v1.md`
  - `hdl/cores/Z90/docs/Z90_v1.md`
  - `hdl/cores/Z380/docs/Z380.md`
  - `hdl/cores/Z480/docs/Z480.md`
- FPU tier docs:
  - `docs/fpu/Am9513.md`
  - `docs/fpu/Am9514.md`
  - `docs/fpu/Am9515.md`
- Verification flow and regression philosophy: `docs/VERIFICATION.md`
- HDL contract layer README: `hdl/README.md`
- v1.0 release contents: `docs/RELEASE_v1.md`
- Deferred/non-goals list (v1.0): `docs/DEFERRED.md`
- HDL simulation prerequisites/usage: `hdl/sim/README.md`
- System memory maps & smoke tests (examples):
  - `hdl/systems/CarbonZ80/docs/MEMORY_MAP.md`
  - `hdl/systems/CarbonX96/docs/MEMORY_MAP.md`
- `carbon-sim` usage and platform maps:
  - `source/sim/carbon_sim/docs/USAGE.md`
  - `source/sim/carbon_sim/docs/PLATFORMS.md`
  - ROM policy: `source/sim/carbon_sim/roms/README.md`
- KiCad 9 generated/manual workflow: `schem/kicad9/docs/USAGE.md`
- Carbon_Z80 schematic/PCB exports: `schem/Carbon_Z80/export/Carbon_Z80_150_sch_rev1.pdf`
- Release notes: `CHANGELOG.md`

## 10. Build / usage (high-level only)

- HDL (generate + run regressions): see `hdl/sim/README.md` and `docs/RELEASE_v1.md`.
- `carbon-sim` (build/run): see `source/sim/carbon_sim/docs/USAGE.md`.
- KiCad skeleton regeneration: see `schem/kicad9/docs/USAGE.md`.

## 11. Project status & maturity

- Repository version: **v1.0.0** (`VERSION`).
- The **contract/spec layer is frozen for v1.0** and the generator outputs are CI-checked for reproducibility.
- Several cores and systems are intentionally **subset/scaffold implementations** (e.g., partial legacy ISA coverage, minimal peripherals); see `docs/DEFERRED.md` and the per-core docs under `hdl/cores/*/docs/`.
- The primary “known-good” workflows in v1.0 are spec generation and HDL regression in CI; additional platforms (e.g., `carbon-sim` backends) evolve separately.

## 12. License

License: not specified in repository.

## 13. Contributing / contact (if applicable)

This repository includes CI and regression tooling under `.github/` and `scripts/`. If you contribute changes, keep generated outputs in sync and include enough context in your PR/commit to review the contract impact.
