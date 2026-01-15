# Documentation Index

This index points to the canonical home for each topic. If multiple documents
touch the same topic, follow the "canonical" note in the target file.

## Architecture and layering
- docs/ARCHITECTURE.md: system-level architecture and layering.
- docs/HARDWARE_ARCHITECTURE.md: CPUs, SoCs, peripherals, tiers.
- docs/FIRMWARE_ARCHITECTURE.md: JC-BIOS and PAL boot flows.
- docs/OS_ARCHITECTURE.md: JC-DOS model, services, and execution.
- docs/PAL.md: PAL contract index and references.
- docs/EE.md: Execution Environment contract index and references.

## Contracts, determinism, and dependencies
- docs/CONTRACTS.md: ABI/API contract map and versioning pointers.
- docs/DEPENDENCIES.md: allowed and forbidden dependency directions.
- docs/DETERMINISM.md: determinism rules and known limits.
- docs/contract_versioning.md: versioning policy details.
- docs/error_model.md: error mapping conventions and expectations.

## Specs and machine-readable sources
- docs/SPEC_*.md: spec entry points (see each file for canonical sources).
- source/common/spec/: normative text specs for PAL, EE, BDT, and device classes.
- hdl/spec/: machine-readable contract sources.
- docs/ARCH_CONTRACTS.md: generated contract reference summary.

## Boot, platform, and compatibility
- docs/boot_z80.md and docs/boot_pcbios.md: boot models.
- docs/platform/: platform profiles, memory maps, hosting tiers.
- docs/COMPAT_LADDERS.md: CPU/FPU tier ladders.
- docs/compat_gem.md and docs/compat_windows.md: guest compatibility notes.
- docs/LEGACY_SUPPORT.md: legacy platform constraints.

## Verification and simulation
- docs/VERIFICATION.md: verification strategy and conformance artifacts.
- hdl/sim/README.md: HDL simulation and regression workflow.
- source/sim/carbon_sim/roms/README.md: ROM policy for carbon-sim.
