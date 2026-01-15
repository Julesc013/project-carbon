# Hardware Architecture

Purpose
- Summarize CPU, SoC, and peripheral architecture as implemented in HDL.

Scope
- CPU tiers and profiles, cores and accelerators, system integration, and buses.

CPU tiers and profiles
- Tier ladder and profiles are contract-defined; see docs/COMPAT_LADDERS.md.
- Canonical tier/profile specs live in source/common/spec/SPEC_TIERS.md and
  source/common/spec/SPEC_PROFILES.md.
- CPU family docs live in docs/cpu/ and hdl/cores/*/docs/.

Cores and accelerators
- CPU cores: Z85, Z90, Z380, Z480.
- FPU and accelerator families: Am95xx and CAI-facing devices.
- Shared interfaces: hdl/common/if and hdl/common/fabric.

Systems and integration
- hdl/systems/* provides top-levels, memory maps, and smoke tests.
- hdl/common/* supplies fabric arbitration, CSR, IRQ, and debug hubs.

Peripherals and buses
- Device model contracts: docs/DEVICE_MODEL.md and docs/DEVICES_OVERVIEW.md.
- Legacy bus adapters and tiers: docs/platform/ and docs/LEGACY_SUPPORT.md.
