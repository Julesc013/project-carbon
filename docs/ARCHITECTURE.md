# Architecture (v1.0)

Purpose
- Describe system layering and contract flow for Project Carbon.
- Identify canonical sources for specs and generated artifacts.

Scope
- Contract specs and generated outputs.
- HDL cores/systems and shared interfaces.
- Firmware/OS boundaries, PAL, and EE.
- Simulation and tooling inputs.

Sources of truth
- hdl/spec/*.yaml: machine-readable contracts (authoritative).
- hdl/gen/* and docs/ARCH_CONTRACTS.md: generated artifacts.
- source/common/spec/*.md: PAL/EE/BDT and device-class specs.
- source/common/include/*.h: public ABI headers.

Layering
- Contract layer: hdl/spec and source/common/spec.
- HDL implementations: hdl/common, hdl/cores, hdl/systems.
- Firmware and OS: source/firmware/JC-BIOS, source/os/JC-DOS.
- Adaptation boundary: PAL binds platform-specific boot and devices.
- Execution environments: EE providers host guest OS/programs.
- Simulation and tooling: hdl/sim, source/sim/carbon_sim, scripts/tools.

Boundary rules
- BIOS/OS code never hardcode device addresses; BDT is authoritative.
- PAL is the only layer allowed to depend on platform boot details.
- Contracts are versioned and must be checked at boot or bind time.

Related docs
- docs/HARDWARE_ARCHITECTURE.md
- docs/FIRMWARE_ARCHITECTURE.md
- docs/OS_ARCHITECTURE.md
- docs/CONTRACTS.md
