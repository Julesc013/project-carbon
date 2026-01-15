# OS Architecture

Purpose
- Describe JC-DOS structure, services, and execution model.

Scope
- OS layering, PAL boundary, EE hosting, and service contracts.

OS layers
- JC-DOS core runs in the highest available tier and consumes PAL services.
- Execution Environments (EE) host legacy guests under JC-DOS control.
- Platform-specific details are isolated behind PAL and board packs.

Service model
- Console, block storage, timer, and memory map are required services.
- Optional services are capability-gated and must be deterministic.

Contracts and compatibility
- Canonical OS hardware contract: source/common/spec/JC0_OS_CONTRACT.md.
- JC-DOS architecture detail: docs/JC-DOS_ARCHITECTURE.md.
- EE contracts: docs/EE.md and source/common/spec/SPEC_EE.md.

Boot and handoff
- BIOS constructs BDT/CAPSET and hands off via jc_dos_handoff.
- MODEUP/RETMD define tier transitions; see docs/SPEC_MODEUP.md.
