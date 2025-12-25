# JC-DOS Architecture (JC0)

Purpose
- Define the DOS components and contract dependencies for v1.

Scope
- JC0 provides structure, contracts, and guards only.
- No runtime OS, filesystem, or shell functionality is implemented.

Subsystems
- kernel: boot handoff, scheduling stubs, system calls.
- fs: CPMX filesystem parsing and block I/O stubs.
- shell: command dispatch stubs.
- drivers: device-class bindings via the BDT.

Contract dependencies
- CPU/FPU tiers and profiles: `SPEC_TIERS`, `SPEC_PROFILES`.
- Mode ABI: `SPEC_MODE`.
- Device discovery: `SPEC_DISCOVERY`, `SPEC_CAPSET`, `SPEC_BDT`.
- Device ABIs: `SPEC_DEV_UART`, `SPEC_DEV_TIMER`, `SPEC_DEV_PIC`,
  `SPEC_DEV_STORAGE_IDEPIO`.
- Program format: `SPEC_JCOM`.
- Filesystem: `SPEC_FS_CPMX`.

Binding model
- Devices are resolved by (class, instance) using the BDT.
- All polling uses tick-based deadlines; IRQs are optional.

Error handling
- DOS surfaces errors via `jc_error_t` codes and stable category ranges.
