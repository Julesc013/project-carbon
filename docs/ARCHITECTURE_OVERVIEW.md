# Project Carbon — Architecture Overview (v1.0 freeze)

This document summarizes the frozen architecture contract for Project Carbon. The authoritative, machine-readable
specs live in `hdl/spec/*.yaml`; generated constants are in `hdl/gen/`; and the rendered summary is
`docs/ARCH_CONTRACTS.md` (auto-generated).

## Core / Uncore / Chip / System

- **Core**: CPU tier state, MODEFLAGS, CSR access, IRQ delivery, and debug control.
- **Uncore**: fabric, caches, memory controllers, DMA engines, CAI accelerators, and KIO blocks.
- **Chip**: discovery table, topology table, and BDT stored in ROM and exposed via discovery pointers.
- **System**: BSP + BDT define device addressing and capabilities; no hardcoded ports outside BSP.

## Compatibility Tiers

- **CPU ladder**: unified 8080-derived ladder (`P0`..`P7`), with `P8`..`P15` reserved.
- **FPU ladder**: Am95xx ladder (Am9511 → Am9515, `P0`..`P4`), with `P5`..`P15` reserved.
- Presented tiers are reported via discovery; optional supersets are exposed via feature bits.

## Mode Switching

- **Only two instructions**: `MODEUP(target_tier, entry_vector)` and `RETMD()`.
- `MODEUP` is upgrade-only, pushes a mode frame (prev tier + flags + return PC), flushes prefetch/decode, masks interrupts during the transition, and jumps to `entry_vector`.
- `RETMD` is the only downgrade path and restores the prior tier/modeframe state; traps on underflow.

## CPU/FPU Boundary

- Z90/Z380/Z480 include **no** floating-point instructions or FP register files.
- Floating point is provided by Am95xx devices; Am9513+ must expose a CAI-native interface.

## Profiles

- **PROFILE_CPU_ONLY**: minimal core + CSR/IRQ/DBG.
- **PROFILE_MCU**: adds KIO + timer; requires UART + timer; safe mode forces UART console, caches off, P0.
- **PROFILE_SOC_RETRO**: adds DMA + storage; legacy Z80 bus adapter present.
- **PROFILE_SOC_WORKSTATION**: adds CAI accelerators and limits table.

## Discovery Model

- A **canonical discovery table** contains presented tiers, profile ID, topology pointer, BDT pointer, limits table pointer, and feature bitmap pointers.
- **Z480 P7** uses `CPUID`; **Z85/Z90** use `CAPS` (index/data mirror of CPUID leaves).
- Topology and BDT are authoritative for core count and device enumeration.

## Multiprocessing and Topology

- Z480 supports coherent SMP within a socket; core count is discoverable, not a tier.
- Multi-socket and SMT are expressed in topology tables and profiles, not tier changes.

## External Interfaces and Option A Hosting

- Legacy external profiles cover RC2014/S-100 bus adapters; modern SoC profiles abstract external memory/peripherals.
- **Option A hosting**: the Carbon CPU is the primary host, booting from ROM that exposes discovery + BDT; safe-mode strap ensures UART console, caches off, and P0.

## Regenerating Outputs

- PowerShell: `.\scripts\gen_arch.ps1`
- POSIX shell: `./scripts/gen_arch.sh`
- Direct: `python hdl/tools/gen_specs.py`
