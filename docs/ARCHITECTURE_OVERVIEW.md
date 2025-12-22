# Project Carbon — Architecture Overview (v1.0 freeze)

This document describes the high-level architecture contract that future CPU cores, accelerators, and SoCs consume.
The frozen, machine-readable contract is in `hdl/spec/*.yaml`; generated constants are in `hdl/gen/`; and the
rendered summary is `docs/ARCH_CONTRACTS.md` (auto-generated).

## Project Families

- **Z85 / Z90 / Z480**: Z80-derived compatibility family; Z480 at P7 provides the CPUID instruction transport, while Z85/Z90 provide a CAPS mirror of the same leaf model.
- **8096 / 8097**: x86-derived compatibility family line (tier ladder contract shared across implementations).
- **Am951x / Am9513-class**: AMD-derived numeric/FPU accelerators; presence is reported via discovery and exposed to software via CAI.

## Compatibility Tiers

- Tiers form monotonic ladders: reset starts at `P0`; upgrades only; downgrades only via `RETMD`.
- Three ladders are defined: Z80-derived CPU (8080 → Z480, `P0`..`P7`), x86-derived CPU (`P0`..`P7`), and Am95xx FPU (Am9511 → Am9515, `P0`..`P4`, `P5`..`P15` reserved).
- Presented tiers are reported via discovery; optional supersets are exposed via feature bits (e.g., Z85 undocumented Z80, Z90 Z180-class, Z380 32-bit extended, Z480 native 64, Am9512 IEEE, Am9513 async, Am9514 vector, Am9515 tensor).

## Mode Switching

- **Single canonical mechanism**: `MODEUP(target_tier, entry_vector)` and `RETMD()`.
- `MODEUP` pushes a mode frame (previous tier + flags + return PC), flushes prefetch/decode state, masks interrupts during the atomic transition, and jumps to `entry_vector`.
- `RETMD` pops a mode frame, restores tier/flags/PC, flushes prefetch/decode state, and traps on underflow.
- `MODEFLAGS` is a small, reserved-for-growth bitfield defined by the contract.

## Discovery

- A unified leaf model describes vendor/family/model/stepping, supported ladder + max tier, feature bitmaps, topology, cache, accelerators, and errata.
- **Z480 P7**: `CPUID` instruction transport.
- **Z85/Z90**: `CAPS` index+data transport that mirrors the same leaf IDs and packing.
- Discovery reports presented tier and max tier for both CPU and FPU lineages, with optional extras described by feature bits.

## CSR Model

- A global CSR address scheme uses `(vendor_id, block_id, block_version, reg_id)` packed into a 32-bit address.
- Block-ID ranges partition common core CSRs, MMU/VM CSRs, interrupt/timer CSRs, debug/trace CSRs, cache control CSRs, fabric CSRs, and accelerator CSRs, plus reserved ranges for future expansion.

## Fabric + CAI

- **Fabric** defines internal request/response transaction types, packed per-transaction attributes, response codes, and ready/valid stability requirements suitable for a SystemVerilog interface definition.
- **CAI (Carbon Accelerator Interface)** defines a standard submission/completion queue model (doorbell + rings) with fixed descriptor and completion record formats.

## Regenerating Outputs

- PowerShell: `.\scripts\gen_arch.ps1`
- POSIX shell: `./scripts/gen_arch.sh`
- Direct: `python hdl/tools/gen_specs.py`
