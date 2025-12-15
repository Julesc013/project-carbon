# Project Carbon — Architecture Overview (v1.0 freeze)

This document describes the high-level architecture contract that future CPU cores, accelerators, and SoCs consume.
The frozen, machine-readable contract is in `hdl/spec/*.yaml`; generated constants are in `hdl/gen/`; and the
rendered summary is `docs/ARCH_CONTRACTS.md` (auto-generated).

## Project Families

- **Z85 / Z90 / eZ90**: Z80-derived compatibility family; eZ90 at P7 provides the CPUID instruction transport, while Z85/Z90 provide a CAPS mirror of the same leaf model.
- **8096 / 8097**: x86-derived compatibility family line (tier ladder contract shared across implementations).
- **Am951x / Am9513-class**: AMD-derived numeric/FPU accelerators; presence is reported via discovery and exposed to software via CAI.

## Compatibility Tiers

- Tiers form monotonic ladders: reset starts at `P0`; upgrades only; downgrades only via `RETMD`.
- Three ladders are defined: Z80-derived, x86-derived, and AMD-derived FPU.
- `P0–P6` are **strict** (no turbo/extension behaviors). `P7` is `TURBO_UNLIMITED` (**turbo** enabled).

## Mode Switching

- **Single canonical mechanism**: `MODEUP(target_tier, entry_vector)` and `RETMD()`.
- `MODEUP` pushes a mode frame (previous tier + flags + return PC), flushes prefetch/decode state, masks interrupts during the atomic transition, and jumps to `entry_vector`.
- `RETMD` pops a mode frame, restores tier/flags/PC, flushes prefetch/decode state, and traps on underflow.
- `MODEFLAGS` is a small, reserved-for-growth bitfield defined by the contract.

## Discovery

- A unified leaf model describes vendor/family/model/stepping, supported ladder + max tier, feature bitmaps, topology, cache, accelerators, and errata.
- **eZ90 P7**: `CPUID` instruction transport.
- **Z85/Z90**: `CAPS` index+data transport that mirrors the same leaf IDs and packing.

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

