# Project Carbon JC0 Hardware Contract (OS View)

This document defines the OS-facing hardware contract for JC0. It is
normative for JC-BIOS, JC-DOS, and BSP implementations.

## 0) Global implementation constraints (non-negotiable)

- All project sources live under `source/`.
  - BIOS: `source/firmware/JC-BIOS/`
  - DOS: `source/os/JC-DOS/`
  - Shared: `source/common/`
- Language: ISO C89 only; no external dependencies; no libc assumptions beyond
  freestanding basics.
- Assembly allowed only where required for reset, traps, and tier transitions,
  under `source/**/arch/*`.
- Must run on:
  - period-correct physical hardware
  - FPGA implementations
  - simulation
- Parity is a gate: behavior is validated by conformance transcripts + hashes.

## 1) Carbon system model: tiers, profiles, discovery

### 1.1 Tiers are strict semantic environments

- There is no "turbo unlimited".
- The highest tier is the chip's fully defined native contract.
- Reset ALWAYS starts in P0.
- Tiers represent ISA + memory model + privilege model semantics (where
  applicable).

### 1.2 Profiles are configuration, not tiers

- System-wide configuration is one of:
  - PROFILE_CPU_ONLY
  - PROFILE_MCU
  - PROFILE_SOC_RETRO (PRIMARY v1 target)
  - PROFILE_SOC_WORKSTATION
- Profile is reported via discovery and must be honored.

## 2) CPU lineage (8080-derived) -- FINAL

Unified compatibility ladder:

| Tier | Label |
| --- | --- |
| P0 | 8080 |
| P1 | 8085 |
| P2 | Z80 |
| P3 | Z180 |
| P4 | eZ80 (24-bit ADL) |
| P5 | Z280 |
| P6 | Z380 |
| P7 | Z480 |

Carbon CPUs:

- Z85
  - Presents as P2
  - Strict Z80 semantics
  - Undocumented Z80 behavior is controlled by a feature bit, not a tier
- Z90
  - Presents as P3
  - Z180-class ISA/semantics
  - High internal performance, strict external ordering
- Z380
  - Presents as P6
  - Hosts P0-P5 as strict personalities
  - 32-bit addressing; native/extended modes
- Z480
  - Presents as P7
  - 64-bit native CPU
  - NO floating-point instructions
  - U/S/H privilege + paging MMU
  - CPUID/CAPS supported
  - Hosts P0-P6 via system-level hosting (Option A):
    - legacy tiers execute on dedicated compatibility cores (Z85/Z90/Z380)
    - Z480 executes native kernel/OS code
    - MODEUP/RETMD switches personalities at the system level (not intra-core
      microcode)

## 3) FPU lineage (Am95xx) -- FINAL

Executive ladder:

| Tier | Label |
| --- | --- |
| P0 | Am9511 (pre-IEEE, stack-based) |
| P1 | Am9512-plus (IEEE FP32/FP64 + restored 9511 functions) |
| P2 | Am9513 (async scalar IEEE engine) |
| P3 | Am9514 (vector/SIMD) |
| P4 | Am9515 (matrix/tensor) |
| P5+ | reserved |

Critical rules:

- CPUs contain NO FP instructions.
- All floating-point uses Am95xx devices.
- Am9513+ native interface uses CAI queues.
- P0/P1 legacy stack personalities may exist via MMIO windows.
- Any CPU may pair with any Am95xx device.

## 4) Mode transitions (non-negotiable)

Only these transitions exist:

- MODEUP(target_tier, entry) -- monotonic upgrade only
- RETMD() -- deterministically returns to the previous tier

Rules:

- Reset starts in P0.
- MODEUP may fail deterministically if unsupported; failure must be detectable
  and handled.
- Interrupt masking/state across transition must be explicitly defined (see
  MODE ABI).

## 5) Peripheral strategy (OS-critical)

There is no monolithic "ultimate I/O chip". Peripherals are partitioned.

### 5.1 CarbonKIO (MANDATORY FOR BOOT)

Must provide (polling MUST work; IRQ optional):

- UART (VT100 console)
- Timer/CTC (monotonic tick)
- GPIO/PIO
- PIC-like interrupt routing

### 5.2 CarbonDMA (separate block)

- Scatter/gather capable
- Non-coherent DMA baseline
- Optional for v1, but discoverable if present

### 5.3 CarbonStorage (separate controller)

- IDE/CompactFlash PIO minimum
- 512-byte blocks minimum (required)
- DMA optional later
- SD/SATA/USB not required for v1

### 5.4 CarbonSuperIO (optional, later)

- PS/2 kbd/mouse
- parallel
- floppy
- RTC

JC-BIOS must assume only: CarbonKIO + one block device is sufficient to boot.

## 6) Device discovery and BIOS Device Table (BDT) -- NON-NEGOTIABLE

### 6.1 No hardcoded bases outside BSP

- BIOS/DOS must never hardcode MMIO/I/O addresses outside BSP.
- BIOS/DOS read the BDT once at boot and cache an index.

### 6.2 Discovery provides (minimum)

- presented CPU tier
- presented FPU tier
- profile ID
- pointer to topology table
- pointer to BDT
- feature bitmaps and limits

### 6.3 BDT entries include (minimum)

- device class (UART, TIMER, PIC, DMA, STORAGE, ACCEL, VIDEO, etc.)
- instance ID
- MMIO or I/O base + span
- IRQ routing info
- capabilities + version
- for storage: block size (must support 512 bytes)

## 7) Mandatory boot flow (OS view)

Reset -> CPU in P0

Minimal ROM stub:

- mask interrupts
- read discovery
- identify profile and devices

Optional MODEUP to higher tier:

- CP/M 1.x -> stay P0/P1
- CP/M 2.2 -> P2
- CP/M 3+ -> P2/P3 with BIOS-managed banking
- JC-DOS -> highest available tier (Z90/Z380/Z480)

Remaining flow:

- BSP builds BDT-backed device map
- BIOS initializes console, timer, block device
- OS loads and runs
- RETMD must always return to prior tier deterministically

## 8) Coding-layer hard rules (modularity/robustness)

- Core code must not know addresses; BSP builds BDT and supplies only
  pointers/handles.
- All device binding is by (class, instance) via BDT.
- All polling loops are tick-deadline-based.
- Boot is a phase state machine with persistent last_error.
- Conformance tests are required artifacts per version.
