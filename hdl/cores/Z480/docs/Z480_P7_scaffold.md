# Z480 P7 Scaffold (v1)

This directory contains the **Z480 P7 (native tier)** core scaffold: a modular, OoO-ready RTL skeleton intended to be stable for long-term evolution. The v1 scaffold focuses on clean module boundaries and a working simulation-elaboratable top-level, not on finishing the ISA or microarchitecture.

## Top-Level

- `hdl/cores/Z480/rtl/z480_core.sv`: Z480 core top module.
  - Ports:
    - `fabric_if.master mem_if` (unified instruction+data for now; idle in v1)
    - `csr_if.slave csr` (CSR read/write window)
    - `irq_if.sink irq` (external interrupt delivery; scaffold only)
    - `dbg_if.core dbg` (halt/run/step; scaffold only)

## Module Split (RTL)

### Front-End (Fetch/Decode)

- `fe_fetch.sv`: sequential fetch (`pc+4`) with redirect hook.
- `fe_bpred.sv`: branch predictor stub (always not-taken).
- `fe_icache_port.sv`: front-end I$ hook stub (returns `0` instruction).
- `fe_decode.sv`: decode stub (emits NOP uops).
- `fe_uop_cache.sv`: uop-cache hook stub (pass-through).

### Rename / Dispatch

- `uop_queue.sv`: real ready/valid FIFO used to buffer uops.
- `renamer.sv`: stub renamer (arch->phys map + monotonic allocator).
- `dispatch.sv`: allocates ROB entries and routes uops into RS/LSQ.

### OoO Backend Skeleton

- `rob.sv`: ROB skeleton (allocate, mark done, commit head).
- `rs_int.sv`: integer reservation station skeleton (FIFO).
- `lsq.sv`: load/store queue skeleton (FIFO, no memory ops in v1).
- `scheduler.sv`: select-ready skeleton to route one uop/cycle to a FU.
- Execution unit stubs (mark ROB entry done, no real execute):
  - `exec_int_alu.sv`
  - `exec_branch.sv`
  - `exec_muldiv.sv`
  - `exec_vec.sv`
- `writeback.sv`: fixed-priority FU writeback arbiter into the ROB.
- `commit.sv`: commits in-order from the ROB head; exposes a retired counter.

### Privilege / MMU / Traps

- `priv_ctrl.sv`: U/S/H privilege mode scaffold + interrupt enable/pending framework.
- `mmu.sv`: MMU register scaffold + identity-translation hook interface.
- `trap_unit.sv`: trap cause/EPC state scaffold + return hooks (SRET/HRET stubs).
- `iommu_hook.sv`: placeholder for future IOMMU integration.

### Cache Hooks

- `icache_port.sv`: instruction cache hook interface (stub in v1).
- `dcache_port.sv`: data cache hook interface (stub in v1).

## CSR + CPUID Model

### Minimal CSR behavior (v1)

`z480_core.sv` implements the core-common CSRs required for bring-up:

- `CARBON_CSR_ID`: implementation-defined ID value.
- `CARBON_CSR_TIER`: fixed to P7 (writes only accepted if requesting P7).
- `CARBON_CSR_MODEFLAGS`: minimal MODEFLAGS storage (reserved bits must be 0).
- `CARBON_CSR_TIME` / `CARBON_CSR_TIME_HI`: free-running cycle counter.
- `CARBON_CSR_CAUSE` / `CARBON_CSR_EPC`: trap state (scaffold; privileged).
- `CARBON_CSR_DBG_CTRL` / `CARBON_CSR_DBG_STEP` / `CARBON_CSR_DBG_STATUS`: debug halt/run/step CSR mirror.

### CPUID exposure (CSR window)

Because the ISA is not finalized in v1, CPUID is exposed via a CSR window:

1. Write `leaf` to `CARBON_CSR_CPUID_LEAF`
2. Write `subleaf` to `CARBON_CSR_CPUID_SUBLEAF`
3. Read `CARBON_CSR_CPUID_DATA{0..3}_{LO,HI}` to obtain four 64-bit result lanes (the low 32 bits carry the discovery word).

`cpuid_block.sv` implements a minimal leaf model:

- `CARBON_CPUID_LEAF_VENDOR`: max leaf + vendor string
- `CARBON_CPUID_LEAF_ID`: vendor/family/model/stepping + `chip_flags`
- `CARBON_CPUID_LEAF_TIERS`: ladder ID + (current,max) tier
- `CARBON_CPUID_LEAF_FEATURES0`: base feature bitmap (from `hdl/spec/discovery.yaml`)
- `CARBON_CPUID_LEAF_TOPOLOGY`: core count + vector width (128) + arch width (64)

`chip_flags` (leaf `CARBON_CPUID_LEAF_ID`, word1) is implementation-defined for the scaffold:

- bit0: U supported
- bit1: S supported
- bit2: H supported
- bit3: OoO skeleton present
- bit4: MMU scaffold present

## What’s Implemented vs Deferred

Implemented in v1:

- Clean module split with stable interfaces for front-end, rename, ROB, RS/LSQ, scheduler, exec stubs, writeback, commit.
- CSR access for ID/tier/modeflags/time, trap placeholders, CPUID CSR window, debug halt/step CSR mirror.
- CPUID leaf model sufficient for discovery.
- Debug halt/run/step handshake (functional; not feature-complete).

Deferred / NOT implemented yet:

- Real ISA fetch/decode/execute (decode currently emits NOP uops).
- Real memory operations on `mem_if` (fabric is idle in v1).
- Cache implementations (only hook modules exist).
- MMU page-table walking, TLBs, access checks (identity hook only).
- Trap routing, precise exceptions, SRET/HRET semantics, vectoring.
- Interrupt controller integration and prioritization.
- Breakpoints/watchpoints, trace streaming, and full debug features.

## Extending the Scaffold

Typical upgrade paths are intended to be localized:

- Replace `fe_icache_port` with an actual I$ + fabric port (or connect through `icache_port.sv`).
- Replace `fe_decode` with a real decoder emitting `z480_uop_t` fields.
- Upgrade `renamer`, `rob`, `rs_*`, `lsq`, and `scheduler` to full OoO behavior without changing the external module boundaries.
- Add cache/MMU/IOMMU functionality behind the existing hook modules and translation interfaces.
