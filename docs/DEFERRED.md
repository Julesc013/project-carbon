# Deferred features (v1.0)

This file explicitly lists what is *not* implemented in v1.0, by subsystem.

## Z85

- Cycle-accurate pin-level bus timing (handled later by bus adapters)
- External bus socket adapters (RC2014/S-100 style), wait-state tuning, and contention modelling
- Full Z80 peripheral ecosystem (PIO/CTC/SIO) integration

## Z90

- Optional caches/predictor, deeper pipeline, and performance features beyond the current scaffold
- Wider/extended instruction coverage beyond the implemented subset
- Full CAI software stack/driver integration (descriptor setup in real firmware/OS)

## Z480 (P7 scaffold)

- Full ISA definition and decode/execute coverage (current v1 is a structural scaffold)
- Full OoO engine (rename/ROB/LSQ/scheduler are skeletal)
- Coherence, SMT, and cache hierarchy implementations
- Full MMU translation and page-walk implementation (scaffold only)

## Am9513

- Decimal floating-point formats
- Correctly-rounded transcendentals (v1 uses deterministic bounded-error approximations)
- Exception trapping/masking beyond sticky-flag model
- Larger or more advanced CAI engines (v1 is single-outstanding/bounded)

## 8096 / 8097

- Full 8086 ISA coverage (beyond the v1 minimum subset)
- Full x87 instruction coverage and extended precision (v1 may simplify internal precision)
- Protected mode, paging, and later x86 tiers (P1–P6 currently trap/not implemented)
- Legacy PC platform/chipset timing emulation (out of scope for core-level functional design)

## Systems

- Real pin-timing RC2014/S-100 physical adapters (stubs exist only)
- Rich peripheral models (UART/SPI/IDE/video), DMA engines, and full interrupt routing policies
- Full firmware/OS loader stacks; boot ROMs are minimal signatures for simulation bring-up
