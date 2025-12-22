# Carbon Devices Overview (v1)

This overview summarizes the device discovery model, register conventions, and the current v1 device set.

## Discovery and Capability Descriptors

Devices are enumerated through the Board Device Table (BDT). Each entry is a fixed-size
Device Capability Descriptor (v1):
- Class/subclass identifiers (CPU, UART, DMA, etc).
- Compatibility and turbo feature flags.
- Standard feature words (FIFO depth, DMA channels, timer count, queue count).
- Compatibility base addresses (I/O or MMIO), CSR base, and MMIO window size.

The BDT base and format are discoverable via CPUID/CAPS leaf `DEVICE_TABLE`.

## Compatibility Register Conventions

- Compatibility windows are BSP-defined (no hardcoded ports outside BSP).
- Registers are 32-bit aligned; byte writes are supported for 8-bit software.
- Compatibility accesses must be ordered and deterministic.
- Polling must always work; interrupts are optional.

## Turbo Queue Conventions

Turbo devices use the standard ring format:
- Submission descriptors are 32 bytes (`TURBO_SUBMIT_DESC_V1`).
- Completions are 16 bytes (`TURBO_COMP_REC_V1`).
- Doorbells notify the device; completion records can be polled.

## Current v1 Devices

- CarbonIO: UART console + PIO + timers + IRQ router.
- CarbonDMA: multi-channel DMA engine with compat and queue modes.
- Am9513 and other accelerators (see `docs/ARCH_CONTRACTS.md`).

## Extending the Device Set

1. Assign a device class/subclass and capability descriptor fields.
2. Implement compatibility + turbo personalities with polling completion.
3. Add CSR blocks and queue layouts per the common contracts.
4. Add BDT entries and update tests.
