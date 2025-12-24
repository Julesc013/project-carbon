# Device Model (BDT/BSP)

This document describes the device discovery and addressing discipline for Project Carbon systems.

## BDT + BSP Discipline

- **BDT is authoritative** for device enumeration, addressing, IRQ routing, capabilities, and versioning.
- **BSP owns addresses**: software must not hardcode ports or MMIO windows outside the BSP/BDT.
- BDT is exposed via the discovery table pointer (`discovery_table.bdt_ptr`) and stored in ROM.

## BDT Entry Expectations

- Each device entry includes class ID, instance ID, version, and capability flags.
- At least one of `mmio_base` or `io_port_base` must be non-zero.
- IRQ routing is described via the BDT IRQ routing table (domain + line + flags).
- `irq_route_offset` is a byte offset from the BDT base (header signature `CBDT`).
- Block storage devices must report a logical sector size that supports 512-byte sectors.
- CAI-capable accelerators include CAI queue count and doorbell CSR offset.

## Required Devices by Firmware

The following minimum devices are required for common firmware targets. Additional devices may be present.

### CP/M

- UART console (primary text I/O).
- Timer tick source (system clock).
- Block storage (512-byte logical sector support).

### JC-BIOS

- UART console (boot/debug).
- Timer tick source.
- GPIO/PIO for board straps and status.
- Block storage (512-byte logical sector support).
- PIC/IRQ router if interrupts are enabled.
