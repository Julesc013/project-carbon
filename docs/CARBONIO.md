# CarbonIO (v1)

CarbonIO is the standard console + I/O peripheral for Project Carbon systems. It integrates:
- UART console with deep FIFOs and optional RX timestamping.
- PIO block with basic edge capture and match hooks.
- Monotonic tick counter and basic timers.
- IRQ routing (optional; polling always works).

## Discovery / BDT

In BDT, CarbonIO is reported as a UART-class device with feature words indicating:
- RX/TX FIFO depth
- Timer count
- Queue count (0 in v1)

Compatibility access is exposed through the BSP-defined CarbonIO base window.

## Compatibility Usage (BIOS)

Typical BIOS usage in compatibility mode:
- UART console: poll `UART_STATUS` for RX/TX availability; read/write `UART_DATA`.
- Timer: poll `TICK_LO/HI` or per-timer `STATUS` bits.
- IRQs are optional; polling must always work.

## Turbo Usage

Turbo queues are reserved for future UART streaming. v1 uses large FIFOs and deterministic polling.

## Register Map

See `hdl/cores/CarbonIO/docs/CarbonIO_v1.md` for the full register map and bit definitions.
