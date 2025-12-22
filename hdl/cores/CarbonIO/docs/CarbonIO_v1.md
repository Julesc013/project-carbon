# CarbonIO v1.0 (Project Carbon)

This document describes the CarbonIO integrated peripheral block in `hdl/cores/CarbonIO/`.

## 1. Dual personality model

CarbonIO exposes two personalities simultaneously:

- **Compatibility personality**: Z80-era style register map via the fabric-attached compat window (`COMPAT_BASE_ADDR + CARBONIO_COMPAT_*`).
- **Turbo personality**: CSR window with extended status, feature words, and queue stubs (`CARBON_CSR_CARBONIO_*`).

Both personalities are deterministic and support polling (IRQs are optional).

## 2. UART console (UART/SIO)

Features:

- Deep RX/TX FIFOs (depths parameterized; defaults in `carbonio_pkg.sv`).
- Overflow sticky bits (`UART_STATUS` RX/TX overflow).
- Optional RX timestamp capture (`UART_CTRL[TS_EN]`, `UART_TS_LO/HI`).
- Watermark-based interrupt hooks (`UART_WATERMARKS`).

Compatibility registers:

- `CARBONIO_COMPAT_UART_DATA_OFF` (read pops RX, write pushes TX)
- `CARBONIO_COMPAT_UART_STATUS_OFF`
- `CARBONIO_COMPAT_UART_CTRL_OFF`
- `CARBONIO_COMPAT_UART_RX_COUNT_OFF`
- `CARBONIO_COMPAT_UART_TX_COUNT_OFF`
- `CARBONIO_COMPAT_UART_WATERMARKS_OFF`
- `CARBONIO_COMPAT_UART_TS_LO_OFF/HI`

Turbo CSRs:

- `CARBON_CSR_CARBONIO_UART_CFG`
- `CARBON_CSR_CARBONIO_UART_STATUS`
- `CARBON_CSR_CARBONIO_UART_RX_COUNT`
- `CARBON_CSR_CARBONIO_UART_TX_COUNT`
- `CARBON_CSR_CARBONIO_UART_RX_RDATA`
- `CARBON_CSR_CARBONIO_UART_TX_WDATA`
- `CARBON_CSR_CARBONIO_UART_WATERMARKS`
- `CARBON_CSR_CARBONIO_UART_TS_LO/HI`

## 3. PIO block

Features:

- Input sampling with edge capture FIFO.
- Output and direction registers.
- Simple glitch filter (`PIO_FILTER_CFG`) and match compare (`PIO_MATCH_CFG`).

Compatibility registers:

- `CARBONIO_COMPAT_PIO_IN_OFF`
- `CARBONIO_COMPAT_PIO_OUT_OFF`
- `CARBONIO_COMPAT_PIO_DIR_OFF`
- `CARBONIO_COMPAT_PIO_EDGE_RDATA_OFF`
- `CARBONIO_COMPAT_PIO_EDGE_COUNT_OFF`
- `CARBONIO_COMPAT_PIO_FILTER_CFG_OFF`
- `CARBONIO_COMPAT_PIO_MATCH_CFG_OFF`

Turbo CSRs:

- `CARBON_CSR_CARBONIO_PIO_IN`
- `CARBON_CSR_CARBONIO_PIO_OUT`
- `CARBON_CSR_CARBONIO_PIO_DIR`
- `CARBON_CSR_CARBONIO_PIO_EDGE_RDATA`
- `CARBON_CSR_CARBONIO_PIO_EDGE_COUNT`
- `CARBON_CSR_CARBONIO_PIO_FILTER_CFG`
- `CARBON_CSR_CARBONIO_PIO_MATCH_CFG`

## 4. Timers and tick

Features:

- 64-bit monotonic tick counter (increments when enabled).
- Two reloadable timers by default (parameterizable).
- Polling completion via per-timer status bits (write-to-clear).

Compatibility registers:

- `CARBONIO_COMPAT_TICK_LO_OFF/HI`
- `CARBONIO_COMPAT_TIMER0_*` and `CARBONIO_COMPAT_TIMER1_*` blocks

Turbo CSRs:

- `CARBON_CSR_CARBONIO_TICK_LO/HI`
- `CARBON_CSR_CARBONIO_TIMER0_*` and `CARBON_CSR_CARBONIO_TIMER1_*` blocks

Timer control semantics (v1):

- `CTRL[0]`: enable
- `CTRL[1]`: auto-reload
- `CTRL[2]`: load `LOAD` into the counter immediately

## 5. IRQ routing

Features:

- Per-source enable, mask, and pending.
- Edge-triggered pulses for UART watermarks, PIO edge/match, and timers.

Compatibility registers:

- `CARBONIO_COMPAT_IRQ_ENABLE_OFF`
- `CARBONIO_COMPAT_IRQ_PENDING_OFF`
- `CARBONIO_COMPAT_IRQ_MASK_OFF`

Turbo CSRs:

- `CARBON_CSR_CARBONIO_IRQ_ENABLE`
- `CARBON_CSR_CARBONIO_IRQ_PENDING`
- `CARBON_CSR_CARBONIO_IRQ_MASK`

## 6. Turbo queue stubs (v1)

CarbonIO v1 exposes standard queue configuration registers but does **not**
implement descriptor processing yet:

- `CARBON_CSR_CARBONIO_QUEUE_*` (submit/comp base + masks + doorbells)

Queue processing is deferred to v2; the CSRs are present for BSP/BDT stability.

## 7. Determinism notes

- FIFO push/pop and timer status are deterministic in both personalities.
- Compatibility mode does not allow turbo-only side effects.
- Polling (`UART_STATUS`, `PIO_EDGE_COUNT`, `TIMERx_STATUS`) is supported without IRQs.
