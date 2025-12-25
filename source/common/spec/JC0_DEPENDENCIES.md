# Project Carbon JC0 Dependencies Pack (Freeze List)

This document enumerates the contract items that must be frozen in JC0.

## D1) Endianness, alignment, and "wire format" rule

- All discovery + BDT + topology structures are encoded in a single declared
  byte order (recommended: little-endian).
- All "on-wire" structs are packed by explicit field sizes; runtime code must
  not rely on compiler packing.
- Alignment guarantees must be stated (e.g., 4-byte aligned pointers).

## D2) Discovery mechanism (how ROM finds discovery)

Freeze one deterministic method for v1:

- Fixed address contains a pointer to the Discovery Block, OR
- Fixed MMIO registers provide pointers, OR
- Signature scan (not recommended for v1)

JC0 must select and freeze one, including exact addresses/registers as BSP
data.

## D3) MODE ABI (MODEUP/RETMD calling convention)

Freeze:

- preserved registers (per tier)
- stack alignment rules
- interrupt mask/state rules during transition
- failure return convention
- "ABI capsule" mechanism: pass a pointer to a fixed struct that carries
  args/results/errors so C signatures do not fragment per tier

## D4) CAPSET normalized schema

Define a single normalized JC_CAPSET produced by BIOS from raw discovery:

- cpu tier + cpu feature bitmap
- fpu tier + fpu interface flags (legacy window vs CAI)
- profile id
- pointers to topology + bdt (as physical addresses or abstract handles)
- limits (max devices, max dma segments, etc.)

## D5) Topology table schema (even minimal)

Freeze minimal layout:

- CPU cores and which tiers they host
- memory regions (RAM/ROM/MMIO) with attributes
- optional: cache coherency domains (for DMA / future)

## D6) BDT binary layout (header + entry layout + versioning)

Freeze:

- magic, major/minor, total size, entry count, checksum/hash
- entry header: class, instance, flags (MMIO vs I/O), base, span, irq routing,
  caps bitmap, class-version, aux pointer/offset
- limits: max entries, max size, alignment requirements

## D7) IRQ routing encoding

Freeze whether IRQ routing is expressed as:

- PIC input line number
- vector number
- both

Also define the optional ACK/EOI protocol if IRQ mode is enabled.

## D8) CarbonKIO device-class ABI (UART/TIMER/PIC/GPIO)

Freeze register-level semantics as class ABI, not per-board:

UART:

- data reg, status reg bits, optional FIFO depth report
- blocking vs nonblocking read/write rules

TIMER:

- monotonic tick counter
- tick frequency publication
- wrap behavior

PIC:

- polling read method always valid
- optional enable/disable/ack if IRQ supported

## D9) CarbonStorage IDE/CF PIO ABI (minimum command subset)

Freeze:

- required task file registers mapping
- required commands: IDENTIFY, READ SECTOR(S), WRITE SECTOR(S)
- init/reset sequence
- error reporting bits
- timeout rules (tick-based)

## D10) CAI ABI (reserved even if deferred in v1)

Freeze:

- descriptor ring layout (producer/consumer indices)
- doorbell mechanism
- completion ring layout
- tag space + completion ordering rules
- memory ordering requirements for DMA visibility (non-coherent baseline)

## D11) Filesystem v1 decision (must be final in JC0)

Freeze:

- FS type: CP/M-like extent FS (or alternative if you choose)
- naming rules
- directory layout
- allocation unit size
- no timestamps in v1 (recommended)

## D12) Program format v1 (JCOM) and exit convention

Freeze:

- header fields (min tier, load policy, entry offset, bss size, crc)
- optional TLV extension area rules
- exit convention (where return code is stored)
- standard I/O model in v1 (console only recommended)

## D13) Conformance transcript format (parity gate)

Freeze:

- stable header lines (contract versions + capset hash + bdt hash)
- strict PASS/FAIL line format
- final CRC over transcript bytes
- allowed-diff policy must be explicit (ideally none for v1 reference targets)

## V1 reference target policy (must be set in JC0)

JC0 must select and freeze:

- SIM_REF identity and BSP name
- FPGA_REF identity and BSP name
- HW_REF1 identity and BSP name

All must be PROFILE_SOC_RETRO for v1, with CarbonKIO + one 512B block storage
path.
