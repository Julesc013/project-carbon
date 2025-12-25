# SPEC_PAL (v1.0)

Purpose
- Define the Platform Adapter Layer (PAL) ABI and required services.
- Make JC-DOS boot and run unchanged across Carbon-native and legacy hosts.

Versioning
- PAL_ABI version format: major.minor.
- Major mismatch: reject and fail boot.
- Minor greater than supported: reject and fail boot.
- Minor lower or equal: accept; reserved fields remain reserved.

PAL boundary
- JC-DOS core must not know how it was booted.
- PAL is the only layer that can depend on platform-specific boot details.
- PAL produces the canonical BDT and CAPSET for the platform.

Required services
All PALs must provide the following services via vtables in jc_pal_desc.

Console (VT100/text)
- write: emit UTF-8 bytes as VT100 text; must be deterministic.
- read: blocking read into buffer; may return JC_E_DEV_UNSUPPORTED if not wired.
- flush: optional; if provided, must drain output deterministically.

Block device
- read/write: LBA-based, 512-byte sector units.
- get_params: returns sector size, max sectors per op, total sectors, timeout ticks.
- write may return JC_E_DEV_UNSUPPORTED for read-only media.

Timer/ticks
- ticks: monotonic tick counter, stable frequency.
- tick_hz: tick frequency in Hz; must be non-zero.
- ticks must be deterministic with respect to PAL input transcript.

Memory map
- get_table: returns pointer to a JC_MEM_REGION_TABLE_V1 (see SPEC_TOPOLOGY).
- Regions classify RAM/ROM/MMIO; attributes are authoritative.

Optional services
- Keyboard: polled or blocking; returns key events with modifiers.
- Local video: platform-local display backends; used only if enabled by caps.
- RTC: returns wall-clock time; must be stubbed in deterministic builds.
- DMA cache sync hooks: sync_for_device/sync_for_cpu for non-coherent DMA.

BDT/CAPSET synthesis
- PAL must synthesize a valid BDT (SPEC_BDT) and CAPSET (SPEC_CAPSET).
- BDT is the internal truth for device discovery.
- CAPSET periph_features[0] must include CAP_HAS_* bits for platform features.

Platform identity
- platform_id: short ASCII ID (e.g., "pal_pcbios").
- platform_version: ASCII string describing PAL/board pack version.

Error mapping
- Unsupported platform or service: JC_E_DEV_UNSUPPORTED.
- Missing required device: JC_E_DEV_NOT_FOUND.
- I/O timeout: JC_E_DEV_IO_TIMEOUT.
- I/O data error: JC_E_DEV_IO_ERROR.
- Invalid BDT/CAPSET: JC_E_BDT_BAD_* or JC_E_DISCOVERY_BAD_*.

Determinism rules
- Identical PAL inputs must produce identical transcripts.
- No ambient sources (wall clock, random, timing jitter) may affect output.
- Optional services must be gated by capabilities + config.
- PAL must not probe or branch on architecture outside its boundary.
