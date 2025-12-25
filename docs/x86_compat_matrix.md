# x86 Compatibility Matrix

| Mode/Bitness | PAL/EE Coverage | Notes |
|---|---|---|
| 16-bit real mode | `pal_pcbios` + BIOS boot stages | Requires BIOS INT hooks. |
| 32-bit protected/V86 | `ee_dos86` (V86 backend stub) | Requires CAP_HAS_V86. |
| 64-bit | `ee_dos86` (soft real-mode stub) | No direct PAL; guests are emulated. |
