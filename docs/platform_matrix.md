# Platform Matrix

| Target | PAL | BSP/Pack | Profile | CPU tier | FPU tier | CarbonKIO (UART/TIMER/PIC) | Storage (512B+) | Notes |
|---|---|---|---|---|---|---|---|---|
| SIM_REF | pal_carbon | sim_ref | PROFILE_SOC_RETRO | unknown | unknown | unknown | unknown | JC-BIOS discovery-based. |
| FPGA_REF | pal_carbon | fpga_ref | PROFILE_SOC_RETRO | unknown | unknown | unknown | unknown | JC-BIOS discovery-based. |
| HW_REF1 | pal_carbon | hw_ref1 | PROFILE_SOC_RETRO | unknown | unknown | unknown | unknown | JC-BIOS discovery-based. |
| RC2014 | pal_z80_static | board_pack rc2014 | PROFILE_SOC_RETRO | P2 (Z80) | none | UART+TIMER | 512B (stub) | Static pack, no probing. |
| S-100 | pal_z80_static | board_pack s100_ref | PROFILE_SOC_RETRO | P2 (Z80) | none | UART+TIMER+PIC | 512B (stub) | CAP_HAS_IRQ set. |
| Generic Z80 | pal_z80_static | board_pack generic_z80 | PROFILE_SOC_RETRO | P1 (Z80) | none | UART | 512B (stub) | Minimal pack. |
| ROMWBW | pal_romwbw | ROMWBW hooks | PROFILE_SOC_RETRO | Z80 class | none | ROMWBW KIO | ROMWBW disk | Requires ROMWBW hook table. |
| PC BIOS | pal_pcbios | BIOS hooks | unknown | x86 real mode | none | BIOS console/timer | BIOS INT 13h | Virtual BDT. |
| UEFI | pal_uefi | stub | n/a | n/a | n/a | n/a | n/a | Returns unsupported. |
