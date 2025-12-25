# Platform Matrix (v2.0 template)

| Target   | BSP name | Profile            | CPU tier | Personality tiers | FPU tier | CAI              | CarbonKIO (UART/TIMER/PIC) | Storage (512B+) | Display          | Notes |
|----------|----------|--------------------|----------|-------------------|----------|------------------|-----------------------------|-----------------|------------------|-------|
| SIM_REF  | sim_ref  | PROFILE_SOC_RETRO  | TBD      | Per CAPSET        | TBD      | Mock (optional)  | Yes                         | IDE/CF PIO      | VT100 baseline   | IRQ optional (caps+config) |
| SIM_REF  | sim_ref  | PROFILE_MCU        | TBD      | Per CAPSET        | TBD      | Off              | Yes                         | Optional        | VT100 baseline   | Minimal shell, cache off    |
| FPGA_REF | fpga_ref | PROFILE_SOC_RETRO  | TBD      | Per CAPSET        | TBD      | TBD              | TBD                         | TBD             | VT100 baseline   | TBD   |
| HW_REF1  | hw_ref1  | PROFILE_SOC_RETRO  | TBD      | Per CAPSET        | TBD      | TBD              | TBD                         | TBD             | VT100 baseline   | TBD   |
