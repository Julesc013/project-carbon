# GEM Compatibility

Scope
- GEM runs as a DOS application set under `ee_dos86`.
- No kernel or PAL changes are introduced for GEM.

Execution model
- GEM executables run as standard DOS programs.
- BIOS services are virtualized through PAL-derived BDT/CAPSET.
- Direct hardware access is blocked; only DOS/BIOS calls are available.

Requirements
- DOS guest must boot under `ee_dos86`.
- Console output is text-only; no direct framebuffer access.

Limitations
- Protected mode and VxD-style drivers are not supported.
- Timing-sensitive demos may require deterministic PAL ticks.
