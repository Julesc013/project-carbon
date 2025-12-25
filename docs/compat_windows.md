# Windows 1/2/3 Compatibility

Scope
- Windows 1/2/3 run as DOS application sets under `ee_dos86`.
- No kernel mode or PAL extensions are required.

Execution model
- Windows executables run as DOS programs with BIOS INT services virtualized.
- Console output remains text-mode; graphics backends are not exposed.

Requirements
- A DOS guest environment via `ee_dos86`.
- Deterministic PAL ticks for stable scheduling.

Limitations
- Protected-mode Windows 3.x features are not supported.
- No 32-bit VxD or hardware acceleration.
