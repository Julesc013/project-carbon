# JC-DOS Architecture (v2.0)

Purpose
- Describe the v1.4 DOS structure, BIOS handoff, and contract dependencies.

Boot and handoff
- BIOS loads `JCDOS.JCO` and calls `jc_dos_entry` with `jc_dos_handoff_v1`.
- Handoff contains pointers to CAPSET, BDT, and BIOS services, plus TPA base/size.
- DOS validates handoff signature, version, and size before use.

BIOS services
- DOS uses `jc_bios_services_v1` for console, block I/O, timer ticks, and reboot.
- DOS core never touches MMIO or I/O bases directly.

Memory model
- Fixed bump arenas: kernel, fs, and shell.
- TPA is provided by BIOS and used for JCOM loads.

Components and configuration
- Optional modules are registered via the component manifest (`jc_component`).
- Defaults preserve v1.0 behavior (cache/fastmem/CAI/FPU off unless enabled).
- Profile policy (`jc_profile`) declares required devices, optional devices, and
  allowed subsystems. MCU profile enforces minimal shell and optional storage.

Performance (v1.1)
- Read-through/write-through block cache (fixed arena, deterministic eviction).
- Fastmem uses capability-led selection; semantics match baseline C loops.

Acceleration (v1.2)
- CAI runtime is optional; mock CAI used for SIM_REF when enabled.
- Am95xx FPU routing selects CAI backend when present, otherwise soft fallback.

Display (v1.3)
- `jc_display` provides a text-mode abstraction with VT100 as default backend.
- Optional local display backends are BDT-bound and stubbed unless validated.
- Shadow buffer hashing is used for local-display conformance when enabled.
- Local probes search for `DEVCLASS_PIO` entries with display subclass IDs in
  `source/common/include/jc_display.h`.

Personalities (v1.4)
- `jc_personality_session` provides tier-specific execution without forking DOS.
- `jc_personality_open/exec/close` enforce shared vs isolated resources.
- Mode stack and tier transitions are managed internally and reported via errors.
- Shared: console, block storage, filesystem, timer; isolated: regs/stack/address.

Filesystem
- CPMX per `SPEC_FS_CPMX`.
- Filenames are 8.3 uppercase, space padded.

Shell
- Commands: DIR, TYPE, COPY, DEL, REN, RUN.
- RUN supports `/P2`, `/P3`, and `/NATIVE` to force a personality.
- DIR pattern matching: exact match or a single trailing `*` for prefix match.
  `*` alone matches all entries.

Execution
- JCOM loader per `SPEC_JCOM` with CRC32 validation and min-tier check.
- Return code is propagated back to the shell.

Conformance
- DOS emits stable transcripts for v0.7 through v1.4 using LF line endings only.
- v1.1: perf cache/fastmem checks; v1.2: CAI/FPU checks; v1.3: display checks;
  v1.4: personality session checks.
