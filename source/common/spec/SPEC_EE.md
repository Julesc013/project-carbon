# SPEC_EE (v1.0)

Purpose
- Define Execution Environments (EE) that run legacy guests under JC-DOS.
- Guests are sandboxed runtimes, not kernel modes.

Versioning
- EE_ABI version format: major.minor.
- Major mismatch: reject and fail open.
- Minor greater than supported: reject and fail open.
- Minor lower or equal: accept; reserved fields remain reserved.

EE types
- EE_CPM80: CP/M 2.x style 8080/Z80 binaries.
- EE_DOS86: MS-DOS 8086 real-mode binaries.
- GEM/Windows 1/2/3 are application sets under EE_DOS86, not kernels.

Lifecycle
- ee_open(kind): allocate environment and bind to PAL services.
- ee_load(path): load guest program from host FS.
- ee_run(): execute guest until exit or fault.
- ee_close(): release resources; must be idempotent.

Guest/host boundary
- Guests use virtualized console, filesystem, and timer services.
- CP/M BDOS and DOS INT 21h are trapped and mapped to host services.
- Direct hardware access by guests is prohibited.
- BIOS services for DOS guests are virtualized via PAL-derived BDT/CAPSET.

Determinism rules
- Guest execution must be deterministic given identical inputs and host FS.
- Host timing sources must be normalized to PAL ticks.
- Fault injection must be deterministic and transcripted.

Error mapping
- Unsupported EE kind: JC_E_DEV_UNSUPPORTED.
- Invalid or unsupported binary: JC_E_EXEC_BAD_*.
- Unsupported INT/BDOS call: JC_E_EXEC_UNSUPPORTED_TIER or JC_E_DEV_UNSUPPORTED.
- Illegal opcode or fault: JC_E_EXEC_BAD_VERSION (with transcript detail).
