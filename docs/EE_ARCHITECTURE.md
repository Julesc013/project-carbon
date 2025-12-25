# EE Architecture

Purpose
- Execute legacy guests under JC-DOS as sandboxed environments.
- Keep guest ABIs isolated from kernel mode and PAL internals.

ABI surface
- `source/common/include/jc_ee.h` defines `jc_ee` and EE kinds.
- `source/common/util/jc_ee.c` dispatches to providers by kind.
- ABI version is `JC_EE_ABI_MAJOR`/`JC_EE_ABI_MINOR`.

Lifecycle
- `ee_open(kind)` binds a provider and allocates state.
- `ee_load(path)` loads a guest program from host storage.
- `ee_run()` executes until exit or fault.
- `ee_close()` releases state (idempotent).

Providers
- `source/runtime/ee_cpm80/`: CP/M 2.x style guests.
- `source/runtime/ee_dos86/`: MS-DOS real-mode guests.
- Both providers are deterministic stubs with fault-injection paths:
  - `NEG_UNSUPPORTED` returns `JC_E_DEV_UNSUPPORTED`.
  - `NEG_ILLEGAL` returns `JC_E_EXEC_BAD_VERSION`.
- Each provider exports `JC_COMPONENT_DESC` for dependency metadata.

Host/guest boundary
- Guests use virtualized console and filesystem services.
- Direct hardware access is not permitted; PAL is the only hardware boundary.

Determinism
- EE output is deterministic given identical inputs and host storage.
- Fault injection is deterministic and transcripted.
