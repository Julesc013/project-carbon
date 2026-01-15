# Style and Documentation Standards

Purpose
- Define coding and documentation standards for Project Carbon artifacts.

Language constraints
- Firmware/OS/PAL/EE: ISO C89/C90, freestanding, no external runtime deps.
- C++ components: C++98 unless a component doc explicitly states otherwise.
- Assembly only for reset, traps, and tier transitions.
- HDL: Verilog/SystemVerilog/VHDL as present in hdl/.

File-level header blocks
Use structured headers at the top of every non-trivial file.

C/C++/Assembly
```c
/*
 * FILE:
 * MODULE:
 * LAYER / SUBSYSTEM:
 * RESPONSIBILITY:
 *   - What this file explicitly owns
 *   - What it explicitly does NOT do
 * ALLOWED DEPENDENCIES:
 * FORBIDDEN DEPENDENCIES:
 * EXECUTION CONTEXT:
 *   - BIOS / DOS / PAL / EE / Tool / Firmware
 * THREADING / REENTRANCY:
 * ERROR MODEL:
 * DETERMINISM GUARANTEES:
 * ABI / BINARY / WIRE FORMAT NOTES:
 * HARDWARE ASSUMPTIONS (if any):
 * EXTENSION POINTS:
 */
```

HDL
```verilog
// FILE:
// MODULE:
// SUBSYSTEM:
// RESPONSIBILITY:
// CLOCKING MODEL:
// RESET BEHAVIOR:
// SIGNAL OWNERSHIP:
// TIMING / ORDERING ASSUMPTIONS:
// CONFIGURATION / GENERICS:
// EXTENSION POINTS:
```

Public headers are contracts
- Public functions, structs, enums, typedefs, and semantic macros require
  doc blocks describing purpose, parameters, return values, preconditions,
  side effects, determinism, and ABI constraints (as applicable).
- Source files must not duplicate public header documentation.

Inline comments
- Use inline comments only for non-obvious invariants, ordering constraints,
  or hardware quirks that would be unsafe to omit.
- Avoid narrating control flow.
