# Dependency Rules

Purpose
- Document allowed and forbidden dependency directions across layers.

Scope
- Firmware, OS, PAL, EE, common, HDL, and tools.

Allowed dependencies
- source/common is the shared contract and utility layer for firmware/OS/PAL/EE.
- JC-BIOS and JC-DOS may depend on source/common and generated contract headers.
- PAL implementations may depend on source/common and platform board packs.
- EE providers may depend on JC-DOS services and source/common, not platform details.
- HDL implementations depend on hdl/spec and hdl/gen artifacts.

Forbidden dependencies
- BIOS/OS/EE must not depend directly on platform board packs or PAL internals.
- PAL must not depend on guest EE implementations.
- HDL contract specs must not depend on implementation RTL or tests.
- Tools and scripts must not be linked into firmware/OS runtime images.

Canonical reference
- source/common/spec/JC0_DEPENDENCIES.md
