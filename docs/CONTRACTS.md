# Contracts

Purpose
- Provide a map of ABI/API contracts and their authoritative sources.

Contract sources
- hdl/spec/*.yaml: machine-readable architecture contracts.
- docs/ARCH_CONTRACTS.md: generated summary of HDL contracts.
- source/common/spec/*.md: PAL/EE/BDT and device-class specs.
- source/common/include/*.h: public ABI headers.
- hdl/common/if/*.sv: HDL interface contracts.

Versioning and compatibility
- Versioning policy: docs/contract_versioning.md.
- Spec hash set: source/common/spec/spec_hashes_v1_0.txt.
- Compatibility ladders: docs/COMPAT_LADDERS.md.

Enforcement
- Conformance and transcript rules: source/common/spec/SPEC_CONFORMANCE.md.
- Verification guidance: docs/VERIFICATION.md.
