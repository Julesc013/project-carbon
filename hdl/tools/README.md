# hdl/tools

This directory contains tooling for the Project Carbon HDL tree.

- `gen_specs.py`: reads `hdl/spec/*.yaml` and generates:
  - `hdl/gen/carbon_arch_pkg.sv`
  - `hdl/gen/carbon_arch.h`
  - `docs/ARCH_CONTRACTS.md`

The generator is deterministic and uses no third-party dependencies.
