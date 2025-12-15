# HDL (Architecture Spec Layer)

This directory contains the Project Carbon architecture contract layer.

- `hdl/spec/`: frozen v1.0 machine-readable YAML specs
- `hdl/tools/gen_specs.py`: deterministic generator (no external dependencies)
- `hdl/gen/`: generated SystemVerilog + C constants (committed)
- `hdl/common/`: shared HDL utilities (non-generated; reserved for later)

## Regenerating

- PowerShell: `.\scripts\gen_arch.ps1`
- POSIX shell: `./scripts/gen_arch.sh`
- Direct: `python hdl/tools/gen_specs.py`

Generated outputs:

- `hdl/gen/carbon_arch_pkg.sv`
- `hdl/gen/carbon_arch.h`
- `docs/ARCH_CONTRACTS.md`

Do not hand-edit files under `hdl/gen/`.
