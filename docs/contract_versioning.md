# Contract Versioning

Purpose
- Define how on-wire and ABI contracts evolve and how versions are validated.

Spec versioning
- Each SPEC_*.md defines a major.minor version.
- `genspec` emits `JC_SPEC_*_MAJOR` and `JC_SPEC_*_MINOR` in
  `source/common/include/jc_contracts_autogen.h`.

On-wire validation rules
- Major mismatch: reject and fail.
- Minor greater than supported: reject and fail.
- Minor lower or equal: accept; reserved fields remain reserved.

Structure validation rules
- Magic values, size fields, and version fields are required in every table header.
- `size_bytes`/`entry_size` fields must match the spec exactly for v1.
- Reserved fields must be zero.

Compatibility constraints
- New fields may only be introduced by consuming reserved space.
- Field order and sizes never change within the same major version.
