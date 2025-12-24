# KiCad 9 schematics (generated vs manual)

This tree is intentionally split:

- `schem/kicad9/generated/`: always safe to regenerate (owned by the generator)
- `schem/kicad9/manual/`: never touched by the generator (hand edits live here)
- `schem/kicad9/spec/`: mapping specs that drive generation
- `schem/kicad9/libs/`: local symbol libraries (placeholders in v1)

## Regeneration

From repo root:

- PowerShell: `scripts/gen_kicad.ps1`
- POSIX shell: `scripts/gen_kicad.sh`

This only rewrites `schem/kicad9/generated/`.

## Extending the mapping specs

Mapping specs are JSON so `tools/kicadgen/src/kicadgen.py` can parse them using
Python stdlib `json` (no external YAML dependency).

- `schem/kicad9/spec/kicadgen_common.json`: interface port naming, common block sheets, layout defaults
- `schem/kicad9/spec/kicadgen_cores.json`: core-to-sheet mapping (blocks, interfaces, output paths)
- `schem/kicad9/spec/kicadgen_systems.json`: system top schematics (core selection, peripherals, common blocks)

Legacy `.yaml` files remain supported for compatibility, but JSON is the source
of truth.

To add a new chip, add a new entry in `schem/kicad9/spec/kicadgen_cores.json` and
reference it from a new system entry in `schem/kicad9/spec/kicadgen_systems.json`.

Key fields to know:

- `common_sheets` in `kicadgen_common.json` drives the generated common block sheets.
- `peripherals` in `kicadgen_systems.json` instantiates extra core sheets (e.g., CarbonIO).
- `common_blocks` in `kicadgen_systems.json` places shared fabric/clock/power blocks.

## Adding real parts later (74ACT, SRAMs, CPLDs)

v1 intentionally generates *logical* block-level hierarchy.

Recommended refinement workflow:

1. Keep regenerating `generated/` as the “source of truth” for hierarchy and naming.
2. Copy a generated sheet into `manual/` when you start hand-editing it.
3. Replace placeholder blocks with real parts (74xx logic, SRAMs, etc.) and add wiring.
4. Update mapping specs so the top-level hierarchy continues to reflect reality.

## Verifying in KiCad 9

Open any generated top-level schematic under:

- `schem/kicad9/generated/cores/<Core>/<name>.kicad_sch`
- `schem/kicad9/generated/systems/<System>/<name>.kicad_sch`

The placeholder symbol library is `schem/kicad9/libs/carbon_blocks.kicad_sym`.
