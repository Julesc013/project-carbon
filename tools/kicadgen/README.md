# kicadgen (KiCad 9 schematic generator)

`kicadgen` generates KiCad 9 hierarchical schematic skeletons under `schem/kicad9/generated/` from data-driven mapping specs in `schem/kicad9/spec/`.

Notes:
- Mapping files are JSON (`schem/kicad9/spec/kicadgen_*.json`) so the generator can use Python stdlib `json` without external YAML dependencies.
- `generated/` is safe to overwrite during regeneration.
- `manual/` is intentionally untouched by the generator.

Entrypoint: `tools/kicadgen/src/kicadgen.py`
