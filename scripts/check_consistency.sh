#!/usr/bin/env bash
set -euo pipefail

repo_root=$(CDPATH= cd "$(dirname "$0")/.." && pwd)

if ! command -v rg >/dev/null 2>&1; then
  echo "error: ripgrep (rg) is required for consistency checks." >&2
  exit 2
fi

python_cmd=""
if command -v python3 >/dev/null 2>&1; then
  python_cmd="python3"
elif command -v python >/dev/null 2>&1; then
  python_cmd="python"
else
  echo "error: python (or python3) is required for consistency checks." >&2
  exit 2
fi

echo "Running spec generator..."
"$python_cmd" "$repo_root/hdl/tools/gen_specs.py" --repo-root "$repo_root"

pattern="TURBO""_UNLIMITED"
echo "Checking for ${pattern}..."
if rg -n "$pattern" "$repo_root"; then
  echo "error: ${pattern} must not appear in the repository." >&2
  exit 1
fi

echo "Checking required spec files..."
required_specs=(
  "$repo_root/hdl/spec/tiers.yaml"
  "$repo_root/hdl/spec/mode_switch.yaml"
  "$repo_root/hdl/spec/profiles.yaml"
  "$repo_root/hdl/spec/topology.yaml"
  "$repo_root/hdl/spec/bdt.yaml"
  "$repo_root/hdl/spec/memory_attrs.yaml"
  "$repo_root/hdl/spec/external_if.yaml"
  "$repo_root/hdl/spec/interfaces.yaml"
  "$repo_root/hdl/spec/discovery.yaml"
  "$repo_root/hdl/spec/csr_map.yaml"
  "$repo_root/hdl/spec/device_model.yaml"
  "$repo_root/hdl/spec/formats.yaml"
  "$repo_root/hdl/spec/fabric.yaml"
  "$repo_root/hdl/spec/cai.yaml"
  "$repo_root/hdl/spec/isa_z90.yaml"
)
for spec in "${required_specs[@]}"; do
  if [[ ! -f "$spec" ]]; then
    echo "error: missing required spec $spec" >&2
    exit 1
  fi
done

echo "Checking tier ladder tables..."
tiers_file="$repo_root/hdl/spec/tiers.yaml"
for ladder in TIER_LADDER_Z80 TIER_LADDER_AM95; do
  if ! rg -n "$ladder" "$tiers_file" >/dev/null; then
    echo "error: missing $ladder in $tiers_file" >&2
    exit 1
  fi
done

echo "Running KiCad generator..."
"$python_cmd" "$repo_root/tools/kicadgen/src/kicadgen.py"

echo "Checking KiCad schematic outputs..."
required_kicad_files=(
  "$repo_root/schem/kicad9/generated/cores/Z85/Z85.kicad_sch"
  "$repo_root/schem/kicad9/generated/cores/Z90/Z90.kicad_sch"
  "$repo_root/schem/kicad9/generated/cores/Z380/Z380.kicad_sch"
  "$repo_root/schem/kicad9/generated/cores/Z480/Z480.kicad_sch"
  "$repo_root/schem/kicad9/generated/cores/Am9513/Am9513.kicad_sch"
  "$repo_root/schem/kicad9/generated/cores/Am9514/Am9514.kicad_sch"
  "$repo_root/schem/kicad9/generated/cores/Am9515/Am9515.kicad_sch"
  "$repo_root/schem/kicad9/generated/systems/CarbonZ80/CarbonZ80.kicad_sch"
  "$repo_root/schem/kicad9/generated/systems/CarbonZ90/CarbonZ90.kicad_sch"
  "$repo_root/schem/kicad9/generated/systems/CarbonZ380/CarbonZ380.kicad_sch"
  "$repo_root/schem/kicad9/generated/systems/CarbonZ480/CarbonZ480.kicad_sch"
)
for f in "${required_kicad_files[@]}"; do
  if [[ ! -f "$f" ]]; then
    echo "error: missing generated schematic $f" >&2
    exit 1
  fi
done

echo "Checking KiCad schematics for stale eZ90 naming..."
if rg -n "eZ90" "$repo_root/schem/kicad9" >/dev/null; then
  echo "error: stale eZ90 naming found in schematics." >&2
  exit 1
fi

echo "Checking KiCad generator determinism..."
hash_a=$("$python_cmd" - "$repo_root/schem/kicad9/generated" <<'PY'
import hashlib
import pathlib
import sys

root = pathlib.Path(sys.argv[1])
hasher = hashlib.sha256()
for path in sorted(root.rglob("*.kicad_sch")):
    rel = path.relative_to(root).as_posix()
    hasher.update(rel.encode("utf-8"))
    hasher.update(b"\0")
    hasher.update(path.read_bytes())
    hasher.update(b"\0")
print(hasher.hexdigest())
PY
)
"$python_cmd" "$repo_root/tools/kicadgen/src/kicadgen.py"
hash_b=$("$python_cmd" - "$repo_root/schem/kicad9/generated" <<'PY'
import hashlib
import pathlib
import sys

root = pathlib.Path(sys.argv[1])
hasher = hashlib.sha256()
for path in sorted(root.rglob("*.kicad_sch")):
    rel = path.relative_to(root).as_posix()
    hasher.update(rel.encode("utf-8"))
    hasher.update(b"\0")
    hasher.update(path.read_bytes())
    hasher.update(b"\0")
print(hasher.hexdigest())
PY
)
if [[ "$hash_a" != "$hash_b" ]]; then
  echo "error: KiCad generation is not deterministic (hash mismatch)." >&2
  exit 1
fi

echo "Consistency checks passed."
