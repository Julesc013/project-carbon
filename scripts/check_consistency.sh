#!/usr/bin/env bash
set -euo pipefail

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
"$python_cmd" hdl/tools/gen_specs.py

echo "Checking for TURBO_UNLIMITED..."
if rg -n "TURBO_UNLIMITED" .; then
  echo "error: TURBO_UNLIMITED must not appear in the repository." >&2
  exit 1
fi

echo "Checking tier ladder tables..."
tiers_file="hdl/spec/tiers.yaml"
if [[ ! -f "$tiers_file" ]]; then
  echo "error: missing $tiers_file" >&2
  exit 1
fi
for ladder in TIER_LADDER_Z80 TIER_LADDER_X86 TIER_LADDER_AMD_FPU; do
  if ! rg -n "$ladder" "$tiers_file" >/dev/null; then
    echo "error: missing $ladder in $tiers_file" >&2
    exit 1
  fi
done

echo "Consistency checks passed."
