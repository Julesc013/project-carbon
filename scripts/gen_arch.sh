#!/usr/bin/env sh
set -eu

repo_root=$(CDPATH= cd "$(dirname "$0")/.." && pwd)

python_cmd=""
if command -v python3 >/dev/null 2>&1; then
  python_cmd="python3"
elif command -v python >/dev/null 2>&1; then
  python_cmd="python"
else
  echo "ERROR: missing required tool: python (or python3)" >&2
  exit 2
fi

"$python_cmd" "$repo_root/hdl/tools/gen_specs.py" --repo-root "$repo_root"
