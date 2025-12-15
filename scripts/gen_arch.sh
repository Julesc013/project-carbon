#!/usr/bin/env sh
set -eu

repo_root=$(CDPATH= cd "$(dirname "$0")/.." && pwd)
python3 "$repo_root/hdl/tools/gen_specs.py" --repo-root "$repo_root"

