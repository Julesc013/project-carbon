$ErrorActionPreference = "Stop"

$RepoRoot = (Resolve-Path (Join-Path $PSScriptRoot "..")).Path
& python (Join-Path $RepoRoot "hdl/tools/gen_specs.py") --repo-root $RepoRoot

