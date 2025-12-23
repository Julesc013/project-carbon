$ErrorActionPreference = "Stop"

$RepoRoot = (Resolve-Path (Join-Path $PSScriptRoot "..")).Path
$pythonCmd = $null
if (Get-Command python3 -ErrorAction SilentlyContinue) { $pythonCmd = "python3" }
elseif (Get-Command python -ErrorAction SilentlyContinue) { $pythonCmd = "python" }
if (-not $pythonCmd) {
  throw "Missing required tool: python (or python3)"
}
& $pythonCmd (Join-Path $RepoRoot "tools/gen_bdt.py") --repo-root $RepoRoot
