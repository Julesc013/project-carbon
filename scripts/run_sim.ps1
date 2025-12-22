param(
  [switch]$All,
  [switch]$List,
  [string]$Test,
  [string]$Manifest,
  [switch]$NoGen
)

$ErrorActionPreference = "Stop"

$RepoRoot = (Resolve-Path (Join-Path $PSScriptRoot "..")).Path
if (-not $Manifest -or $Manifest -eq "") {
  $Manifest = (Join-Path $RepoRoot "hdl/sim/tests/regress.yaml")
}

if (-not (Test-Path $Manifest)) {
  throw "Regression manifest not found: $Manifest"
}

if (-not $NoGen) {
  & (Join-Path $RepoRoot "scripts/gen_arch.ps1")
}

function Require-Tool([string]$Name) {
  $cmd = Get-Command $Name -ErrorAction SilentlyContinue
  if (-not $cmd) { return $false }
  return $true
}

$missing = @()
foreach ($t in @("make", "iverilog", "vvp", "python")) {
  if (-not (Require-Tool $t)) { $missing += $t }
}
if ($missing.Count -gt 0) {
  throw ("Missing required tools: " + ($missing -join ", ") + ". See: " + (Join-Path $RepoRoot "hdl/sim/README.md"))
}

$tests = @()
foreach ($line in Get-Content $Manifest) {
  $s = ($line.Split("#")[0]).Trim()
  if ($s.StartsWith("-")) {
    $name = $s.Substring(1).Trim().Trim("'").Trim('"')
    if ($name -ne "") { $tests += $name }
  }
}

if ($List) {
  $tests | ForEach-Object { Write-Output $_ }
  exit 0
}

if (-not $All -and (-not $Test -or $Test -eq "")) {
  $All = $true
}

if ($Test -and $Test -ne "") {
  $tests = @($Test)
}

$logDir = Join-Path $RepoRoot "hdl/sim/build/logs"
New-Item -ItemType Directory -Force -Path $logDir | Out-Null

$pass = 0
$fail = 0
$failed = @()

$simDir = Join-Path $RepoRoot "hdl/sim"
foreach ($t in $tests) {
  Write-Host "=== RUN: $t ==="
  $logPath = Join-Path $logDir ($t + ".log")
  & make -C $simDir $t 2>&1 | Tee-Object -FilePath $logPath | Out-Null
  if ($LASTEXITCODE -eq 0) {
    Write-Host "=== PASS: $t ==="
    $pass++
  } else {
    Write-Host "=== FAIL: $t (see $logPath) ==="
    $fail++
    $failed += $t
  }
}

Write-Host ""
Write-Host ("Summary: pass=" + $pass + " fail=" + $fail)
if ($fail -ne 0) {
  throw ("Failed: " + ($failed -join ", "))
}
