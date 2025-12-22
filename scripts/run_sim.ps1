param(
  [switch]$All,
  [switch]$List,
  [string]$Test,
  [string]$Manifest,
  [ValidateSet("all","contract","core","system")]
  [string]$Suite = "all",
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

function Require-Tool([string]$Name) {
  $cmd = Get-Command $Name -ErrorAction SilentlyContinue
  if (-not $cmd) { return $false }
  return $true
}

$pythonCmd = $null
if (Require-Tool "python3") { $pythonCmd = "python3" }
elseif (Require-Tool "python") { $pythonCmd = "python" }
if (-not $pythonCmd) {
  throw ("Missing required tool: python (or python3). See: " + (Join-Path $RepoRoot "hdl/sim/docs/USAGE.md"))
}

if (-not $List) {
  if (-not $NoGen) {
    & (Join-Path $RepoRoot "scripts/gen_arch.ps1")
    $checkPs1 = Join-Path $RepoRoot "scripts/check_consistency.ps1"
    $checkSh = Join-Path $RepoRoot "scripts/check_consistency.sh"
    if (Test-Path $checkPs1) {
      & $checkPs1
    } elseif (Test-Path $checkSh) {
      if (-not (Require-Tool "bash")) {
        throw ("check_consistency.sh exists but bash is not available.")
      }
      & bash $checkSh
    }
  }
}

if ($List -and $Test) {
  throw "--List and --Test are mutually exclusive."
}

$sections = @{
  contract_tests = @()
  core_tests = @()
  system_tests = @()
  placeholder_tests = @()
}
$current = $null
foreach ($line in Get-Content $Manifest) {
  $trimmed = ($line.Split("#")[0]).TrimEnd()
  if (-not $trimmed.Trim()) { continue }
  if ($trimmed -match "^[^\\s].*:$") {
    $current = $trimmed.Trim().TrimEnd(":")
    continue
  }
  if ($trimmed -match "^\\s*-") {
    $name = $trimmed.Trim().Substring(1).Trim()
    $name = $name.Trim("'","`"")
    if ($name -ne "" -and $sections.ContainsKey($current)) {
      $sections[$current] += $name
    }
  }
}

$alias = @{
  all = @("contract_tests","core_tests","system_tests")
  contract = @("contract_tests")
  core = @("core_tests")
  system = @("system_tests")
}

$tests = @()
foreach ($key in $alias[$Suite]) {
  $tests += $sections[$key]
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

$missing = @()
if (-not (Require-Tool "make")) { $missing += "make" }
if ($missing.Count -gt 0) {
  throw ("Missing required tools: " + ($missing -join ", ") + ". See: " + (Join-Path $RepoRoot "hdl/sim/docs/USAGE.md"))
}

$sim = $null
if (Require-Tool "verilator") { $sim = "verilator" }
elseif ((Require-Tool "iverilog") -and (Require-Tool "vvp")) { $sim = "iverilog" }
if (-not $sim) {
  throw ("No supported simulator found (verilator or iverilog+vvp). See: " + (Join-Path $RepoRoot "hdl/sim/docs/USAGE.md"))
}

Write-Host ("Using simulator: " + $sim)

$pass = 0
$fail = 0
$failed = @()

$simDir = Join-Path $RepoRoot "hdl/sim"
foreach ($t in $tests) {
  Write-Host "=== RUN: $t ==="
  $logPath = Join-Path $logDir ($t + ".log")
  if ($sim -eq "verilator") {
    & make -C $simDir ("SIM=" + $sim) $t 2>&1 | Tee-Object -FilePath $logPath | Out-Null
  } else {
    & make -C $simDir $t 2>&1 | Tee-Object -FilePath $logPath | Out-Null
  }
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
