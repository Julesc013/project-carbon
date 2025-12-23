#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
OUT_DIR="${OUT_DIR:-$ROOT_DIR/build/os_boot_logs}"
MAX_CYCLES="${MAX_CYCLES:-5000000}"
TARGET_OS="all"

BIN="${CARBON_SIM_BIN:-$ROOT_DIR/build/sim/carbon-sim}"
if [[ ! -x "$BIN" ]]; then
  BIN="carbon-sim"
fi

usage() {
  cat <<EOF
Usage: $(basename "$0") [--os cpm1|cpm22|cpm3|romwbw|all] [--outdir DIR] [--max-cycles N]

Environment variables (per OS):
  CPM1_ROM, CPM1_MEM, CPM1_DISK, CPM1_BSP, CPM1_EXPECT
  CPM22_ROM, CPM22_MEM, CPM22_DISK, CPM22_BSP, CPM22_EXPECT
  CPM3_ROM, CPM3_MEM, CPM3_DISK, CPM3_BSP, CPM3_EXPECT
  ROMWBW_ROM, ROMWBW_MEM, ROMWBW_DISK, ROMWBW_BSP, ROMWBW_EXPECT

Defaults:
  Binaries: \$CARBON_SIM_BIN or build/sim/carbon-sim
  BSP: source/os/common/bsp/CarbonZ80.bsp (CP/M), source/os/romwbw/RomWBW.bsp (RomWBW)
  EXPECT: "A>" for CP/M, "RomWBW" for RomWBW
EOF
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    --os)
      TARGET_OS="$2"
      shift 2
      ;;
    --outdir)
      OUT_DIR="$2"
      shift 2
      ;;
    --max-cycles)
      MAX_CYCLES="$2"
      shift 2
      ;;
    --help|-h)
      usage
      exit 0
      ;;
    *)
      echo "Unknown option: $1" >&2
      usage
      exit 2
      ;;
  esac
done

mkdir -p "$OUT_DIR"

run_case() {
  local name="$1"
  local platform="$2"
  local rom="$3"
  local mem="$4"
  local disk="$5"
  local bsp="$6"
  local expect="$7"

  if [[ -z "$rom" || -z "$disk" || -z "$bsp" ]]; then
    echo "SKIP $name (missing ROM/DISK/BSP)"
    return 0
  fi
  if [[ -n "$mem" && ! -f "$mem" ]]; then
    echo "SKIP $name (mem image missing: $mem)"
    return 0
  fi
  if [[ ! -f "$rom" ]]; then
    echo "SKIP $name (rom missing: $rom)"
    return 0
  fi
  if [[ ! -f "$disk" ]]; then
    echo "SKIP $name (disk missing: $disk)"
    return 0
  fi
  if [[ ! -f "$bsp" ]]; then
    echo "SKIP $name (bsp missing: $bsp)"
    return 0
  fi

  local log="$OUT_DIR/${name}.log"
  local cmd=("$BIN" --platform "$platform" --rom "$rom" --disk0 "$disk" --bsp "$bsp" --max-cycles "$MAX_CYCLES")
  if [[ -n "$mem" ]]; then
    cmd+=(--load "$mem")
  fi

  echo "RUN  $name"
  if ! "${cmd[@]}" >"$log" 2>&1; then
    echo "FAIL $name (sim error, see $log)"
    return 1
  fi
  if [[ -n "$expect" ]] && ! grep -q "$expect" "$log"; then
    echo "FAIL $name (missing banner '$expect', see $log)"
    return 1
  fi
  echo "PASS $name"
  return 0
}

failures=0

if [[ "$TARGET_OS" == "all" || "$TARGET_OS" == "cpm1" ]]; then
  run_case "cpm1" "cpm1" "${CPM1_ROM:-}" "${CPM1_MEM:-}" "${CPM1_DISK:-}" \
    "${CPM1_BSP:-$ROOT_DIR/source/os/common/bsp/CarbonZ80.bsp}" "${CPM1_EXPECT:-A>}" || failures=1
fi

if [[ "$TARGET_OS" == "all" || "$TARGET_OS" == "cpm22" ]]; then
  run_case "cpm22" "cpm22" "${CPM22_ROM:-}" "${CPM22_MEM:-}" "${CPM22_DISK:-}" \
    "${CPM22_BSP:-$ROOT_DIR/source/os/common/bsp/CarbonZ80.bsp}" "${CPM22_EXPECT:-A>}" || failures=1
fi

if [[ "$TARGET_OS" == "all" || "$TARGET_OS" == "cpm3" ]]; then
  run_case "cpm3" "cpm3" "${CPM3_ROM:-}" "${CPM3_MEM:-}" "${CPM3_DISK:-}" \
    "${CPM3_BSP:-$ROOT_DIR/source/os/common/bsp/CarbonZ80.bsp}" "${CPM3_EXPECT:-A>}" || failures=1
fi

if [[ "$TARGET_OS" == "all" || "$TARGET_OS" == "romwbw" ]]; then
  run_case "romwbw" "romwbw" "${ROMWBW_ROM:-}" "${ROMWBW_MEM:-}" "${ROMWBW_DISK:-}" \
    "${ROMWBW_BSP:-$ROOT_DIR/source/os/romwbw/RomWBW.bsp}" "${ROMWBW_EXPECT:-RomWBW}" || failures=1
fi

exit "$failures"
