#!/usr/bin/env sh
set -eu

repo_root=$(CDPATH= cd "$(dirname "$0")/.." && pwd)
manifest="$repo_root/hdl/sim/tests/regress.yaml"
no_gen=0
do_all=0
do_list=0
test_name=""
suite="all"

usage() {
  cat <<EOF
Usage:
  scripts/run_sim.sh --all [--no-gen] [--manifest <path>]
  scripts/run_sim.sh --test <tb_target> [--no-gen]
  scripts/run_sim.sh --list [--manifest <path>] [--suite <contract|core|system|all>]
  scripts/run_sim.sh --all --suite <contract|core|system>

Notes:
  - Test names are Make targets under hdl/sim (e.g. tb_carbonz80).
  - Logs are written to hdl/sim/build/logs/.
EOF
}

while [ $# -gt 0 ]; do
  case "$1" in
    --all) do_all=1 ;;
    --list) do_list=1 ;;
    --test)
      shift
      test_name="${1:-}"
      ;;
    --suite)
      shift
      suite="${1:-}"
      ;;
    --manifest)
      shift
      manifest="${1:-}"
      ;;
    --no-gen) no_gen=1 ;;
    -h|--help) usage; exit 0 ;;
    *)
      echo "ERROR: unknown argument: $1" >&2
      usage
      exit 2
      ;;
  esac
  shift
done

if [ "$do_all" -eq 0 ] && [ "$do_list" -eq 0 ] && [ -z "$test_name" ]; then
  do_all=1
fi

if [ ! -f "$manifest" ]; then
  echo "ERROR: regression manifest not found: $manifest" >&2
  exit 2
fi

case "$suite" in
  all|contract|core|system) ;;
  *)
    echo "ERROR: unknown suite: $suite" >&2
    exit 2
    ;;
esac

need_cmd() {
  if ! command -v "$1" >/dev/null 2>&1; then
    echo "missing:$1"
    return 1
  fi
  return 0
}

python_cmd=""
if command -v python3 >/dev/null 2>&1; then
  python_cmd="python3"
elif command -v python >/dev/null 2>&1; then
  python_cmd="python"
fi

if [ -z "$python_cmd" ]; then
  echo "ERROR: missing required tool: python (or python3)" >&2
  echo "See: $repo_root/hdl/sim/docs/USAGE.md" >&2
  exit 2
fi

if [ "$do_list" -eq 0 ]; then
  if [ "$no_gen" -eq 0 ]; then
    "$repo_root/scripts/gen_arch.sh"
    if [ -f "$repo_root/scripts/check_consistency.sh" ]; then
      "$repo_root/scripts/check_consistency.sh"
    fi
  fi
fi

if [ "$do_list" -eq 1 ] && [ -n "$test_name" ]; then
  echo "ERROR: --list and --test are mutually exclusive." >&2
  exit 2
fi

if [ "$do_list" -eq 1 ]; then
  tests=$(
    "$python_cmd" - "$manifest" "$suite" <<'PY'
import sys
path = sys.argv[1]
suite = sys.argv[2] if len(sys.argv) > 2 else "all"
sections = {"contract_tests": [], "core_tests": [], "system_tests": [], "placeholder_tests": []}
current = None
for raw in open(path, "r", encoding="utf-8"):
    line = raw.split("#", 1)[0].rstrip()
    if not line.strip():
        continue
    if line.lstrip() == line:
        if line.strip().endswith(":"):
            current = line.strip().split(":", 1)[0].strip()
        else:
            current = None
        continue
    item = line.strip()
    if not item.startswith("-"):
        continue
    name = item[1:].strip().strip("\"'")
    if current in sections and name:
        sections[current].append(name)
alias = {
    "all": ["contract_tests", "core_tests", "system_tests"],
    "contract": ["contract_tests"],
    "core": ["core_tests"],
    "system": ["system_tests"],
}
if suite not in alias:
    sys.stderr.write("ERROR: unknown suite: %s\n" % suite)
    sys.exit(2)
tests = []
for key in alias[suite]:
    tests.extend(sections.get(key, []))
for t in tests:
    print(t)
PY
  )
  printf "%s\n" "$tests"
  exit 0
fi

if [ -n "$test_name" ]; then
  tests="$test_name"
else
  tests=$(
    "$python_cmd" - "$manifest" "$suite" <<'PY'
import sys
path = sys.argv[1]
suite = sys.argv[2] if len(sys.argv) > 2 else "all"
sections = {"contract_tests": [], "core_tests": [], "system_tests": [], "placeholder_tests": []}
current = None
for raw in open(path, "r", encoding="utf-8"):
    line = raw.split("#", 1)[0].rstrip()
    if not line.strip():
        continue
    if line.lstrip() == line:
        if line.strip().endswith(":"):
            current = line.strip().split(":", 1)[0].strip()
        else:
            current = None
        continue
    item = line.strip()
    if not item.startswith("-"):
        continue
    name = item[1:].strip().strip("\"'")
    if current in sections and name:
        sections[current].append(name)
alias = {
    "all": ["contract_tests", "core_tests", "system_tests"],
    "contract": ["contract_tests"],
    "core": ["core_tests"],
    "system": ["system_tests"],
}
if suite not in alias:
    sys.stderr.write("ERROR: unknown suite: %s\n" % suite)
    sys.exit(2)
tests = []
for key in alias[suite]:
    tests.extend(sections.get(key, []))
for t in tests:
    print(t)
PY
  )
fi

logdir="$repo_root/hdl/sim/build/logs"
mkdir -p "$logdir"

if ! need_cmd make >/dev/null 2>&1; then
  echo "ERROR: missing required tool: make" >&2
  echo "See: $repo_root/hdl/sim/docs/USAGE.md" >&2
  exit 2
fi

sim=""
if command -v verilator >/dev/null 2>&1; then
  sim="verilator"
elif command -v iverilog >/dev/null 2>&1 && command -v vvp >/dev/null 2>&1; then
  sim="iverilog"
else
  echo "ERROR: no supported simulator found (verilator or iverilog+vvp)." >&2
  echo "See: $repo_root/hdl/sim/docs/USAGE.md" >&2
  exit 2
fi

sim_arg=""
if [ "$sim" = "verilator" ]; then
  sim_arg="SIM=verilator"
fi

echo "Using simulator: $sim"

pass=0
fail=0
failed=""

for t in $tests; do
  echo "=== RUN: $t ==="
  log="$logdir/$t.log"
  if make -C "$repo_root/hdl/sim" $sim_arg "$t" >"$log" 2>&1; then
    echo "=== PASS: $t ==="
    pass=$((pass + 1))
  else
    echo "=== FAIL: $t (see $log) ===" >&2
    fail=$((fail + 1))
    failed="$failed $t"
  fi
done

echo ""
echo "Summary: pass=$pass fail=$fail"
if [ "$fail" -ne 0 ]; then
  echo "Failed:$failed" >&2
  exit 1
fi
