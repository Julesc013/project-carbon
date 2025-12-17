#!/usr/bin/env sh
set -eu

repo_root=$(CDPATH= cd "$(dirname "$0")/.." && pwd)
manifest="$repo_root/hdl/sim/tests/regress.yaml"
no_gen=0
do_all=0
do_list=0
test_name=""

usage() {
  cat <<EOF
Usage:
  scripts/run_sim.sh --all [--no-gen] [--manifest <path>]
  scripts/run_sim.sh --test <tb_target> [--no-gen]
  scripts/run_sim.sh --list [--manifest <path>]

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

if [ "$no_gen" -eq 0 ]; then
  "$repo_root/scripts/gen_arch.sh"
fi

need_cmd() {
  if ! command -v "$1" >/dev/null 2>&1; then
    echo "missing:$1"
    return 1
  fi
  return 0
}

missing=""
for c in make iverilog vvp python3; do
  if ! need_cmd "$c" >/dev/null 2>&1; then
    missing="${missing} $c"
  fi
done

if [ -n "$missing" ]; then
  echo "ERROR: missing required tools:${missing}" >&2
  echo "See: $repo_root/hdl/sim/README.md" >&2
  exit 2
fi

tests=$(
  python3 - <<PY "$manifest"
import sys
path=sys.argv[1]
out=[]
for line in open(path,"r",encoding="utf-8"):
  line=line.split("#",1)[0].rstrip()
  s=line.strip()
  if s.startswith("-"):
    name=s[1:].strip().strip("\"'").strip()
    if name:
      out.append(name)
for t in out:
  print(t)
PY
)

if [ "$do_list" -eq 1 ]; then
  printf "%s\n" "$tests"
  exit 0
fi

if [ -n "$test_name" ]; then
  tests="$test_name"
fi

logdir="$repo_root/hdl/sim/build/logs"
mkdir -p "$logdir"

pass=0
fail=0
failed=""

for t in $tests; do
  echo "=== RUN: $t ==="
  log="$logdir/$t.log"
  if make -C "$repo_root/hdl/sim" "$t" >"$log" 2>&1; then
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

