#!/usr/bin/env bash
set -euo pipefail

repo_root=$(CDPATH= cd "$(dirname "$0")/.." && pwd)
spec_manifest="$repo_root/source/common/spec/spec_hashes_v1_0.txt"
genspec="$repo_root/source/tools/host/genspec/genspec"
defs_list="$repo_root/source/common/spec/defs/defs.lst"
autogen_dir="$repo_root/source/common/include"
transcript_cmp="$repo_root/source/tools/host/transcript_cmp/transcript_cmp"

need_cmd() {
  if ! command -v "$1" >/dev/null 2>&1; then
    echo "error: missing required tool: $1" >&2
    exit 2
  fi
}

python_cmd=""
if command -v python3 >/dev/null 2>&1; then
  python_cmd="python3"
elif command -v python >/dev/null 2>&1; then
  python_cmd="python"
else
  echo "error: missing required tool: python (or python3)" >&2
  exit 2
fi

echo "Checking spec hash manifest..."
if [ ! -f "$spec_manifest" ]; then
  echo "error: missing spec manifest $spec_manifest" >&2
  exit 1
fi
"$python_cmd" "$repo_root/scripts/spec_hash.py" --repo-root "$repo_root" \
  --manifest "$spec_manifest"

echo "Checking autogen headers..."
if [ ! -x "$genspec" ]; then
  echo "error: genspec not built ($genspec)" >&2
  exit 1
fi
if [ ! -f "$defs_list" ]; then
  echo "error: defs list missing ($defs_list)" >&2
  exit 1
fi
tmpdir="$(mktemp -d)"
trap 'rm -rf "$tmpdir"' EXIT
"$genspec" --list "$defs_list" --out-dir "$tmpdir"
for f in jc_contracts_autogen.h jc_offsets_autogen.h; do
  if [ ! -f "$autogen_dir/$f" ]; then
    echo "error: missing autogen header $autogen_dir/$f" >&2
    exit 1
  fi
  if ! cmp -s "$tmpdir/$f" "$autogen_dir/$f"; then
    echo "error: autogen header out of date ($f)" >&2
    exit 1
  fi
done

echo "Checking conformance transcripts..."
if [ ! -x "$transcript_cmp" ]; then
  echo "error: transcript_cmp not built ($transcript_cmp)" >&2
  exit 1
fi

check_transcript() {
  local golden="$1"
  local candidate="$2"
  if [ ! -f "$golden" ]; then
    echo "error: missing golden transcript $golden" >&2
    exit 1
  fi
  if [ ! -f "$candidate" ]; then
    echo "error: missing candidate transcript $candidate" >&2
    exit 1
  fi
  "$transcript_cmp" "$golden" "$candidate"
}

check_transcript "$repo_root/source/firmware/JC-BIOS/tests/conformance/v0_1_boot/golden.txt" \
  "$repo_root/build/transcripts/jc_bios_v0_1.txt"
check_transcript "$repo_root/source/firmware/JC-BIOS/tests/conformance/v0_2_monitor/golden.txt" \
  "$repo_root/build/transcripts/jc_bios_v0_2.txt"
check_transcript "$repo_root/source/firmware/JC-BIOS/tests/conformance/v0_3_modeup/golden.txt" \
  "$repo_root/build/transcripts/jc_bios_v0_3.txt"
check_transcript "$repo_root/source/firmware/JC-BIOS/tests/conformance/v0_4_devmodel/golden.txt" \
  "$repo_root/build/transcripts/jc_bios_v0_4.txt"
check_transcript "$repo_root/source/firmware/JC-BIOS/tests/conformance/v0_5_fs_ops/golden.txt" \
  "$repo_root/build/transcripts/jc_bios_v0_5.txt"
check_transcript "$repo_root/source/firmware/JC-BIOS/tests/conformance/v0_6_jcom/golden.txt" \
  "$repo_root/build/transcripts/jc_bios_v0_6.txt"

check_transcript "$repo_root/source/os/JC-DOS/tests/conformance/v0_7_boot/golden.txt" \
  "$repo_root/build/transcripts/jc_dos_v0_7.txt"
check_transcript "$repo_root/source/os/JC-DOS/tests/conformance/v0_8_fileops/golden.txt" \
  "$repo_root/build/transcripts/jc_dos_v0_8.txt"
check_transcript "$repo_root/source/os/JC-DOS/tests/conformance/v0_9_hardening/golden.txt" \
  "$repo_root/build/transcripts/jc_dos_v0_9.txt"
check_transcript "$repo_root/source/os/JC-DOS/tests/conformance/v1_0_release/golden.txt" \
  "$repo_root/build/transcripts/jc_dos_v1_0.txt"

echo "Release gate v1.0 OK."
