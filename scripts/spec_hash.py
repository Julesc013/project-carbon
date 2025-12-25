#!/usr/bin/env python3
import argparse
import hashlib
import pathlib
import sys


def hash_file(path: pathlib.Path) -> str:
    h = hashlib.sha256()
    h.update(path.read_bytes())
    return h.hexdigest()


def list_specs(spec_dir: pathlib.Path):
    specs = sorted(spec_dir.glob("SPEC_*.md"))
    if not specs:
        raise RuntimeError(f"no SPEC_*.md files found in {spec_dir}")
    return specs


def write_manifest(manifest: pathlib.Path, specs):
    lines = [f"{p.name} {hash_file(p)}" for p in specs]
    manifest.write_text("\n".join(lines) + "\n", encoding="utf-8")


def read_manifest(manifest: pathlib.Path):
    data = {}
    for raw in manifest.read_text(encoding="utf-8").splitlines():
        line = raw.strip()
        if not line:
            continue
        parts = line.split()
        if len(parts) != 2:
            raise RuntimeError(f"bad manifest line: {raw}")
        data[parts[0]] = parts[1]
    return data


def check_manifest(manifest: pathlib.Path, specs):
    expected = read_manifest(manifest)
    ok = True
    for p in specs:
        digest = hash_file(p)
        if p.name not in expected:
            print(f"missing in manifest: {p.name}", file=sys.stderr)
            ok = False
            continue
        if expected[p.name] != digest:
            print(f"hash mismatch: {p.name}", file=sys.stderr)
            ok = False
    for name in expected.keys():
        if not any(p.name == name for p in specs):
            print(f"manifest entry without spec: {name}", file=sys.stderr)
            ok = False
    return ok


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo-root", required=True)
    parser.add_argument("--manifest", required=True)
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()

    repo_root = pathlib.Path(args.repo_root)
    spec_dir = repo_root / "source" / "common" / "spec"
    manifest = pathlib.Path(args.manifest)

    specs = list_specs(spec_dir)
    if args.write:
        write_manifest(manifest, specs)
        return 0
    return 0 if check_manifest(manifest, specs) else 1


if __name__ == "__main__":
    raise SystemExit(main())
