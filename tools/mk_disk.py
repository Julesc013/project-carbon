#!/usr/bin/env python3

import argparse
import os
from pathlib import Path


def parse_int(s: str) -> int:
    s = s.strip().lower()
    if s.startswith("0x"):
        return int(s, 16)
    return int(s, 10)


def create_blank(path: Path, size_bytes: int, fill_byte: int) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with open(path, "wb") as f:
        chunk = bytes([fill_byte]) * 4096
        remaining = size_bytes
        while remaining > 0:
            n = min(remaining, len(chunk))
            f.write(chunk[:n])
            remaining -= n


def inject(path: Path, src: Path, offset: int) -> None:
    with open(src, "rb") as fsrc:
        data = fsrc.read()
    with open(path, "r+b") as fdst:
        fdst.seek(offset, os.SEEK_SET)
        fdst.write(data)


def main() -> int:
    ap = argparse.ArgumentParser(description="Create simple raw disk images for carbon-sim.")
    ap.add_argument("--out", required=True, help="Output image path")
    ap.add_argument("--size-bytes", required=True, type=parse_int, help="Image size in bytes (decimal or 0x..)")
    ap.add_argument("--fill", default="0xE5", type=parse_int, help="Fill byte (default 0xE5)")

    ap.add_argument("--inject", default="", help="Optional binary file to write into the image")
    ap.add_argument(
        "--offset",
        default="0",
        type=parse_int,
        help="Byte offset for --inject (default 0). Use --lba and --sector-size as an alternative.",
    )
    ap.add_argument("--lba", default="", help="If set, computes offset = LBA * sector-size")
    ap.add_argument("--sector-size", default="512", type=parse_int, help="Sector size for --lba (default 512)")

    args = ap.parse_args()

    out = Path(args.out)
    size_bytes = int(args.size_bytes)
    fill = int(args.fill) & 0xFF

    if size_bytes < 0:
        raise SystemExit("size must be >= 0")

    create_blank(out, size_bytes, fill)

    if args.inject:
        src = Path(args.inject)
        if not src.exists():
            raise SystemExit(f"inject file not found: {src}")

        offset = int(args.offset)
        if args.lba:
            lba = parse_int(args.lba)
            offset = lba * int(args.sector_size)
        if offset < 0:
            raise SystemExit("offset must be >= 0")

        inject(out, src, offset)

    return 0


if __name__ == "__main__":
    raise SystemExit(main())

