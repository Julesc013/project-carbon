#!/usr/bin/env python3
"""
mk_os_image.py

Build a flat memory image by placing binary segments at fixed addresses.
This is used to compose CP/M and RomWBW boot images without shipping
copyrighted binaries.
"""

from __future__ import annotations

import argparse
import sys
from pathlib import Path
from typing import List, Tuple


class ImageError(Exception):
    pass


def parse_addr(text: str) -> int:
    text = text.strip()
    if text.lower().startswith("0x"):
        return int(text, 16)
    return int(text, 10)


def parse_segment(spec: str) -> Tuple[Path, int]:
    if "@" not in spec:
        raise ImageError(f"segment '{spec}' must be PATH@ADDR")
    path_text, addr_text = spec.split("@", 1)
    path = Path(path_text)
    addr = parse_addr(addr_text)
    return path, addr


def write_segment(image: bytearray, base: int, data: bytes, name: str) -> None:
    end = base + len(data)
    if base < 0 or end > len(image):
        raise ImageError(f"{name} does not fit in image (0x{base:04X}..0x{end - 1:04X})")
    image[base:end] = data


def main(argv: List[str]) -> int:
    parser = argparse.ArgumentParser(description="Build a flat memory image from segments.")
    parser.add_argument("--size", type=parse_addr, default=65536, help="Image size in bytes.")
    parser.add_argument("--fill", type=parse_addr, default=0x00, help="Fill byte value.")
    parser.add_argument("--segment", action="append", default=[], help="Segment PATH@ADDR.")
    parser.add_argument("--bsp", action="append", default=[], help="BSP blob PATH@ADDR.")
    parser.add_argument("--entry", type=parse_addr, default=None, help="Entry address for JMP at 0x0000.")
    parser.add_argument("--out", required=True, help="Output image path.")
    parser.add_argument("--map-out", default=None, help="Optional text map output.")
    args = parser.parse_args(argv)

    if args.size <= 0:
        raise ImageError("size must be positive")
    if args.fill < 0 or args.fill > 0xFF:
        raise ImageError("fill must be a byte value")

    image = bytearray([args.fill] * args.size)
    map_lines: List[str] = []

    if args.entry is not None:
        if args.entry < 0 or args.entry > 0xFFFF:
            raise ImageError("entry must fit in 16-bit address space")
        # 8080/Z80 JMP opcode at 0x0000.
        image[0] = 0xC3
        image[1] = args.entry & 0xFF
        image[2] = (args.entry >> 8) & 0xFF
        map_lines.append(f"entry_jump 0x0000..0x0002 -> 0x{args.entry:04X}")

    for spec in args.segment:
        path, addr = parse_segment(spec)
        data = path.read_bytes()
        write_segment(image, addr, data, str(path))
        map_lines.append(f"segment {path} @ 0x{addr:04X} ({len(data)} bytes)")

    for spec in args.bsp:
        path, addr = parse_segment(spec)
        data = path.read_bytes()
        write_segment(image, addr, data, str(path))
        map_lines.append(f"bsp {path} @ 0x{addr:04X} ({len(data)} bytes)")

    out_path = Path(args.out)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_bytes(image)

    if args.map_out:
        Path(args.map_out).write_text("\n".join(map_lines) + "\n", encoding="utf-8")

    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main(sys.argv[1:]))
    except ImageError as exc:
        print(f"mk_os_image: ERROR: {exc}", file=sys.stderr)
        raise SystemExit(2)
