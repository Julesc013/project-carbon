#!/usr/bin/env python3
"""
mk_cpm1_image.py

Compose a CP/M 1.x SYS16 memory image from user-supplied binaries.
"""

from __future__ import annotations

import argparse
import sys
from pathlib import Path
from typing import List


class ImageError(Exception):
    pass


def parse_addr(text: str) -> int:
    text = text.strip()
    if text.lower().startswith("0x"):
        return int(text, 16)
    return int(text, 10)


def write_segment(image: bytearray, base: int, data: bytes, name: str) -> None:
    end = base + len(data)
    if base < 0 or end > len(image):
        raise ImageError(f"{name} does not fit in image (0x{base:04X}..0x{end - 1:04X})")
    image[base:end] = data


def build_page0(entry: int, bdos_entry: int) -> bytes:
    page0 = bytearray([0x00] * 256)
    page0[0] = 0xC3
    page0[1] = entry & 0xFF
    page0[2] = (entry >> 8) & 0xFF
    page0[3] = 0x00
    page0[5] = 0xC3
    page0[6] = bdos_entry & 0xFF
    page0[7] = (bdos_entry >> 8) & 0xFF
    return bytes(page0)


def main(argv: List[str]) -> int:
    parser = argparse.ArgumentParser(description="Build a CP/M 1.x memory image.")
    parser.add_argument("--system", required=True, help="Combined CCP+BDOS+BIOS image.")
    parser.add_argument("--system-base", type=parse_addr, default=0x0100, help="System image base.")
    parser.add_argument("--entry", type=parse_addr, default=0x0100, help="Entry address for reset JMP.")
    parser.add_argument("--bdos-entry", type=parse_addr, default=0x0100, help="BDOS entry for 0x0005 JMP.")
    parser.add_argument("--page0", default=None, help="Optional page-0 binary (256 bytes).")
    parser.add_argument("--bsp", default=None, help="Optional BSP blob.")
    parser.add_argument("--bsp-addr", type=parse_addr, default=0xFF00, help="BSP load address.")
    parser.add_argument("--out", required=True, help="Output memory image path.")
    parser.add_argument("--map-out", default=None, help="Optional text map output.")
    args = parser.parse_args(argv)

    image = bytearray([0x00] * 65536)
    map_lines: List[str] = []

    system = Path(args.system).read_bytes()
    write_segment(image, args.system_base, system, "system")
    map_lines.append(f"system {args.system} @ 0x{args.system_base:04X} ({len(system)} bytes)")

    if args.page0:
        page0 = Path(args.page0).read_bytes()
        if len(page0) != 256:
            raise ImageError("page0 image must be exactly 256 bytes")
    else:
        page0 = build_page0(args.entry, args.bdos_entry)
    write_segment(image, 0x0000, page0, "page0")
    map_lines.append("page0 @ 0x0000 (256 bytes)")

    if args.bsp:
        bsp = Path(args.bsp).read_bytes()
        write_segment(image, args.bsp_addr, bsp, "bsp")
        map_lines.append(f"bsp {args.bsp} @ 0x{args.bsp_addr:04X} ({len(bsp)} bytes)")

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
        print(f"mk_cpm1_image: ERROR: {exc}", file=sys.stderr)
        raise SystemExit(2)
