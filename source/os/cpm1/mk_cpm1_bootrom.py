#!/usr/bin/env python3
"""
mk_cpm1_bootrom.py

Emit a small ROM stub that disables the ROM overlay and jumps to entry.
"""

from __future__ import annotations

import argparse
from pathlib import Path


def parse_addr(text: str) -> int:
    text = text.strip()
    if text.lower().startswith("0x"):
        return int(text, 16)
    return int(text, 10)


def main() -> int:
    parser = argparse.ArgumentParser(description="Build CP/M 1.x boot ROM stub.")
    parser.add_argument("--entry", type=parse_addr, default=0x0100, help="Entry address.")
    parser.add_argument("--out", required=True, help="Output ROM path.")
    parser.add_argument("--size", type=parse_addr, default=256, help="ROM size in bytes.")
    args = parser.parse_args()

    rom = bytearray([0x00] * args.size)
    rom[0:2] = bytes([0x3E, 0x00])  # MVI A,0
    rom[2:4] = bytes([0xD3, 0x3F])  # OUT 0x3F
    rom[4:7] = bytes([0xC3, args.entry & 0xFF, (args.entry >> 8) & 0xFF])  # JMP entry

    out_path = Path(args.out)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_bytes(rom)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
