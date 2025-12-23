#!/usr/bin/env python3
"""
mk_bsp_blob.py

Generate a fixed-format BSP (Board Support Parameters) blob from a YAML spec.
"""

from __future__ import annotations

import argparse
import sys
from pathlib import Path
from typing import Any, Dict, List, Tuple


class BspError(Exception):
    pass


def _strip_comment_line(line: str) -> str:
    stripped = line.lstrip()
    if stripped.startswith("#"):
        return ""
    return line.rstrip("\r\n")


def _parse_scalar(text: str) -> Any:
    s = text.strip()
    if s == "":
        return ""
    if s.startswith("'") and s.endswith("'") and len(s) >= 2:
        return s[1:-1]
    if s.startswith('"') and s.endswith('"') and len(s) >= 2:
        return s[1:-1]
    lower = s.lower()
    if lower == "true":
        return True
    if lower == "false":
        return False
    if s.startswith("0x"):
        return int(s, 16)
    if s.lstrip("-").isdigit():
        return int(s, 10)
    return s


def _split_key_value(line: str) -> Tuple[str, str | None]:
    if ":" not in line:
        raise BspError(f"invalid mapping line (missing ':'): {line!r}")
    key, rest = line.split(":", 1)
    key = key.strip()
    rest = rest.strip()
    return key, rest if rest != "" else None


def _next_significant_line(lines: List[str], start: int) -> str | None:
    for i in range(start, len(lines)):
        cleaned = _strip_comment_line(lines[i])
        if cleaned.strip() == "":
            continue
        return cleaned
    return None


def parse_yaml_subset(text: str) -> Dict[str, Any]:
    lines = text.splitlines()
    root: Dict[str, Any] = {}
    stack: List[Tuple[int, Dict[str, Any] | List[Any]]] = [(0, root)]

    def current_container(expected_indent: int) -> Dict[str, Any] | List[Any]:
        while stack and stack[-1][0] > expected_indent:
            stack.pop()
        if not stack or stack[-1][0] != expected_indent:
            raise BspError(f"bad indentation at indent={expected_indent}")
        return stack[-1][1]

    for idx, raw in enumerate(lines):
        cleaned = _strip_comment_line(raw)
        if cleaned.strip() == "":
            continue
        indent = len(cleaned) - len(cleaned.lstrip(" "))
        if indent % 2 != 0:
            raise BspError(f"indentation must be multiple of 2 spaces (line {idx + 1})")

        content = cleaned.strip()
        container = current_container(indent)

        if content.startswith("- "):
            if not isinstance(container, list):
                raise BspError("list item in non-list context")
            item_text = content[2:].strip()
            if item_text == "":
                next_line = _next_significant_line(lines, idx + 1)
                if next_line is None:
                    raise BspError("'-' with no nested block at end of file")
                next_indent = len(next_line) - len(next_line.lstrip(" "))
                new_obj: Dict[str, Any] = {}
                container.append(new_obj)
                stack.append((next_indent, new_obj))
                continue
            if ":" in item_text:
                key, rest = _split_key_value(item_text)
                new_obj = {key: _parse_scalar(rest) if rest is not None else None}
                container.append(new_obj)
                stack.append((indent + 2, new_obj))
                continue
            container.append(_parse_scalar(item_text))
            continue

        if not isinstance(container, dict):
            raise BspError("mapping entry in non-dict context")
        key, rest = _split_key_value(content)
        if rest is None:
            next_line = _next_significant_line(lines, idx + 1)
            if next_line is None:
                raise BspError(f"key {key!r} missing nested block at end of file")
            next_indent = len(next_line) - len(next_line.lstrip(" "))
            new_obj2: Dict[str, Any] = {}
            container[key] = new_obj2
            stack.append((next_indent, new_obj2))
            continue
        container[key] = _parse_scalar(rest)

    return root


def _expect_dict(obj: Any, where: str) -> Dict[str, Any]:
    if not isinstance(obj, dict):
        raise BspError(f"{where} must be a mapping")
    return obj


def _expect_int(value: Any, where: str) -> int:
    if not isinstance(value, int):
        raise BspError(f"{where} must be an int")
    return int(value)


def _expect_bool(value: Any, where: str) -> bool:
    if not isinstance(value, bool):
        raise BspError(f"{where} must be a bool")
    return bool(value)


def _u16(value: int, where: str) -> int:
    if value < 0 or value > 0xFFFF:
        raise BspError(f"{where} out of 16-bit range")
    return value


def _write_u16(buf: List[int], off: int, value: int) -> None:
    buf[off] = value & 0xFF
    buf[off + 1] = (value >> 8) & 0xFF


def _write_u32(buf: List[int], off: int, value: int) -> None:
    _write_u16(buf, off, value & 0xFFFF)
    _write_u16(buf, off + 2, (value >> 16) & 0xFFFF)


def build_bsp_blob(spec: Dict[str, Any]) -> bytes:
    bsp = _expect_dict(spec.get("bsp"), "bsp")

    console = _expect_dict(bsp.get("console"), "bsp.console")
    block = _expect_dict(bsp.get("block"), "bsp.block")
    timer = _expect_dict(bsp.get("timer"), "bsp.timer")

    console_kind_map = {
        "CARBONIO_UART": 1,
        "SIO": 2,
    }
    block_kind_map = {
        "IDE": 1,
        "CPMDISK": 2,
        "RAMDISK": 3,
    }
    timer_kind_map = {
        "CARBONIO_TICK": 1,
        "NONE": 0,
    }

    def kind_id(kind: Any, mapping: Dict[str, int], where: str) -> int:
        if isinstance(kind, int):
            return kind
        if not isinstance(kind, str):
            raise BspError(f"{where} must be string or int")
        if kind not in mapping:
            raise BspError(f"{where}: unknown kind {kind!r}")
        return mapping[kind]

    version = _expect_int(bsp.get("version", 1), "bsp.version")
    bdt_base = _u16(_expect_int(bsp.get("bdt_base"), "bsp.bdt_base"), "bsp.bdt_base")
    bdt_size = _u16(_expect_int(bsp.get("bdt_size"), "bsp.bdt_size"), "bsp.bdt_size")
    console_base = _u16(_expect_int(console.get("io_base"), "bsp.console.io_base"), "bsp.console.io_base")
    block_base = _u16(_expect_int(block.get("io_base"), "bsp.block.io_base"), "bsp.block.io_base")
    timer_base = _u16(_expect_int(timer.get("io_base"), "bsp.timer.io_base"), "bsp.timer.io_base")
    fpu_present = _expect_bool(bsp.get("fpu_present", False), "bsp.fpu_present")
    sector_bytes = _u16(_expect_int(block.get("sector_bytes", 512), "bsp.block.sector_bytes"),
                        "bsp.block.sector_bytes")

    console_kind = kind_id(console.get("kind"), console_kind_map, "bsp.console.kind")
    block_kind = kind_id(block.get("kind"), block_kind_map, "bsp.block.kind")
    timer_kind = kind_id(timer.get("kind"), timer_kind_map, "bsp.timer.kind")

    size = 32
    blob = [0x00] * size
    _write_u32(blob, 0, 0x50534243)  # "CBSP"
    _write_u16(blob, 4, version)
    _write_u16(blob, 6, size)
    _write_u16(blob, 8, bdt_base)
    _write_u16(blob, 10, bdt_size)
    _write_u16(blob, 12, console_base)
    _write_u16(blob, 14, block_base)
    _write_u16(blob, 16, timer_base)
    blob[18] = 1 if fpu_present else 0
    blob[19] = 0
    blob[20] = console_kind & 0xFF
    blob[21] = block_kind & 0xFF
    blob[22] = timer_kind & 0xFF
    blob[23] = 0
    _write_u16(blob, 24, sector_bytes)
    _write_u16(blob, 26, 0)
    _write_u32(blob, 28, 0)
    return bytes(blob)


def main(argv: List[str]) -> int:
    parser = argparse.ArgumentParser(description="Generate BSP blob from YAML.")
    parser.add_argument("--spec", required=True, help="Path to BSP YAML.")
    parser.add_argument("--out", required=True, help="Output blob path.")
    args = parser.parse_args(argv)

    path = Path(args.spec)
    data = parse_yaml_subset(path.read_text(encoding="utf-8"))
    blob = build_bsp_blob(data)

    out_path = Path(args.out)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_bytes(blob)
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main(sys.argv[1:]))
    except BspError as exc:
        print(f"mk_bsp_blob: ERROR: {exc}", file=sys.stderr)
        raise SystemExit(2)
