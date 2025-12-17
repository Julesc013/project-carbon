#!/usr/bin/env python3
"""
kicadgen: Generate KiCad 9 hierarchical schematics for Project Carbon.

Design goals:
- Deterministic output (stable UUIDs, stable ordering)
- Generator only overwrites schem/kicad9/generated/
- Data-driven via schem/kicad9/spec/*.yaml (YAML 1.2-compatible JSON)
- Python stdlib only

This produces a v1 *logical* schematic hierarchy (block-level placeholders).
"""

from __future__ import annotations

import argparse
import json
import os
import re
import sys
import uuid
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Dict, Iterable, List, Optional, Sequence, Tuple, Union


KI_SCH_VERSION = 20250114
KI_GEN_NAME = "kicadgen"
KI_GEN_VERSION = "0.1"

GRID_MM = 1.27  # 50 mil grid in mm

_UUID_NS = uuid.uuid5(uuid.NAMESPACE_URL, "https://project-carbon.local/kicadgen/v1")


class KicadGenError(RuntimeError):
    pass


@dataclass(frozen=True)
class Sym:
    value: str


def _stable_uuid(*parts: str) -> str:
    return str(uuid.uuid5(_UUID_NS, "/".join(parts)))


def _q(s: str) -> str:
    escaped = (
        s.replace("\\", "\\\\")
        .replace('"', '\\"')
        .replace("\r", "\\r")
        .replace("\n", "\\n")
        .replace("\t", "\\t")
    )
    return f'"{escaped}"'


def _fmt_num(value: Union[int, float]) -> str:
    if isinstance(value, int):
        return str(value)
    s = f"{value:.4f}".rstrip("0").rstrip(".")
    if s == "-0":
        s = "0"
    return s


def _sexp(node: Any, indent: int = 0) -> str:
    tab = "\t" * indent

    if isinstance(node, Sym):
        return node.value
    if isinstance(node, bool):
        return "yes" if node else "no"
    if isinstance(node, (int, float)):
        return _fmt_num(node)
    if isinstance(node, str):
        return _q(node)
    if isinstance(node, list):
        if not node:
            return "()"

        head, *rest = node
        if not rest:
            return f"({_sexp(head, 0)})"

        inline = (
            len(rest) <= 2
            and all(not isinstance(x, list) for x in rest)
            and all(not isinstance(x, dict) for x in rest)
        )
        if inline:
            inner = " ".join(_sexp(x, 0) for x in [head, *rest])
            return f"({inner})"

        lines = [f"{tab}({_sexp(head, 0)}"]
        for child in rest:
            if isinstance(child, list):
                lines.append(_sexp(child, indent + 1))
            else:
                child_tab = "\t" * (indent + 1)
                lines.append(f"{child_tab}{_sexp(child, 0)}")
        lines.append(f"{tab})")
        return "\n".join(lines)

    raise TypeError(f"Unsupported S-expression node type: {type(node)!r}")


def _grid(n: int) -> float:
    return n * GRID_MM


def _effects(font_mm: float = 1.27, justify: Optional[str] = None) -> List[Any]:
    effects: List[Any] = [Sym("effects"), [Sym("font"), [Sym("size"), font_mm, font_mm]]]
    if justify:
        effects.append([Sym("justify"), Sym(justify)])
    return effects


def _title_block(title: str, common: Dict[str, Any]) -> List[Any]:
    tb = [Sym("title_block"), [Sym("title"), title]]
    company = (common.get("layout", {}).get("title_block", {}) or {}).get("company")
    if company:
        tb.append([Sym("company"), company])

    comments = common.get("layout", {}).get("title_block", {}) or {}
    for key, idx in [("comment1", 1), ("comment2", 2), ("comment3", 3), ("comment4", 4), ("comment5", 5)]:
        if key in comments and comments[key]:
            tb.append([Sym("comment"), idx, str(comments[key])])
    return tb


def _sheet(
    project: str,
    root_uuid: str,
    page: int,
    sheetname: str,
    sheetfile: str,
    at_xy: Tuple[float, float],
    size_wh: Tuple[float, float],
    pins: Sequence[Tuple[str, str, Tuple[float, float], int]] = (),
    sheet_uuid: Optional[str] = None,
) -> List[Any]:
    x, y = at_xy
    w, h = size_wh
    suuid = sheet_uuid or _stable_uuid("sheet", project, sheetname, sheetfile)

    s: List[Any] = [
        Sym("sheet"),
        [Sym("at"), x, y],
        [Sym("size"), w, h],
        [Sym("exclude_from_sim"), Sym("no")],
        [Sym("in_bom"), Sym("yes")],
        [Sym("on_board"), Sym("yes")],
        [Sym("dnp"), Sym("no")],
        [Sym("stroke"), [Sym("width"), 0], [Sym("type"), Sym("solid")]],
        [Sym("fill"), [Sym("color"), 0, 0, 0, 0.0]],
        [Sym("uuid"), suuid],
        [
            Sym("property"),
            "Sheetname",
            sheetname,
            [Sym("at"), x, y - _grid(1), 0],
            _effects(justify="left"),
        ],
        [
            Sym("property"),
            "Sheetfile",
            sheetfile,
            [Sym("at"), x, y + h + _grid(1), 0],
            _effects(justify="left"),
        ],
    ]

    for pin_name, pin_dir, (px, py), rot in pins:
        pin_uuid = _stable_uuid("sheetpin", suuid, pin_name, pin_dir)
        s.append(
            [
                Sym("pin"),
                pin_name,
                Sym(pin_dir),
                [Sym("at"), px, py, rot],
                [Sym("uuid"), pin_uuid],
                _effects(justify="left" if rot == 180 else "right"),
            ]
        )

    s.append(
        [
            Sym("instances"),
            [Sym("project"), project, [Sym("path"), f"/{root_uuid}", [Sym("page"), str(page)]]],
        ]
    )
    return s


def _hier_label(
    label: str, direction: str, at_xy: Tuple[float, float], rot: int, file_id: str
) -> List[Any]:
    x, y = at_xy
    shape = direction.lower()
    if shape not in {"input", "output", "bidirectional"}:
        shape = "bidirectional"

    just = "right" if rot == 180 else "left"
    return [
        Sym("hierarchical_label"),
        label,
        [Sym("shape"), Sym(shape)],
        [Sym("at"), x, y, rot],
        _effects(justify=just),
        [Sym("uuid"), _stable_uuid("hlabel", file_id, label, shape)],
    ]


def _text_box(text: str, at_xy: Tuple[float, float], size_wh: Tuple[float, float], file_id: str) -> List[Any]:
    x, y = at_xy
    w, h = size_wh
    return [
        Sym("text_box"),
        text,
        [Sym("exclude_from_sim"), Sym("no")],
        [Sym("at"), x, y, 0],
        [Sym("size"), w, h],
        [Sym("margins"), _grid(1), _grid(1), _grid(1), _grid(1)],
        [Sym("stroke"), [Sym("width"), 0], [Sym("type"), Sym("default")], [Sym("color"), 0, 0, 0, 1]],
        [Sym("fill"), [Sym("type"), Sym("color")], [Sym("color"), 255, 255, 150, 1]],
        _effects(justify="left"),
        [Sym("uuid"), _stable_uuid("textbox", file_id, text)],
    ]


def _kicad_schematic(
    rel_path: str,
    title: str,
    common: Dict[str, Any],
    items: Sequence[List[Any]],
    paper: Optional[str] = None,
) -> str:
    paper_name = paper or common.get("layout", {}).get("paper", "A3")
    root_uuid = _stable_uuid("sch", rel_path)

    root: List[Any] = [
        Sym("kicad_sch"),
        [Sym("version"), int(common.get("kicad", {}).get("version", KI_SCH_VERSION))],
        [Sym("generator"), str(common.get("kicad", {}).get("generator", KI_GEN_NAME))],
        [Sym("generator_version"), str(common.get("kicad", {}).get("generator_version", KI_GEN_VERSION))],
        [Sym("uuid"), root_uuid],
        [Sym("paper"), paper_name],
        _title_block(title, common),
        [Sym("lib_symbols")],
    ]

    root.extend(items)
    root.append([Sym("sheet_instances"), [Sym("path"), "/", [Sym("page"), "1"]]])
    root.append([Sym("embedded_fonts"), Sym("no")])

    out = _sexp(root, 0)
    if not out.endswith("\n"):
        out += "\n"
    return out


def _read_json(path: Path) -> Dict[str, Any]:
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except FileNotFoundError as e:
        raise KicadGenError(f"Missing mapping spec: {path}") from e
    except json.JSONDecodeError as e:
        raise KicadGenError(f"Invalid JSON in mapping spec: {path}: {e}") from e


def _write_text(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8", newline="\n") as f:
        f.write(text)


def _resolve_under(root: Path, rel_or_abs: str) -> Path:
    p = Path(rel_or_abs)
    if p.is_absolute():
        return p.resolve()
    return (root / p).resolve()


def _ensure_within(path: Path, base: Path) -> None:
    base = base.resolve()
    path = path.resolve()
    if path == base:
        return
    if base not in path.parents:
        raise KicadGenError(f"Refusing to write outside generated/: {path} (base: {base})")


def _iface_ports(common: Dict[str, Any], iface_name: str) -> List[Dict[str, str]]:
    interfaces = common.get("interfaces", {}) or {}
    iface = interfaces.get(iface_name)
    if not isinstance(iface, dict):
        raise KicadGenError(f"Unknown interface in mapping spec: {iface_name}")
    ports = iface.get("ports", [])
    if not isinstance(ports, list):
        raise KicadGenError(f"Invalid ports for interface: {iface_name}")
    out: List[Dict[str, str]] = []
    for p in ports:
        if not isinstance(p, dict) or "name" not in p:
            continue
        out.append({"name": str(p["name"]), "dir": str(p.get("dir", "bidirectional"))})
    return out


def _sanitize_sheetname(name: str) -> str:
    name = name.strip()
    name = re.sub(r"[^A-Za-z0-9_]+", "_", name)
    if not name:
        name = "blk"
    if not name.startswith("blk_"):
        name = f"blk_{name}"
    return name


def _generate_core(common: Dict[str, Any], core: Dict[str, Any], root: Path) -> List[Path]:
    out_dir = _resolve_under(root, str(core["out_dir"]))
    generated_root = (root / "schem/kicad9/generated").resolve()
    _ensure_within(out_dir, generated_root)
    out_dir.mkdir(parents=True, exist_ok=True)

    core_name = str(core["name"])
    top_name = str(core["top_schematic"])
    top_path = out_dir / top_name
    rel_top = str(top_path.relative_to(root)).replace("\\", "/")

    written: List[Path] = []

    blocks = core.get("blocks", []) or []
    # Generate child block sheets first.
    for b in blocks:
        sheet_file = str(b["sheet_file"])
        sheet_path = out_dir / sheet_file
        rel_sheet = str(sheet_path.relative_to(root)).replace("\\", "/")
        title = f"{core_name}::{b.get('name', sheet_file)}"
        items = [
            _text_box(
                f"Generated placeholder block for {core_name}/{b.get('name', sheet_file)}",
                (_grid(10), _grid(10)),
                (_grid(60), _grid(6)),
                rel_sheet,
            )
        ]
        _write_text(sheet_path, _kicad_schematic(rel_sheet, title, common, items))
        written.append(sheet_path)

    # Place block sheets on the core top-level.
    sheets: List[List[Any]] = []
    col_w = _grid(90)
    row_h = _grid(40)
    sheet_w = _grid(80)
    sheet_h = _grid(30)
    origin_x = _grid(10)
    origin_y = _grid(20)

    project_name = f"core_{core_name}"
    root_uuid = _stable_uuid("sch", rel_top)
    page = 2
    for idx, b in enumerate(blocks):
        sheet_file = str(b["sheet_file"])
        sheetname = _sanitize_sheetname(str(b.get("name", Path(sheet_file).stem)))
        col = idx % 2
        row = idx // 2
        x = origin_x + col * col_w
        y = origin_y + row * row_h
        sheets.append(
            _sheet(
                project=project_name,
                root_uuid=root_uuid,
                page=page,
                sheetname=sheetname,
                sheetfile=sheet_file,
                at_xy=(x, y),
                size_wh=(sheet_w, sheet_h),
                pins=(),
            )
        )
        page += 1

    # External interface ports as hierarchical labels on the core top sheet.
    hlabels: List[List[Any]] = []
    interfaces = core.get("interfaces", []) or []
    ports: List[Dict[str, str]] = []
    for iface in interfaces:
        ports.extend(_iface_ports(common, str(iface)))

    # Stable ordering: interface order then port order from mapping spec.
    left_x = _grid(6)
    right_x = origin_x + col_w * 2 + _grid(10)
    y0 = _grid(20)
    dy = _grid(2)
    y_left = y0
    y_right = y0
    for p in ports:
        pname = p["name"]
        pdir = p.get("dir", "bidirectional").lower()
        if pdir == "output":
            hlabels.append(_hier_label(pname, pdir, (right_x, y_right), 0, rel_top))
            y_right += dy
        else:
            hlabels.append(_hier_label(pname, pdir, (left_x, y_left), 180, rel_top))
            y_left += dy

    items = [
        _text_box(
            f"Generated core top: {core_name}  (edit mapping specs; do not hand-edit generated/)",
            (_grid(10), _grid(10)),
            (_grid(90), _grid(6)),
            rel_top,
        ),
        *sheets,
        *hlabels,
    ]
    _write_text(top_path, _kicad_schematic(rel_top, f"{core_name} (generated)", common, items))
    written.append(top_path)
    return written


def _generate_common(common: Dict[str, Any], root: Path) -> List[Path]:
    generated_root = (root / "schem/kicad9/generated").resolve()
    common_dir = generated_root / "common"
    common_dir.mkdir(parents=True, exist_ok=True)

    written: List[Path] = []

    common_sheets = [
        ("blk_clock_reset.kicad_sch", "Clock/Reset (placeholder)"),
        ("blk_debug_header.kicad_sch", "Debug Header (placeholder)"),
        ("blk_power_dist.kicad_sch", "Power Distribution (placeholder)"),
        ("blk_jtag_uart.kicad_sch", "JTAG/UART (placeholder)"),
        ("blk_rc2014_adapter.kicad_sch", "RC2014 Adapter (placeholder)"),
        ("blk_s100_adapter.kicad_sch", "S-100 Adapter (placeholder)"),
        ("blk_sram.kicad_sch", "SRAM (placeholder)"),
        ("blk_rom.kicad_sch", "ROM (placeholder)"),
        ("blk_dram.kicad_sch", "DRAM (placeholder)"),
    ]

    for fname, title in common_sheets:
        path = common_dir / fname
        rel_path = str(path.relative_to(root)).replace("\\", "/")
        items = [
            _text_box(
                f"Generated common block: {title}",
                (_grid(10), _grid(10)),
                (_grid(90), _grid(6)),
                rel_path,
            )
        ]
        _write_text(path, _kicad_schematic(rel_path, title, common, items))
        written.append(path)

    return written


def _generate_system(common: Dict[str, Any], system: Dict[str, Any], root: Path) -> List[Path]:
    out_dir = _resolve_under(root, str(system["out_dir"]))
    generated_root = (root / "schem/kicad9/generated").resolve()
    _ensure_within(out_dir, generated_root)
    out_dir.mkdir(parents=True, exist_ok=True)

    sys_name = str(system["name"])
    top_name = str(system["top_schematic"])
    top_path = out_dir / top_name
    rel_top = str(top_path.relative_to(root)).replace("\\", "/")

    project_name = f"system_{sys_name}"
    root_uuid = _stable_uuid("sch", rel_top)

    # Sheet refs.
    cpu_core = str(system.get("cpu_core", ""))
    accel_core = str(system.get("accel_core", ""))

    # Compute relative paths to core top schematics.
    def core_top_path(core_name: str) -> str:
        cores_spec = _read_json(root / "schem/kicad9/spec/kicadgen_cores.yaml")
        for c in cores_spec.get("cores", []) or []:
            if str(c.get("name")) == core_name:
                return str(Path(str(c["out_dir"])) / str(c["top_schematic"]))
        raise KicadGenError(f"Unknown core referenced by system mapping: {core_name}")

    cpu_sheetfile = os.path.relpath(_resolve_under(root, core_top_path(cpu_core)), out_dir).replace("\\", "/")
    accel_sheetfile = ""
    if accel_core:
        accel_sheetfile = os.path.relpath(_resolve_under(root, core_top_path(accel_core)), out_dir).replace("\\", "/")

    # System-level blocks as sheets (v1 placeholder).
    common_rel = os.path.relpath((root / "schem/kicad9/generated/common").resolve(), out_dir).replace("\\", "/")

    def common_sheetfile(fname: str) -> str:
        return f"{common_rel}/{fname}"

    sheets: List[List[Any]] = []
    page = 2

    cpu_at = (_grid(10), _grid(20))
    accel_at = (_grid(110), _grid(20))
    mem_at = (_grid(10), _grid(70))
    misc_at = (_grid(110), _grid(70))

    sheet_w = _grid(80)
    sheet_h = _grid(30)

    sheets.append(
        _sheet(
            project=project_name,
            root_uuid=root_uuid,
            page=page,
            sheetname="blk_cpu",
            sheetfile=cpu_sheetfile,
            at_xy=cpu_at,
            size_wh=(sheet_w, sheet_h),
            pins=(),
        )
    )
    page += 1

    if accel_sheetfile:
        sheets.append(
            _sheet(
                project=project_name,
                root_uuid=root_uuid,
                page=page,
                sheetname="blk_accel",
                sheetfile=accel_sheetfile,
                at_xy=accel_at,
                size_wh=(sheet_w, sheet_h),
                pins=(),
            )
        )
        page += 1

    memory = [str(x) for x in (system.get("memory", []) or [])]
    if "ROM" in memory:
        sheets.append(
            _sheet(
                project=project_name,
                root_uuid=root_uuid,
                page=page,
                sheetname="blk_rom",
                sheetfile=common_sheetfile("blk_rom.kicad_sch"),
                at_xy=mem_at,
                size_wh=(sheet_w, sheet_h),
            )
        )
        page += 1
        mem_at = (mem_at[0], mem_at[1] + _grid(40))
    if "SRAM" in memory:
        sheets.append(
            _sheet(
                project=project_name,
                root_uuid=root_uuid,
                page=page,
                sheetname="blk_sram",
                sheetfile=common_sheetfile("blk_sram.kicad_sch"),
                at_xy=mem_at,
                size_wh=(sheet_w, sheet_h),
            )
        )
        page += 1
        mem_at = (mem_at[0], mem_at[1] + _grid(40))
    if "DRAM" in memory:
        sheets.append(
            _sheet(
                project=project_name,
                root_uuid=root_uuid,
                page=page,
                sheetname="blk_dram",
                sheetfile=common_sheetfile("blk_dram.kicad_sch"),
                at_xy=mem_at,
                size_wh=(sheet_w, sheet_h),
            )
        )
        page += 1

    # Common blocks.
    sheets.append(
        _sheet(
            project=project_name,
            root_uuid=root_uuid,
            page=page,
            sheetname="blk_clock_reset",
            sheetfile=common_sheetfile("blk_clock_reset.kicad_sch"),
            at_xy=misc_at,
            size_wh=(sheet_w, sheet_h),
        )
    )
    page += 1
    misc_at = (misc_at[0], misc_at[1] + _grid(40))
    sheets.append(
        _sheet(
            project=project_name,
            root_uuid=root_uuid,
            page=page,
            sheetname="blk_debug_header",
            sheetfile=common_sheetfile("blk_debug_header.kicad_sch"),
            at_xy=misc_at,
            size_wh=(sheet_w, sheet_h),
        )
    )
    page += 1
    misc_at = (misc_at[0], misc_at[1] + _grid(40))
    sheets.append(
        _sheet(
            project=project_name,
            root_uuid=root_uuid,
            page=page,
            sheetname="blk_power_dist",
            sheetfile=common_sheetfile("blk_power_dist.kicad_sch"),
            at_xy=misc_at,
            size_wh=(sheet_w, sheet_h),
        )
    )
    page += 1

    adapters = [str(x) for x in (system.get("adapters", []) or [])]
    if "RC2014" in adapters:
        misc_at = (misc_at[0], misc_at[1] + _grid(40))
        sheets.append(
            _sheet(
                project=project_name,
                root_uuid=root_uuid,
                page=page,
                sheetname="blk_rc2014_adapter",
                sheetfile=common_sheetfile("blk_rc2014_adapter.kicad_sch"),
                at_xy=misc_at,
                size_wh=(sheet_w, sheet_h),
            )
        )
        page += 1
    if "S-100" in adapters:
        misc_at = (misc_at[0], misc_at[1] + _grid(40))
        sheets.append(
            _sheet(
                project=project_name,
                root_uuid=root_uuid,
                page=page,
                sheetname="blk_s100_adapter",
                sheetfile=common_sheetfile("blk_s100_adapter.kicad_sch"),
                at_xy=misc_at,
                size_wh=(sheet_w, sheet_h),
            )
        )
        page += 1

    items = [
        _text_box(
            f"Generated system top: {sys_name}  (edit mapping specs; do not hand-edit generated/)",
            (_grid(10), _grid(10)),
            (_grid(120), _grid(6)),
            rel_top,
        ),
        *sheets,
    ]
    _write_text(top_path, _kicad_schematic(rel_top, f"{sys_name} (generated)", common, items))
    return [top_path]


def generate(root: Path, spec_dir: Path) -> List[Path]:
    common = _read_json(spec_dir / "kicadgen_common.yaml")
    cores_spec = _read_json(spec_dir / "kicadgen_cores.yaml")
    systems_spec = _read_json(spec_dir / "kicadgen_systems.yaml")

    written: List[Path] = []
    written.extend(_generate_common(common, root))

    for core in cores_spec.get("cores", []) or []:
        written.extend(_generate_core(common, core, root))

    for sys_spec in systems_spec.get("systems", []) or []:
        written.extend(_generate_system(common, sys_spec, root))

    return written


def main(argv: Optional[Sequence[str]] = None) -> int:
    script_dir = Path(__file__).resolve().parent
    default_root = script_dir.parents[3]

    parser = argparse.ArgumentParser(description="Generate KiCad 9 hierarchical schematics (Project Carbon).")
    parser.add_argument(
        "--root",
        default=str(default_root),
        help="Repository root (defaults to the project-carbon repo root inferred from this script location).",
    )
    parser.add_argument(
        "--spec-dir",
        default="",
        help="Mapping spec directory (defaults to <root>/schem/kicad9/spec).",
    )
    args = parser.parse_args(list(argv) if argv is not None else None)

    root = Path(args.root).resolve()
    spec_dir = Path(args.spec_dir).resolve() if args.spec_dir else (root / "schem/kicad9/spec").resolve()

    generate(root=root, spec_dir=spec_dir)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
