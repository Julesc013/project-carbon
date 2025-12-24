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
KI_GEN_VERSION = "0.2"

GRID_MM = 1.27  # 50 mil grid in mm

_UUID_NS = uuid.uuid5(uuid.NAMESPACE_URL, "https://project-carbon.local/kicadgen/v1")

PIN_SPACING_U = 2
PIN_MARGIN_U = 2
MIN_SHEET_H_U = 30


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
            return f"{tab}()"

        head, *rest = node
        if not rest:
            return f"{tab}({_sexp(head, 0)})"

        inline = (
            len(rest) <= 2
            and all(not isinstance(x, list) for x in rest)
            and all(not isinstance(x, dict) for x in rest)
        )
        if inline:
            inner = " ".join(_sexp(x, 0) for x in [head, *rest])
            return f"{tab}({inner})"

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


def _effects(font_mm: float = 1.27, justify: Optional[str] = None, *, hide: bool = False) -> List[Any]:
    effects: List[Any] = [Sym("effects"), [Sym("font"), [Sym("size"), font_mm, font_mm]]]
    if justify:
        effects.append([Sym("justify"), Sym(justify)])
    if hide:
        effects.append([Sym("hide"), Sym("yes")])
    return effects


def _property(
    name: str,
    value: str,
    at_xy: Tuple[float, float],
    rot: int = 0,
    *,
    font_mm: float = 1.27,
    justify: Optional[str] = None,
    hide: bool = False,
) -> List[Any]:
    x, y = at_xy
    return [
        Sym("property"),
        name,
        value,
        [Sym("at"), x, y, rot],
        _effects(font_mm=font_mm, justify=justify, hide=hide),
    ]


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
    *,
    lib_symbols: Optional[Sequence[List[Any]]] = None,
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
    ]

    libs: List[Any] = [Sym("lib_symbols")]
    if lib_symbols:
        libs.extend(list(lib_symbols))
    root.append(libs)

    root.extend(items)
    root.append([Sym("sheet_instances"), [Sym("path"), "/", [Sym("page"), "1"]]])
    root.append([Sym("embedded_fonts"), Sym("no")])

    out = _sexp(root, 0)
    if not out.endswith("\n"):
        out += "\n"
    return out


def _carbon_block_symbol_def(symbol_name: str, *, ref_prefix: str, description: str) -> List[Any]:
    w = _grid(20)
    h = _grid(10)
    hw = w / 2.0
    hh = h / 2.0

    full_name = f"carbon_blocks:{symbol_name}"
    return [
        Sym("symbol"),
        full_name,
        [Sym("pin_names"), [Sym("offset"), 1.016]],
        [Sym("exclude_from_sim"), Sym("no")],
        [Sym("in_bom"), Sym("yes")],
        [Sym("on_board"), Sym("yes")],
        _property("Reference", ref_prefix, (0.0, hh + _grid(2))),
        _property("Value", symbol_name, (0.0, -hh - _grid(2))),
        _property("Footprint", "", (0.0, 0.0), hide=True),
        _property("Datasheet", "", (0.0, 0.0), hide=True),
        _property("Description", description, (0.0, 0.0), hide=True),
        [
            Sym("symbol"),
            f"{symbol_name}_1_1",
            [
                Sym("rectangle"),
                [Sym("start"), -hw, hh],
                [Sym("end"), hw, -hh],
                [Sym("stroke"), [Sym("width"), 0.254], [Sym("type"), Sym("default")]],
                [Sym("fill"), [Sym("type"), Sym("background")]],
            ],
        ],
        [Sym("embedded_fonts"), Sym("no")],
    ]


def _carbon_symbols_by_name() -> Dict[str, List[Any]]:
    return {
        "CARBON_BLOCK_CPU": _carbon_block_symbol_def(
            "CARBON_BLOCK_CPU", ref_prefix="U", description="Project Carbon CPU placeholder block"
        ),
        "CARBON_BLOCK_FPU": _carbon_block_symbol_def(
            "CARBON_BLOCK_FPU", ref_prefix="U", description="Project Carbon FPU placeholder block"
        ),
        "CARBON_BLOCK_ACCEL": _carbon_block_symbol_def(
            "CARBON_BLOCK_ACCEL", ref_prefix="U", description="Project Carbon accelerator placeholder block"
        ),
        "CARBON_BLOCK_FABRIC": _carbon_block_symbol_def(
            "CARBON_BLOCK_FABRIC", ref_prefix="U", description="Project Carbon fabric/interconnect placeholder block"
        ),
        "CARBON_BLOCK_SRAM": _carbon_block_symbol_def(
            "CARBON_BLOCK_SRAM", ref_prefix="U", description="Project Carbon SRAM placeholder block"
        ),
        "CARBON_BLOCK_ROM": _carbon_block_symbol_def(
            "CARBON_BLOCK_ROM", ref_prefix="U", description="Project Carbon ROM placeholder block"
        ),
        "CARBON_BLOCK_DRAM": _carbon_block_symbol_def(
            "CARBON_BLOCK_DRAM", ref_prefix="U", description="Project Carbon DRAM placeholder block"
        ),
        "CARBON_BLOCK_CAI_ACCEL": _carbon_block_symbol_def(
            "CARBON_BLOCK_CAI_ACCEL", ref_prefix="U", description="Project Carbon CAI accelerator placeholder block"
        ),
        "CARBON_BLOCK_MMIO": _carbon_block_symbol_def(
            "CARBON_BLOCK_MMIO", ref_prefix="U", description="Project Carbon MMIO/decoder placeholder block"
        ),
        "CARBON_BLOCK_CONN_HEADER": _carbon_block_symbol_def(
            "CARBON_BLOCK_CONN_HEADER", ref_prefix="J", description="Project Carbon generic header connector placeholder"
        ),
        "CARBON_BLOCK_CLOCK_RESET": _carbon_block_symbol_def(
            "CARBON_BLOCK_CLOCK_RESET", ref_prefix="U", description="Project Carbon clock/reset placeholder block"
        ),
        "CARBON_BLOCK_POWER": _carbon_block_symbol_def(
            "CARBON_BLOCK_POWER", ref_prefix="U", description="Project Carbon power distribution placeholder block"
        ),
        "CARBON_BLOCK_DBG": _carbon_block_symbol_def(
            "CARBON_BLOCK_DBG", ref_prefix="U", description="Project Carbon debug/JTAG/UART placeholder block"
        ),
        "CARBON_BLOCK_RC2014_ADAPTER": _carbon_block_symbol_def(
            "CARBON_BLOCK_RC2014_ADAPTER", ref_prefix="U", description="Project Carbon RC2014 adapter placeholder block"
        ),
        "CARBON_BLOCK_S100_ADAPTER": _carbon_block_symbol_def(
            "CARBON_BLOCK_S100_ADAPTER", ref_prefix="U", description="Project Carbon S-100 adapter placeholder block"
        ),
    }


def _symbol_instance(
    *,
    project: str,
    root_uuid: str,
    file_id: str,
    lib_id: str,
    ref: str,
    value: str,
    at_xy: Tuple[float, float],
) -> List[Any]:
    x, y = at_xy
    sym_uuid = _stable_uuid("sym", file_id, lib_id, ref, value)
    return [
        Sym("symbol"),
        [Sym("lib_id"), lib_id],
        [Sym("at"), x, y, 0],
        [Sym("unit"), 1],
        [Sym("exclude_from_sim"), Sym("no")],
        [Sym("in_bom"), Sym("yes")],
        [Sym("on_board"), Sym("yes")],
        [Sym("dnp"), Sym("no")],
        [Sym("uuid"), sym_uuid],
        _property("Reference", ref, (x, y + _grid(8))),
        _property("Value", value, (x, y - _grid(8))),
        _property("Footprint", "", (x, y), hide=True),
        _property("Datasheet", "", (x, y), hide=True),
        _property("Description", "", (x, y), hide=True),
        [
            Sym("instances"),
            [Sym("project"), project, [Sym("path"), f"/{root_uuid}", [Sym("reference"), ref], [Sym("unit"), 1]]],
        ],
    ]


def _read_json(path: Path) -> Dict[str, Any]:
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except FileNotFoundError as e:
        raise KicadGenError(f"Missing mapping spec: {path}") from e
    except json.JSONDecodeError as e:
        raise KicadGenError(f"Invalid JSON in mapping spec: {path}: {e}") from e


def _load_spec(spec_dir: Path, base_name: str) -> Dict[str, Any]:
    json_path = spec_dir / f"{base_name}.json"
    yaml_path = spec_dir / f"{base_name}.yaml"
    if json_path.exists():
        return _read_json(json_path)
    if yaml_path.exists():
        return _read_json(yaml_path)
    raise KicadGenError(f"Missing mapping spec: {json_path} (or {yaml_path})")


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
    display_name = str(core.get("display_name", core_name))
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
        title = f"{display_name}::{b.get('name', sheet_file)}"
        items = [
            _text_box(
                f"Generated placeholder block for {display_name}/{b.get('name', sheet_file)}",
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

    items: List[List[Any]] = [
        _text_box(
            f"Generated core top: {display_name}  (edit mapping specs; do not hand-edit generated/)",
            (_grid(10), _grid(10)),
            (_grid(90), _grid(6)),
            rel_top,
        )
    ]
    notes = core.get("notes", [])
    if isinstance(notes, (list, tuple)) and notes:
        note_text = "\n".join(str(n) for n in notes if str(n).strip())
        if note_text:
            items.append(
                _text_box(
                    note_text,
                    (_grid(10), _grid(18)),
                    (_grid(90), _grid(10)),
                    rel_top,
                )
            )
    items.extend(sheets)
    items.extend(hlabels)
    _write_text(top_path, _kicad_schematic(rel_top, f"{display_name} (generated)", common, items))
    written.append(top_path)
    return written


def _generate_common(common: Dict[str, Any], root: Path) -> List[Path]:
    generated_root = (root / "schem/kicad9/generated").resolve()
    common_dir = generated_root / "common"
    common_dir.mkdir(parents=True, exist_ok=True)

    written: List[Path] = []

    carbon_symbols = _carbon_symbols_by_name()
    common_sheets = common.get("common_sheets", [])
    if not isinstance(common_sheets, list) or not common_sheets:
        raise KicadGenError("common_sheets must be a non-empty list in kicadgen_common spec")

    for entry in common_sheets:
        if not isinstance(entry, dict):
            continue
        fname = str(entry.get("sheet_file", "")).strip()
        title = str(entry.get("title", "")).strip() or fname
        sym_name = str(entry.get("symbol", "")).strip()
        sym_ref = str(entry.get("ref", "U")).strip() or "U"
        if not fname:
            continue
        if sym_name not in carbon_symbols:
            raise KicadGenError(f"Unknown symbol '{sym_name}' in common_sheets entry {entry!r}")

        path = common_dir / fname
        rel_path = str(path.relative_to(root)).replace("\\", "/")
        root_uuid = _stable_uuid("sch", rel_path)
        items = [
            _text_box(
                f"Generated common block: {title}",
                (_grid(10), _grid(10)),
                (_grid(90), _grid(6)),
                rel_path,
            ),
            _symbol_instance(
                project="carbon_common",
                root_uuid=root_uuid,
                file_id=rel_path,
                lib_id=f"carbon_blocks:{sym_name}",
                ref=sym_ref,
                value=title,
                at_xy=(_grid(60), _grid(40)),
            ),
        ]
        _write_text(path, _kicad_schematic(rel_path, title, common, items, lib_symbols=[carbon_symbols[sym_name]]))
        written.append(path)

    return written


def _generate_system(
    common: Dict[str, Any],
    core_index: Dict[str, Dict[str, Any]],
    system: Dict[str, Any],
    root: Path,
) -> List[Path]:
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

    def core_spec(core_name: str) -> Dict[str, Any]:
        if core_name in core_index:
            return core_index[core_name]
        raise KicadGenError(f"Unknown core referenced by system mapping: {core_name}")

    def core_top_path(core_name: str) -> str:
        c = core_spec(core_name)
        return str(Path(str(c["out_dir"])) / str(c["top_schematic"]))

    def _pin_dir(dir_name: str) -> str:
        d = dir_name.strip().lower()
        if d in {"input", "output", "bidirectional"}:
            return d
        return "bidirectional"

    def sheet_pins_for_core(
        core_name: str, sheet_x: float, sheet_y: float, sheet_w: float
    ) -> Tuple[int, List[Tuple[str, str, Tuple[float, float], int]]]:
        c = core_spec(core_name)
        interfaces = [str(x) for x in (c.get("interfaces", []) or [])]
        ports: List[Dict[str, str]] = []
        for iface in interfaces:
            ports.extend(_iface_ports(common, iface))

        left_ports = [p for p in ports if _pin_dir(p.get("dir", "")) != "output"]
        right_ports = [p for p in ports if _pin_dir(p.get("dir", "")) == "output"]
        max_pins = max(len(left_ports), len(right_ports), 1)
        height_u = max(MIN_SHEET_H_U, max_pins * PIN_SPACING_U + 2 * PIN_MARGIN_U)

        pins: List[Tuple[str, str, Tuple[float, float], int]] = []
        y0 = sheet_y + _grid(PIN_MARGIN_U)
        for idx, p in enumerate(left_ports):
            pins.append((p["name"], _pin_dir(p.get("dir", "")), (sheet_x, y0 + _grid(idx * PIN_SPACING_U)), 180))
        for idx, p in enumerate(right_ports):
            pins.append((p["name"], "output", (sheet_x + sheet_w, y0 + _grid(idx * PIN_SPACING_U)), 0))
        return height_u, pins

    cpu_core = str(system.get("cpu_core", "")).strip()
    if not cpu_core:
        raise KicadGenError(f"System mapping missing cpu_core: {sys_name}")
    accel_core = str(system.get("accel_core", "")).strip()

    cpu_sheetfile = os.path.relpath(_resolve_under(root, core_top_path(cpu_core)), out_dir).replace("\\", "/")
    accel_sheetfile = ""
    if accel_core:
        accel_sheetfile = os.path.relpath(_resolve_under(root, core_top_path(accel_core)), out_dir).replace("\\", "/")

    common_sheets = common.get("common_sheets", [])
    common_map: Dict[str, Dict[str, Any]] = {}
    if isinstance(common_sheets, list):
        for entry in common_sheets:
            if isinstance(entry, dict) and entry.get("name"):
                common_map[str(entry["name"]).lower()] = entry
    if not common_map:
        raise KicadGenError("common_sheets must define at least one entry")

    common_rel = os.path.relpath((root / "schem/kicad9/generated/common").resolve(), out_dir).replace("\\", "/")

    def common_sheetfile(sheet_name: str) -> str:
        key = sheet_name.strip().lower()
        if key not in common_map:
            raise KicadGenError(f"Unknown common sheet '{sheet_name}' in system {sys_name}")
        return f"{common_rel}/{common_map[key]['sheet_file']}"

    sheets: List[List[Any]] = []
    page = 2

    sheet_w = _grid(80)
    base_sheet_h = _grid(30)
    left_x, top_y = (_grid(10), _grid(20))
    right_x = _grid(110)

    cpu_h_u, cpu_pins = sheet_pins_for_core(cpu_core, left_x, top_y, sheet_w)
    cpu_h = _grid(cpu_h_u)

    accel_h = base_sheet_h
    accel_pins: List[Tuple[str, str, Tuple[float, float], int]] = []
    if accel_sheetfile:
        accel_h_u, accel_pins = sheet_pins_for_core(accel_core, right_x, top_y, sheet_w)
        accel_h = _grid(accel_h_u)

    top_row_h = max(cpu_h, accel_h)
    row_gap = _grid(10)
    mem_y = top_y + top_row_h + row_gap
    right_y = top_y + top_row_h + row_gap

    sheets.append(
        _sheet(
            project=project_name,
            root_uuid=root_uuid,
            page=page,
            sheetname="blk_cpu",
            sheetfile=cpu_sheetfile,
            at_xy=(left_x, top_y),
            size_wh=(sheet_w, cpu_h),
            pins=cpu_pins,
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
                at_xy=(right_x, top_y),
                size_wh=(sheet_w, accel_h),
                pins=accel_pins,
            )
        )
        page += 1

    # Memory blocks on left column.
    memory = [str(x) for x in (system.get("memory", []) or [])]
    for mem in memory:
        mem_key = str(mem).strip().lower()
        if mem_key in {"rom", "sram", "dram"} and mem_key in common_map:
            sheets.append(
                _sheet(
                    project=project_name,
                    root_uuid=root_uuid,
                    page=page,
                    sheetname=f"blk_{mem_key}",
                    sheetfile=common_sheetfile(mem_key),
                    at_xy=(left_x, mem_y),
                    size_wh=(sheet_w, base_sheet_h),
                )
            )
            page += 1
            mem_y += _grid(40)

    # Peripheral cores on right column.
    peripherals = [str(x) for x in (system.get("peripherals", []) or [])]
    for periph in peripherals:
        periph = periph.strip()
        if not periph:
            continue
        periph_h_u, periph_pins = sheet_pins_for_core(periph, right_x, right_y, sheet_w)
        periph_h = _grid(periph_h_u)
        sheets.append(
            _sheet(
                project=project_name,
                root_uuid=root_uuid,
                page=page,
                sheetname=_sanitize_sheetname(periph),
                sheetfile=os.path.relpath(_resolve_under(root, core_top_path(periph)), out_dir).replace("\\", "/"),
                at_xy=(right_x, right_y),
                size_wh=(sheet_w, periph_h),
                pins=periph_pins,
            )
        )
        page += 1
        right_y += periph_h + _grid(10)

    # Common blocks on right column.
    common_blocks = [str(x) for x in (system.get("common_blocks", []) or [])]
    adapters = [str(x) for x in (system.get("adapters", []) or [])]
    adapter_map = {
        "rc2014": "rc2014_adapter",
        "s-100": "s100_adapter",
        "s100": "s100_adapter",
    }
    for adapter in adapters:
        key = adapter.strip().lower()
        if key in adapter_map:
            common_blocks.append(adapter_map[key])

    for blk in common_blocks:
        blk_key = blk.strip().lower()
        if not blk_key:
            continue
        sheets.append(
            _sheet(
                project=project_name,
                root_uuid=root_uuid,
                page=page,
                sheetname=f"blk_{blk_key}",
                sheetfile=common_sheetfile(blk_key),
                at_xy=(right_x, right_y),
                size_wh=(sheet_w, base_sheet_h),
            )
        )
        page += 1
        right_y += _grid(40)

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
    common = _load_spec(spec_dir, "kicadgen_common")
    cores_spec = _load_spec(spec_dir, "kicadgen_cores")
    systems_spec = _load_spec(spec_dir, "kicadgen_systems")

    written: List[Path] = []
    written.extend(_generate_common(common, root))

    cores_list = cores_spec.get("cores", []) or []
    core_index = {str(c.get("name")): c for c in cores_list if isinstance(c, dict) and c.get("name")}

    for core in cores_list:
        written.extend(_generate_core(common, core, root))

    for sys_spec in systems_spec.get("systems", []) or []:
        written.extend(_generate_system(common, core_index, sys_spec, root))

    return written


def main(argv: Optional[Sequence[str]] = None) -> int:
    script_dir = Path(__file__).resolve().parent
    default_root = script_dir.parents[2]

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
