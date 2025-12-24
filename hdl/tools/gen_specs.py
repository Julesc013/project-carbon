#!/usr/bin/env python3
from __future__ import annotations

import argparse
import os
import re
import sys
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Dict, List, Optional, Sequence, Tuple, Union


class SpecError(Exception):
    pass


_RE_INT = re.compile(r"^-?\d+$")
_RE_HEX = re.compile(r"^0x[0-9a-fA-F]+$")


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
    if s.startswith("[") and s.endswith("]"):
        inner = s[1:-1].strip()
        if inner == "":
            return []
        parts = [p.strip() for p in inner.split(",")]
        return [_parse_scalar(p) for p in parts if p != ""]
    if _RE_HEX.match(s):
        return int(s, 16)
    if _RE_INT.match(s):
        return int(s, 10)
    return s


def _split_key_value(line: str) -> Tuple[str, Optional[str]]:
    if ":" not in line:
        raise SpecError(f"Invalid mapping line (missing ':'): {line!r}")
    key, rest = line.split(":", 1)
    key = key.strip()
    if key == "":
        raise SpecError(f"Invalid mapping line (empty key): {line!r}")
    rest = rest.strip()
    if rest == "":
        return key, None
    return key, rest


def _next_significant_line(lines: Sequence[str], start_index: int) -> Optional[str]:
    for i in range(start_index, len(lines)):
        cleaned = _strip_comment_line(lines[i])
        if cleaned.strip() == "":
            continue
        return cleaned
    return None


def parse_yaml_subset(text: str, *, source: str = "<string>") -> Dict[str, Any]:
    lines = text.splitlines()
    root: Dict[str, Any] = {}
    stack: List[Tuple[int, Union[Dict[str, Any], List[Any]]]] = [(0, root)]

    def current_container(expected_indent: int) -> Union[Dict[str, Any], List[Any]]:
        while stack and stack[-1][0] > expected_indent:
            stack.pop()
        if not stack or stack[-1][0] != expected_indent:
            raise SpecError(f"{source}: bad indentation at indent={expected_indent}")
        return stack[-1][1]

    for index, raw in enumerate(lines):
        cleaned = _strip_comment_line(raw)
        if cleaned.strip() == "":
            continue
        indent = len(cleaned) - len(cleaned.lstrip(" "))
        if indent % 2 != 0:
            raise SpecError(f"{source}:{index+1}: indentation must be multiple of 2 spaces")

        content = cleaned.strip()
        container = current_container(indent)

        if content.startswith("- "):
            if not isinstance(container, list):
                raise SpecError(f"{source}:{index+1}: list item in non-list context")
            item_text = content[2:].strip()
            if item_text == "":
                next_line = _next_significant_line(lines, index + 1)
                if next_line is None:
                    raise SpecError(f"{source}:{index+1}: '-' with no value at end of file")
                next_indent = len(next_line) - len(next_line.lstrip(" "))
                if next_indent <= indent:
                    raise SpecError(f"{source}:{index+1}: '-' with no nested block")
                if next_line.strip().startswith("-"):
                    new_list: List[Any] = []
                    container.append(new_list)
                    stack.append((indent + 2, new_list))
                else:
                    new_dict: Dict[str, Any] = {}
                    container.append(new_dict)
                    stack.append((indent + 2, new_dict))
                continue

            if ":" in item_text:
                key, rest = _split_key_value(item_text)
                new_dict2: Dict[str, Any] = {}
                new_dict2[key] = _parse_scalar(rest) if rest is not None else None
                container.append(new_dict2)
                stack.append((indent + 2, new_dict2))
                continue

            container.append(_parse_scalar(item_text))
            continue

        if not isinstance(container, dict):
            raise SpecError(f"{source}:{index+1}: mapping entry in non-dict context")
        key, rest = _split_key_value(content)
        if rest is None:
            next_line = _next_significant_line(lines, index + 1)
            if next_line is None:
                raise SpecError(
                    f"{source}:{index+1}: key {key!r} missing nested block at end of file"
                )
            next_indent = len(next_line) - len(next_line.lstrip(" "))
            if next_indent <= indent:
                raise SpecError(f"{source}:{index+1}: key {key!r} missing nested block")
            if next_line.strip().startswith("-"):
                new_list2: List[Any] = []
                container[key] = new_list2
                stack.append((indent + 2, new_list2))
            else:
                new_dict3: Dict[str, Any] = {}
                container[key] = new_dict3
                stack.append((indent + 2, new_dict3))
            continue

        container[key] = _parse_scalar(rest)

    return root


def _require_keys(obj: Dict[str, Any], keys: Sequence[str], *, where: str) -> None:
    missing = [k for k in keys if k not in obj]
    if missing:
        raise SpecError(f"{where}: missing required keys: {', '.join(missing)}")


def _expect_type(value: Any, expected: type, *, where: str) -> None:
    if not isinstance(value, expected):
        raise SpecError(f"{where}: expected {expected.__name__}, got {type(value).__name__}")


def _fmt_hex(value: int, bits: int) -> str:
    width = (bits + 3) // 4
    return f"{value:#0{width+2}x}"


def _sv_hex(value: int, bits: int) -> str:
    width = (bits + 3) // 4
    return f"{bits}'h{value:0{width}x}"


def _c_hex_u32(value: int) -> str:
    return f"0x{value:08x}u"


def _md_escape(text: str) -> str:
    return str(text).replace("|", "\\|")


def _write_text_unix(path: Path, text: str) -> None:
    path.write_bytes(text.encode("utf-8"))


def _generation_timestamp() -> str:
    env = os.getenv("SOURCE_DATE_EPOCH")
    if env is not None:
        try:
            ts = datetime.fromtimestamp(int(env), tz=timezone.utc)
        except (ValueError, OverflowError):
            ts = datetime.now(timezone.utc)
    else:
        ts = datetime.now(timezone.utc)
    return ts.strftime("%Y-%m-%dT%H:%M:%SZ")


def _spec_revision_summary(specs: Dict[str, Dict[str, Any]]) -> str:
    parts = []
    for name in sorted(specs.keys()):
        rev = specs[name].get("revision", "unknown")
        parts.append(f"{name}:{rev}")
    return ", ".join(parts)


def _build_gen_info(specs: Dict[str, Dict[str, Any]]) -> Dict[str, str]:
    return {
        "timestamp": _generation_timestamp(),
        "spec_summary": _spec_revision_summary(specs),
    }


def _load_specs(spec_dir: Path) -> Dict[str, Dict[str, Any]]:
    required = [
        "tiers.yaml",
        "mode_switch.yaml",
        "profiles.yaml",
        "topology.yaml",
        "bdt.yaml",
        "memory_attrs.yaml",
        "external_if.yaml",
        "interfaces.yaml",
        "discovery.yaml",
        "csr_map.yaml",
        "device_model.yaml",
        "formats.yaml",
        "fabric.yaml",
        "cai.yaml",
        "isa_z90.yaml",
    ]
    specs: Dict[str, Dict[str, Any]] = {}
    for filename in required:
        path = spec_dir / filename
        if not path.exists():
            raise SpecError(f"Missing required spec: {path.as_posix()}")
        data = parse_yaml_subset(path.read_text(encoding="utf-8"), source=path.as_posix())
        _require_keys(
            data,
            ["spec_version", "name", "description", "revision", "created", "stable"],
            where=path.as_posix(),
        )
        if str(data["spec_version"]) != "1.0":
            raise SpecError(f"{path.as_posix()}: spec_version must be 1.0")
        if data["stable"] is not True:
            raise SpecError(f"{path.as_posix()}: stable must be true")
        specs[filename] = data
    return specs


def _validate_tiers(spec: Dict[str, Any]) -> None:
    where = "tiers.yaml"
    ladders = spec.get("ladders")
    _expect_type(ladders, list, where=f"{where}:ladders")
    if len(ladders) != 2:
        raise SpecError(f"{where}: expected exactly 2 ladders, got {len(ladders)}")
    ladder_values = set()
    ladder_ids = set()
    for ladder in ladders:
        _expect_type(ladder, dict, where=f"{where}:ladder")
        _require_keys(
            ladder,
            ["id", "value", "name", "tiers", "reset_default", "upgrade_rule", "downgrade_rule"],
            where=f"{where}:{ladder.get('id','<ladder>')}",
        )
        ladder_ids.add(ladder["id"])
        value = ladder["value"]
        if not isinstance(value, int) or value < 0 or value > 255:
            raise SpecError(f"{where}:{ladder['id']}: ladder value must be 0..255")
        if value in ladder_values:
            raise SpecError(f"{where}:{ladder['id']}: duplicate ladder value {value}")
        ladder_values.add(value)

        tiers = ladder["tiers"]
        _expect_type(tiers, list, where=f"{where}:{ladder['id']}:tiers")
        seen_tier_values = set()
        seen_ids = set()
        for t in tiers:
            _expect_type(t, dict, where=f"{where}:{ladder['id']}:tier")
            _require_keys(t, ["id", "value", "mnemonic", "label", "strict"], where=f"{where}:{ladder['id']}:tier")
            if t["id"] in seen_ids:
                raise SpecError(f"{where}:{ladder['id']}: duplicate tier id {t['id']}")
            seen_ids.add(t["id"])
            tv = t["value"]
            if not isinstance(tv, int) or tv < 0 or tv > 255:
                raise SpecError(f"{where}:{ladder['id']}:{t['id']}: tier value must be 0..255")
            if tv in seen_tier_values:
                raise SpecError(f"{where}:{ladder['id']}:{t['id']}: duplicate tier value {tv}")
            seen_tier_values.add(tv)

        if ladder["reset_default"] != "P0":
            raise SpecError(f"{where}:{ladder['id']}: reset_default must be P0")
        if "P0" not in seen_ids:
            raise SpecError(f"{where}:{ladder['id']}: must define P0")
        requires_p7 = ladder["id"] in ("TIER_LADDER_Z80",)
        if requires_p7 and "P7" not in seen_ids:
            raise SpecError(f"{where}:{ladder['id']}: must define P7")

    required_ladders = {"TIER_LADDER_Z80", "TIER_LADDER_AM95"}
    missing = sorted(required_ladders - ladder_ids)
    if missing:
        raise SpecError(f"{where}: missing required ladders: {', '.join(missing)}")


def _validate_mode_switch(spec: Dict[str, Any]) -> None:
    where = "mode_switch.yaml"
    instructions = spec.get("instructions")
    _expect_type(instructions, list, where=f"{where}:instructions")
    names = {i.get("name") for i in instructions if isinstance(i, dict)}
    if "MODEUP" not in names or "RETMD" not in names:
        raise SpecError(f"{where}: instructions must include MODEUP and RETMD")

    modeflags = spec.get("modeflags")
    _expect_type(modeflags, dict, where=f"{where}:modeflags")
    _require_keys(modeflags, ["width_bits", "bits", "reserved_bits"], where=f"{where}:modeflags")
    if not isinstance(modeflags["width_bits"], int) or modeflags["width_bits"] <= 0:
        raise SpecError(f"{where}:modeflags.width_bits must be a positive integer")
    bits = modeflags["bits"]
    _expect_type(bits, list, where=f"{where}:modeflags.bits")
    used = set()
    for b in bits:
        _expect_type(b, dict, where=f"{where}:modeflags.bits entry")
        _require_keys(b, ["name", "bit", "reset", "description"], where=f"{where}:modeflags.bits")
        bit = b["bit"]
        if not isinstance(bit, int) or bit < 0 or bit >= modeflags["width_bits"]:
            raise SpecError(f"{where}:modeflags.bits:{b['name']}: bit out of range")
        if bit in used:
            raise SpecError(f"{where}:modeflags.bits:{b['name']}: duplicate bit {bit}")
        used.add(bit)

    modestack = spec.get("modestack")
    _expect_type(modestack, dict, where=f"{where}:modestack")
    _require_keys(modestack, ["min_depth", "recommended_depth"], where=f"{where}:modestack")
    if modestack["min_depth"] != 4:
        raise SpecError(f"{where}:modestack.min_depth must be 4")
    if modestack["recommended_depth"] != 16:
        raise SpecError(f"{where}:modestack.recommended_depth must be 16")


def _validate_discovery(spec: Dict[str, Any]) -> None:
    where = "discovery.yaml"
    table = spec.get("discovery_table")
    _expect_type(table, dict, where=f"{where}:discovery_table")
    _require_keys(table, ["name", "version", "size_bytes", "fields"], where=f"{where}:discovery_table")
    _expect_type(table["fields"], list, where=f"{where}:discovery_table.fields")

    bitmaps = spec.get("feature_bitmaps")
    _expect_type(bitmaps, dict, where=f"{where}:feature_bitmaps")
    _require_keys(bitmaps, ["word_bits", "words"], where=f"{where}:feature_bitmaps")

    limits = spec.get("limits_table")
    _expect_type(limits, dict, where=f"{where}:limits_table")
    _require_keys(limits, ["name", "version", "size_bytes", "fields"], where=f"{where}:limits_table")
    _expect_type(limits["fields"], list, where=f"{where}:limits_table.fields")

    leafs = spec.get("leafs")
    _expect_type(leafs, list, where=f"{where}:leafs")
    leaf_ids = set()
    for leaf in leafs:
        _expect_type(leaf, dict, where=f"{where}:leaf")
        _require_keys(leaf, ["id", "name", "description"], where=f"{where}:leaf")
        lid = leaf["id"]
        if not isinstance(lid, int) or lid < 0 or lid > 0xFFFFFFFF:
            raise SpecError(f"{where}:{leaf['name']}: leaf id must be u32")
        if lid in leaf_ids:
            raise SpecError(f"{where}:{leaf['name']}: duplicate leaf id {_fmt_hex(lid, 32)}")
        leaf_ids.add(lid)

    feature_sets = spec.get("feature_sets")
    _expect_type(feature_sets, list, where=f"{where}:feature_sets")
    for fs in feature_sets:
        _expect_type(fs, dict, where=f"{where}:feature_set")
        _require_keys(fs, ["id", "leaf", "bits"], where=f"{where}:feature_set")
        bits = fs["bits"]
        _expect_type(bits, list, where=f"{where}:{fs['id']}:bits")
        seen = set()
        for bit in bits:
            _expect_type(bit, dict, where=f"{where}:{fs['id']}:bit")
            _require_keys(bit, ["name", "bit", "description"], where=f"{where}:{fs['id']}:bit")
            b = bit["bit"]
            if not isinstance(b, int) or b < 0 or b > 127:
                raise SpecError(f"{where}:{bit['name']}: feature bit must be 0..127")
            if b in seen:
                raise SpecError(f"{where}:{bit['name']}: duplicate feature bit {b}")
            seen.add(b)


def _validate_csr_map(spec: Dict[str, Any]) -> None:
    where = "csr_map.yaml"
    csrs = spec.get("csrs")
    _expect_type(csrs, list, where=f"{where}:csrs")
    required = {
        "CSR_ID",
        "CSR_TIER",
        "CSR_MODEFLAGS",
        "CSR_TIME",
        "CSR_CAUSE",
        "CSR_EPC",
        "CSR_IE",
        "CSR_IP",
        "CSR_TRACE_CTL",
    }
    present = set()
    addresses = set()
    for csr in csrs:
        _expect_type(csr, dict, where=f"{where}:csr")
        _require_keys(csr, ["name", "address", "access", "privilege_min"], where=f"{where}:csr")
        name = csr["name"]
        present.add(name)
        addr = csr["address"]
        if not isinstance(addr, int) or addr < 0 or addr > 0xFFFFFFFF:
            raise SpecError(f"{where}:{name}: address must be u32")
        if addr in addresses:
            raise SpecError(f"{where}:{name}: duplicate address {_fmt_hex(addr, 32)}")
        addresses.add(addr)
    missing = sorted(required - present)
    if missing:
        raise SpecError(f"{where}: missing required CSRs: {', '.join(missing)}")


def _validate_formats(spec: Dict[str, Any]) -> None:
    where = "formats.yaml"

    num = spec.get("numeric_formats")
    _expect_type(num, dict, where=f"{where}:numeric_formats")
    fmts = num.get("formats")
    _expect_type(fmts, list, where=f"{where}:numeric_formats.formats")

    seen_vals = set()
    for f in fmts:
        _expect_type(f, dict, where=f"{where}:numeric_formats.formats[]")
        _require_keys(
            f,
            ["name", "value", "width_bits", "exp_bits", "frac_bits", "bias", "description"],
            where=f"{where}:numeric_formats.formats[]",
        )
        v = f["value"]
        if not isinstance(v, int) or v < 0 or v > 255:
            raise SpecError(f"{where}:{f.get('name','<fmt>')}: value must be u8")
        if v in seen_vals:
            raise SpecError(f"{where}:{f.get('name','<fmt>')}: duplicate value {v}")
        seen_vals.add(v)

        width = int(f["width_bits"])
        exp = int(f["exp_bits"])
        frac = int(f["frac_bits"])
        if width != (1 + exp + frac):
            raise SpecError(
                f"{where}:{f['name']}: width_bits must equal 1+exp_bits+frac_bits"
            )

    rnd = spec.get("rounding_modes")
    _expect_type(rnd, dict, where=f"{where}:rounding_modes")
    modes = rnd.get("modes")
    _expect_type(modes, list, where=f"{where}:rounding_modes.modes")
    seen_rm = set()
    for m in modes:
        _expect_type(m, dict, where=f"{where}:rounding_modes.modes[]")
        _require_keys(
            m, ["name", "value", "mnemonic", "description"], where=f"{where}:rounding_modes.modes[]"
        )
        v = m["value"]
        if not isinstance(v, int) or v < 0 or v > 7:
            raise SpecError(f"{where}:{m.get('name','<rm>')}: value must be 0..7")
        if v in seen_rm:
            raise SpecError(f"{where}:{m.get('name','<rm>')}: duplicate value {v}")
        seen_rm.add(v)


def _validate_fabric(spec: Dict[str, Any]) -> None:
    where = "fabric.yaml"
    tx = spec.get("transaction_types")
    _expect_type(tx, list, where=f"{where}:transaction_types")
    attrs = spec.get("fabric_attributes")
    _expect_type(attrs, dict, where=f"{where}:fabric_attributes")
    _require_keys(attrs, ["width_bits", "fields"], where=f"{where}:fabric_attributes")
    _expect_type(attrs["fields"], list, where=f"{where}:fabric_attributes.fields")
    resp = spec.get("response_codes")
    _expect_type(resp, list, where=f"{where}:response_codes")


def _validate_cai(spec: Dict[str, Any]) -> None:
    where = "cai.yaml"
    for k in [
        "opcode_model",
        "submission_descriptor",
        "operand_descriptor",
        "tensor_descriptor",
        "completion_record",
        "completion_status_codes",
    ]:
        if k not in spec:
            raise SpecError(f"{where}: missing {k}")

    opcode_model = spec["opcode_model"]
    _expect_type(opcode_model, dict, where=f"{where}:opcode_model")
    _require_keys(opcode_model, ["opcode_groups"], where=f"{where}:opcode_model")
    groups = opcode_model["opcode_groups"]
    _expect_type(groups, list, where=f"{where}:opcode_model.opcode_groups")
    seen = set()
    for g in groups:
        _expect_type(g, dict, where=f"{where}:opcode_model.opcode_groups[]")
        _require_keys(g, ["name", "value", "description"], where=f"{where}:opcode_model.opcode_groups[]")
        v = g["value"]
        if not isinstance(v, int) or v < 0 or v > 255:
            raise SpecError(f"{where}:{g['name']}: opcode group value must be 0..255")
        if v in seen:
            raise SpecError(f"{where}:{g['name']}: duplicate opcode group value {v}")
        seen.add(v)

    for desc_key in ["submission_descriptor", "operand_descriptor", "tensor_descriptor", "completion_record"]:
        desc = spec[desc_key]
        _expect_type(desc, dict, where=f"{where}:{desc_key}")
        _require_keys(desc, ["name", "version", "size_bytes", "fields"], where=f"{where}:{desc_key}")
        _expect_type(desc["fields"], list, where=f"{where}:{desc_key}.fields")
    _expect_type(spec["completion_status_codes"], list, where=f"{where}:completion_status_codes")


def _validate_profiles(spec: Dict[str, Any]) -> None:
    where = "profiles.yaml"
    profiles = spec.get("profiles")
    _expect_type(profiles, list, where=f"{where}:profiles")
    required_ids = {
        "PROFILE_CPU_ONLY",
        "PROFILE_MCU",
        "PROFILE_SOC_RETRO",
        "PROFILE_SOC_WORKSTATION",
    }
    seen_ids = set()
    seen_values = set()
    for prof in profiles:
        _expect_type(prof, dict, where=f"{where}:profile")
        _require_keys(
            prof,
            [
                "id",
                "value",
                "name",
                "description",
                "required_blocks",
                "required_discovery_tables",
                "required_min_devices",
                "legacy_z80_bus_adapter",
                "safe_mode",
            ],
            where=f"{where}:{prof.get('id','<profile>')}",
        )
        pid = prof["id"]
        seen_ids.add(pid)
        value = prof["value"]
        if not isinstance(value, int) or value < 0 or value > 255:
            raise SpecError(f"{where}:{pid}: profile value must be 0..255")
        if value in seen_values:
            raise SpecError(f"{where}:{pid}: duplicate profile value {value}")
        seen_values.add(value)
        _expect_type(prof["required_blocks"], list, where=f"{where}:{pid}:required_blocks")
        _expect_type(
            prof["required_discovery_tables"],
            list,
            where=f"{where}:{pid}:required_discovery_tables",
        )
        _expect_type(prof["required_min_devices"], list, where=f"{where}:{pid}:required_min_devices")
        if not isinstance(prof["legacy_z80_bus_adapter"], bool):
            raise SpecError(f"{where}:{pid}: legacy_z80_bus_adapter must be bool")
        safe_mode = prof["safe_mode"]
        _expect_type(safe_mode, dict, where=f"{where}:{pid}:safe_mode")
        _require_keys(safe_mode, ["requirements"], where=f"{where}:{pid}:safe_mode")
        _expect_type(safe_mode["requirements"], list, where=f"{where}:{pid}:safe_mode.requirements")
    missing = sorted(required_ids - seen_ids)
    if missing:
        raise SpecError(f"{where}: missing required profiles: {', '.join(missing)}")


def _validate_topology(spec: Dict[str, Any]) -> None:
    where = "topology.yaml"
    topo = spec.get("topology_table")
    _expect_type(topo, dict, where=f"{where}:topology_table")
    _require_keys(topo, ["header", "entry"], where=f"{where}:topology_table")
    for key in ("header", "entry"):
        section = topo[key]
        _expect_type(section, dict, where=f"{where}:topology_table.{key}")
        _require_keys(section, ["name", "version", "size_bytes", "fields"], where=f"{where}:{key}")
        _expect_type(section["fields"], list, where=f"{where}:{key}.fields")


def _validate_bdt(spec: Dict[str, Any]) -> None:
    where = "bdt.yaml"
    for key in ("bdt_header", "bdt_entry", "irq_routing_table", "device_classes"):
        if key not in spec:
            raise SpecError(f"{where}: missing {key}")

    for key in ("bdt_header", "bdt_entry"):
        section = spec[key]
        _expect_type(section, dict, where=f"{where}:{key}")
        _require_keys(section, ["name", "version", "size_bytes", "fields"], where=f"{where}:{key}")
        _expect_type(section["fields"], list, where=f"{where}:{key}.fields")

    irq = spec["irq_routing_table"]
    _expect_type(irq, dict, where=f"{where}:irq_routing_table")
    _require_keys(irq, ["entry_size_bytes", "fields"], where=f"{where}:irq_routing_table")
    _expect_type(irq["fields"], list, where=f"{where}:irq_routing_table.fields")

    classes = spec["device_classes"]
    _expect_type(classes, dict, where=f"{where}:device_classes")
    _require_keys(classes, ["classes"], where=f"{where}:device_classes")
    _expect_type(classes["classes"], list, where=f"{where}:device_classes.classes")
    seen_class_vals = set()
    seen_class_names = set()
    for c in classes["classes"]:
        _expect_type(c, dict, where=f"{where}:device_classes.classes[]")
        _require_keys(c, ["name", "value", "description"], where=f"{where}:device_classes.classes[]")
        name = c["name"]
        seen_class_names.add(name)
        v = c["value"]
        if not isinstance(v, int) or v < 0 or v > 0xFFFF:
            raise SpecError(f"{where}:{name}: class value must be u16")
        if v in seen_class_vals:
            raise SpecError(f"{where}:{name}: duplicate class value {v}")
        seen_class_vals.add(v)
    required_classes = {
        "DEVCLASS_UART",
        "DEVCLASS_TIMER",
        "DEVCLASS_PIO",
        "DEVCLASS_PIC",
        "DEVCLASS_DMA",
        "DEVCLASS_STORAGE",
        "DEVCLASS_ACCEL",
    }
    missing = sorted(required_classes - seen_class_names)
    if missing:
        raise SpecError(f"{where}: missing required device classes: {', '.join(missing)}")


def _validate_memory_attrs(spec: Dict[str, Any]) -> None:
    where = "memory_attrs.yaml"
    attrs = spec.get("attributes")
    _expect_type(attrs, dict, where=f"{where}:attributes")
    _require_keys(attrs, ["width_bits", "fields"], where=f"{where}:attributes")
    width = attrs["width_bits"]
    if not isinstance(width, int) or width <= 0:
        raise SpecError(f"{where}:attributes.width_bits must be positive")
    fields = attrs["fields"]
    _expect_type(fields, list, where=f"{where}:attributes.fields")
    seen_bits = set()
    for f in fields:
        _expect_type(f, dict, where=f"{where}:attributes.fields[]")
        _require_keys(f, ["name", "bit", "description"], where=f"{where}:attributes.fields[]")
        bit = f["bit"]
        if not isinstance(bit, int) or bit < 0 or bit >= width:
            raise SpecError(f"{where}:{f['name']}: bit out of range")
        if bit in seen_bits:
            raise SpecError(f"{where}:{f['name']}: duplicate bit {bit}")
        seen_bits.add(bit)


def _validate_external_if(spec: Dict[str, Any]) -> None:
    where = "external_if.yaml"
    legacy = spec.get("legacy_z80_bus_adapter")
    _expect_type(legacy, dict, where=f"{where}:legacy_z80_bus_adapter")
    _require_keys(legacy, ["profiles"], where=f"{where}:legacy_z80_bus_adapter")
    _expect_type(legacy["profiles"], list, where=f"{where}:legacy_z80_bus_adapter.profiles")

    modern = spec.get("modern_soc_external")
    _expect_type(modern, dict, where=f"{where}:modern_soc_external")
    _require_keys(modern, ["profiles"], where=f"{where}:modern_soc_external")
    _expect_type(modern["profiles"], list, where=f"{where}:modern_soc_external.profiles")

    dbg = spec.get("debug_transport")
    _expect_type(dbg, dict, where=f"{where}:debug_transport")
    _require_keys(dbg, ["minimum"], where=f"{where}:debug_transport")


def _validate_interfaces(spec: Dict[str, Any]) -> None:
    where = "interfaces.yaml"
    interfaces = spec.get("interfaces")
    _expect_type(interfaces, list, where=f"{where}:interfaces")
    required_names = {"fabric_if", "csr_if", "irq_if", "dbg_if", "cai_if"}
    seen_names = set()
    seen_values = set()
    for iface in interfaces:
        _expect_type(iface, dict, where=f"{where}:interfaces[]")
        _require_keys(iface, ["name", "value", "description"], where=f"{where}:interfaces[]")
        name = iface["name"]
        seen_names.add(name)
        value = iface["value"]
        if not isinstance(value, int) or value < 0 or value > 255:
            raise SpecError(f"{where}:{name}: interface value must be 0..255")
        if value in seen_values:
            raise SpecError(f"{where}:{name}: duplicate interface value {value}")
        seen_values.add(value)
    missing = sorted(required_names - seen_names)
    if missing:
        raise SpecError(f"{where}: missing required interfaces: {', '.join(missing)}")


def _validate_device_model(spec: Dict[str, Any]) -> None:
    where = "device_model.yaml"

    for k in [
        "device_classes",
        "device_capability_descriptor",
        "bdt_header",
        "compat_feature_bits",
        "turbo_feature_bits",
        "feature_fields",
        "device_csr_common",
        "turbo_submission_descriptor",
        "turbo_completion_record",
        "turbo_completion_status_codes",
    ]:
        if k not in spec:
            raise SpecError(f"{where}: missing {k}")

    classes = spec["device_classes"]
    _expect_type(classes, dict, where=f"{where}:device_classes")
    _require_keys(classes, ["classes"], where=f"{where}:device_classes")
    _expect_type(classes["classes"], list, where=f"{where}:device_classes.classes")
    seen_class_vals = set()
    for c in classes["classes"]:
        _expect_type(c, dict, where=f"{where}:device_classes.classes[]")
        _require_keys(c, ["name", "value", "description"], where=f"{where}:device_classes.classes[]")
        v = c["value"]
        if not isinstance(v, int) or v < 0 or v > 0xFFFF:
            raise SpecError(f"{where}:{c['name']}: class value must be u16")
        if v in seen_class_vals:
            raise SpecError(f"{where}:{c['name']}: duplicate class value {v}")
        seen_class_vals.add(v)

    for desc_key in ["bdt_header", "device_capability_descriptor", "turbo_submission_descriptor", "turbo_completion_record"]:
        desc = spec[desc_key]
        _expect_type(desc, dict, where=f"{where}:{desc_key}")
        _require_keys(desc, ["name", "version", "size_bytes", "fields"], where=f"{where}:{desc_key}")
        _expect_type(desc["fields"], list, where=f"{where}:{desc_key}.fields")

    for bit_key in ["compat_feature_bits", "turbo_feature_bits"]:
        bits = spec[bit_key]
        _expect_type(bits, dict, where=f"{where}:{bit_key}")
        _require_keys(bits, ["bits"], where=f"{where}:{bit_key}")
        _expect_type(bits["bits"], list, where=f"{where}:{bit_key}.bits")
        seen = set()
        for b in bits["bits"]:
            _expect_type(b, dict, where=f"{where}:{bit_key}.bits[]")
            _require_keys(b, ["name", "bit", "description"], where=f"{where}:{bit_key}.bits[]")
            bit = b["bit"]
            if not isinstance(bit, int) or bit < 0 or bit > 31:
                raise SpecError(f"{where}:{b['name']}: feature bit must be 0..31")
            if bit in seen:
                raise SpecError(f"{where}:{b['name']}: duplicate feature bit {bit}")
            seen.add(bit)

    fields = spec["feature_fields"]
    _expect_type(fields, dict, where=f"{where}:feature_fields")
    _require_keys(fields, ["fields"], where=f"{where}:feature_fields")
    _expect_type(fields["fields"], list, where=f"{where}:feature_fields.fields")
    for f in fields["fields"]:
        _expect_type(f, dict, where=f"{where}:feature_fields.fields[]")
        _require_keys(f, ["name", "word", "bits", "description"], where=f"{where}:feature_fields.fields[]")
        word = f["word"]
        if not isinstance(word, int) or word < 0 or word > 3:
            raise SpecError(f"{where}:{f['name']}: word must be 0..3")
        bits = f["bits"]
        if not isinstance(bits, list) or len(bits) != 2:
            raise SpecError(f"{where}:{f['name']}: bits must be [msb, lsb]")
        msb = bits[0]
        lsb = bits[1]
        if not isinstance(msb, int) or not isinstance(lsb, int) or msb < lsb:
            raise SpecError(f"{where}:{f['name']}: invalid bit range")

    devcsr = spec["device_csr_common"]
    _expect_type(devcsr, dict, where=f"{where}:device_csr_common")
    _require_keys(devcsr, ["registers"], where=f"{where}:device_csr_common")
    _expect_type(devcsr["registers"], list, where=f"{where}:device_csr_common.registers")
    seen_reg = set()
    for r in devcsr["registers"]:
        _expect_type(r, dict, where=f"{where}:device_csr_common.registers[]")
        _require_keys(r, ["name", "reg_id", "access", "description"], where=f"{where}:device_csr_common.registers[]")
        reg_id = r["reg_id"]
        if not isinstance(reg_id, int) or reg_id < 0 or reg_id > 0xFFF:
            raise SpecError(f"{where}:{r['name']}: reg_id must be 0..0xFFF")
        if reg_id in seen_reg:
            raise SpecError(f"{where}:{r['name']}: duplicate reg_id {reg_id}")
        seen_reg.add(reg_id)

    codes = spec["turbo_completion_status_codes"]
    _expect_type(codes, list, where=f"{where}:turbo_completion_status_codes")
    for c in codes:
        _expect_type(c, dict, where=f"{where}:turbo_completion_status_codes[]")
        _require_keys(c, ["name", "value", "description"], where=f"{where}:turbo_completion_status_codes[]")


def _validate_isa_z90(spec: Dict[str, Any]) -> None:
    where = "isa_z90.yaml"
    pages = spec.get("opcode_pages")
    _expect_type(pages, list, where=f"{where}:opcode_pages")
    for p in pages:
        _expect_type(p, dict, where=f"{where}:opcode_pages[]")
        _require_keys(p, ["name", "prefix_bytes", "description"], where=f"{where}:opcode_pages[]")
        _expect_type(p["prefix_bytes"], list, where=f"{where}:{p.get('name','<page>')}.prefix_bytes")
        if len(p["prefix_bytes"]) != 2:
            raise SpecError(f"{where}: {p['name']}: prefix_bytes must have length 2")

    majors = spec.get("page0_majors")
    _expect_type(majors, list, where=f"{where}:page0_majors")
    for m in majors:
        _expect_type(m, dict, where=f"{where}:page0_majors[]")
        _require_keys(m, ["name", "value", "description"], where=f"{where}:page0_majors[]")

    subops = spec.get("page0_subops")
    _expect_type(subops, list, where=f"{where}:page0_subops")
    for s in subops:
        _expect_type(s, dict, where=f"{where}:page0_subops[]")
        _require_keys(s, ["name", "major", "value", "description"], where=f"{where}:page0_subops[]")

    p1 = spec.get("page1_ops")
    _expect_type(p1, list, where=f"{where}:page1_ops")
    for o in p1:
        _expect_type(o, dict, where=f"{where}:page1_ops[]")
        _require_keys(o, ["name", "value", "description"], where=f"{where}:page1_ops[]")


def _validate_specs(specs: Dict[str, Dict[str, Any]]) -> None:
    _validate_tiers(specs["tiers.yaml"])
    _validate_mode_switch(specs["mode_switch.yaml"])
    _validate_profiles(specs["profiles.yaml"])
    _validate_topology(specs["topology.yaml"])
    _validate_bdt(specs["bdt.yaml"])
    _validate_memory_attrs(specs["memory_attrs.yaml"])
    _validate_external_if(specs["external_if.yaml"])
    _validate_interfaces(specs["interfaces.yaml"])
    _validate_discovery(specs["discovery.yaml"])
    _validate_csr_map(specs["csr_map.yaml"])
    _validate_device_model(specs["device_model.yaml"])
    _validate_formats(specs["formats.yaml"])
    _validate_fabric(specs["fabric.yaml"])
    _validate_cai(specs["cai.yaml"])
    _validate_isa_z90(specs["isa_z90.yaml"])


def _emit_sv(specs: Dict[str, Dict[str, Any]], gen_info: Dict[str, str]) -> str:
    tiers = specs["tiers.yaml"]
    mode = specs["mode_switch.yaml"]
    profiles = specs["profiles.yaml"]
    topology = specs["topology.yaml"]
    bdt_spec = specs["bdt.yaml"]
    mem_attrs = specs["memory_attrs.yaml"]
    external_if = specs["external_if.yaml"]
    interfaces = specs["interfaces.yaml"]
    disc = specs["discovery.yaml"]
    csr = specs["csr_map.yaml"]
    dev = specs["device_model.yaml"]
    formats = specs["formats.yaml"]
    fabric = specs["fabric.yaml"]
    cai = specs["cai.yaml"]
    isa_z90 = specs["isa_z90.yaml"]

    out: List[str] = []
    out.append("// GENERATED FILE — DO NOT EDIT.")
    out.append(f"// Specs: {gen_info['spec_summary']}")
    out.append(f"// Generated: {gen_info['timestamp']}")
    out.append("// Source: hdl/tools/gen_specs.py")
    out.append("")
    out.append("package carbon_arch_pkg;")
    out.append("")

    out.append("  // Tier ladder identifiers")
    for ladder in tiers["ladders"]:
        out.append(f"  localparam int unsigned CARBON_{ladder['id']} = {ladder['value']};")
    out.append("")

    out.append("  // Tier enums")
    for ladder in tiers["ladders"]:
        ladder_name = str(ladder["name"]).upper()
        enum_name = f"carbon_{ladder['name']}_tier_e"
        out.append("  typedef enum logic [7:0] {")
        entries: List[str] = []
        tier_by_value = {int(t["value"]): t for t in ladder["tiers"]}
        for value in range(16):
            tier = tier_by_value.get(value)
            if tier is None:
                tid = f"P{value}"
                mnemonic = "RESERVED"
            else:
                tid = tier["id"]
                mnemonic = tier["mnemonic"]
            entries.append(f"    CARBON_{ladder_name}_TIER_{tid}_{mnemonic} = 8'd{value}")
        out.append(",\n".join(entries))
        out.append(f"  }} {enum_name};")
        out.append("")

    out.append("  // Profile identifiers")
    for prof in profiles["profiles"]:
        out.append(f"  localparam int unsigned CARBON_{prof['id']} = {int(prof['value'])};")
    out.append("")

    out.append("  // MODEFLAGS")
    modeflags = mode["modeflags"]
    mf_width = int(modeflags["width_bits"])
    out.append(f"  localparam int unsigned CARBON_MODEFLAGS_WIDTH_BITS = {mf_width};")
    for bit in modeflags["bits"]:
        bit_name = bit["name"]
        b = int(bit["bit"])
        mask = 1 << b
        out.append(f"  localparam int unsigned CARBON_{bit_name}_BIT = {b};")
        out.append(
            f"  localparam logic [{mf_width-1}:0] CARBON_{bit_name}_MASK = {_sv_hex(mask, mf_width)};"
        )
    out.append("")
    out.append("  // MODESTACK depth requirements")
    out.append(f"  localparam int unsigned CARBON_MODESTACK_MIN_DEPTH = {mode['modestack']['min_depth']};")
    out.append(
        f"  localparam int unsigned CARBON_MODESTACK_RECOMMENDED_DEPTH = {mode['modestack']['recommended_depth']};"
    )
    out.append("")

    out.append("  // Memory attribute bits")
    mem = mem_attrs["attributes"]
    mem_width = int(mem["width_bits"])
    out.append(f"  localparam int unsigned CARBON_MEM_ATTR_WIDTH_BITS = {mem_width};")
    for field in mem["fields"]:
        name = field["name"]
        bit = int(field["bit"])
        mask = 1 << bit
        out.append(f"  localparam int unsigned CARBON_{name}_BIT = {bit};")
        out.append(
            f"  localparam logic [{mem_width-1}:0] CARBON_{name}_BIT_MASK = {_sv_hex(mask, mem_width)};"
        )
    out.append("")

    out.append("  // Interface identifiers")
    for iface in interfaces["interfaces"]:
        name = str(iface["name"]).upper()
        out.append(f"  localparam int unsigned CARBON_{name} = {int(iface['value'])};")
    out.append("")

    out.append("  // External interface profiles")
    for profile in external_if["legacy_z80_bus_adapter"]["profiles"]:
        out.append(
            f"  localparam int unsigned CARBON_EXTIF_{profile['name']} = {int(profile['value'])};"
        )
    for profile in external_if["modern_soc_external"]["profiles"]:
        out.append(
            f"  localparam int unsigned CARBON_EXTIF_{profile['name']} = {int(profile['value'])};"
        )
    out.append("")

    out.append("  // Numeric format identifiers")
    for f in formats["numeric_formats"]["formats"]:
        name = f["name"]
        out.append(f"  localparam int unsigned CARBON_{name} = {int(f['value'])};")
        out.append(f"  localparam int unsigned CARBON_{name}_WIDTH_BITS = {int(f['width_bits'])};")
        out.append(f"  localparam int unsigned CARBON_{name}_EXP_BITS = {int(f['exp_bits'])};")
        out.append(f"  localparam int unsigned CARBON_{name}_FRAC_BITS = {int(f['frac_bits'])};")
        out.append(f"  localparam int unsigned CARBON_{name}_BIAS = {int(f['bias'])};")
    out.append("")

    out.append("  // IEEE rounding modes")
    for rm in formats["rounding_modes"]["modes"]:
        out.append(f"  localparam int unsigned CARBON_{rm['name']} = {int(rm['value'])};")
    out.append("")

    out.append("  // CPUID leaf identifiers")
    for leaf in disc["leafs"]:
        out.append(f"  localparam int unsigned CARBON_{leaf['name']} = {_sv_hex(leaf['id'], 32)};")
    out.append("")

    out.append("  // Discovery table")
    disc_table = disc["discovery_table"]
    out.append(f"  localparam int unsigned CARBON_{disc_table['name']}_VERSION = {int(disc_table['version'])};")
    out.append(f"  localparam int unsigned CARBON_{disc_table['name']}_SIZE_BYTES = {int(disc_table['size_bytes'])};")
    if "pointer_model" in disc_table and isinstance(disc_table["pointer_model"], dict):
        ptr_bits = disc_table["pointer_model"].get("pointer_width_bits")
        if isinstance(ptr_bits, int):
            out.append(f"  localparam int unsigned CARBON_{disc_table['name']}_POINTER_BITS = {ptr_bits};")
    for f in disc_table["fields"]:
        out.append(
            f"  localparam int unsigned CARBON_{disc_table['name']}_OFF_{str(f['name']).upper()} = {f['offset']};"
        )
    out.append("")

    out.append("  // Feature bitmap format")
    bitmaps = disc["feature_bitmaps"]
    out.append(f"  localparam int unsigned CARBON_FEATURE_BITMAP_WORD_BITS = {int(bitmaps['word_bits'])};")
    out.append(f"  localparam int unsigned CARBON_FEATURE_BITMAP_WORDS = {int(bitmaps['words'])};")
    out.append("")

    out.append("  // Limits table")
    limits = disc["limits_table"]
    out.append(f"  localparam int unsigned CARBON_{limits['name']}_VERSION = {int(limits['version'])};")
    out.append(f"  localparam int unsigned CARBON_{limits['name']}_SIZE_BYTES = {int(limits['size_bytes'])};")
    for f in limits["fields"]:
        out.append(
            f"  localparam int unsigned CARBON_{limits['name']}_OFF_{str(f['name']).upper()} = {f['offset']};"
        )
    out.append("")

    out.append("  // Feature bit identifiers")
    for fs in disc["feature_sets"]:
        out.append(f"  // {fs['id']}")
        for feat in fs["bits"]:
            name = feat["name"]
            bit = int(feat["bit"])
            word = bit // 32
            bit_in_word = bit % 32
            out.append(f"  localparam int unsigned CARBON_{name}_BIT = {bit};")
            out.append(f"  localparam int unsigned CARBON_{name}_WORD = {word};")
            out.append(f"  localparam logic [31:0] CARBON_{name}_MASK = (32'h1 << {bit_in_word});")
        out.append("")

    out.append("  // Topology table")
    topo = topology["topology_table"]
    topo_hdr = topo["header"]
    topo_ent = topo["entry"]
    out.append(f"  localparam int unsigned CARBON_{topo_hdr['name']}_VERSION = {int(topo_hdr['version'])};")
    out.append(f"  localparam int unsigned CARBON_{topo_hdr['name']}_SIZE_BYTES = {int(topo_hdr['size_bytes'])};")
    for f in topo_hdr["fields"]:
        out.append(
            f"  localparam int unsigned CARBON_{topo_hdr['name']}_OFF_{str(f['name']).upper()} = {f['offset']};"
        )
    out.append(f"  localparam int unsigned CARBON_{topo_ent['name']}_VERSION = {int(topo_ent['version'])};")
    out.append(f"  localparam int unsigned CARBON_{topo_ent['name']}_SIZE_BYTES = {int(topo_ent['size_bytes'])};")
    for f in topo_ent["fields"]:
        out.append(
            f"  localparam int unsigned CARBON_{topo_ent['name']}_OFF_{str(f['name']).upper()} = {f['offset']};"
        )
    out.append("")

    out.append("  // CSR addresses")
    for reg in csr["csrs"]:
        out.append(f"  localparam int unsigned CARBON_{reg['name']} = {_sv_hex(reg['address'], 32)};")
    out.append("")

    out.append("  // Fabric transaction types")
    for t in fabric["transaction_types"]:
        out.append(f"  localparam int unsigned CARBON_{t['name']} = {t['value']};")
    out.append("")

    out.append("  // Fabric attribute fields")
    attrs = fabric["fabric_attributes"]
    attr_width = int(attrs["width_bits"])
    out.append(f"  localparam int unsigned CARBON_FABRIC_ATTR_WIDTH_BITS = {attr_width};")
    for field in attrs["fields"]:
        fname = field["name"]
        lsb = int(field["lsb"])
        width = int(field["width"])
        mask = ((1 << width) - 1) << lsb
        out.append(f"  localparam int unsigned CARBON_{fname}_LSB = {lsb};")
        out.append(f"  localparam int unsigned CARBON_{fname}_WIDTH = {width};")
        out.append(
            f"  localparam logic [{attr_width-1}:0] CARBON_{fname}_MASK = {_sv_hex(mask, attr_width)};"
        )
    out.append("")

    out.append("  // Fabric response codes")
    for rc in fabric["response_codes"]:
        out.append(f"  localparam int unsigned CARBON_{rc['name']} = {rc['value']};")
    out.append("")

    out.append("  // CAI opcode groups")
    for group in cai["opcode_model"]["opcode_groups"]:
        out.append(f"  localparam int unsigned CARBON_{group['name']} = {int(group['value'])};")
    out.append("")

    out.append("  // CAI descriptor formats")
    submit = cai["submission_descriptor"]
    out.append(f"  localparam int unsigned CARBON_{submit['name']}_VERSION = {submit['version']};")
    out.append(f"  localparam int unsigned CARBON_{submit['name']}_SIZE_BYTES = {submit['size_bytes']};")
    for f in submit["fields"]:
        out.append(
            f"  localparam int unsigned CARBON_{submit['name']}_OFF_{str(f['name']).upper()} = {f['offset']};"
        )
    out.append("")

    opdesc = cai["operand_descriptor"]
    out.append(f"  localparam int unsigned CARBON_{opdesc['name']}_VERSION = {opdesc['version']};")
    out.append(f"  localparam int unsigned CARBON_{opdesc['name']}_SIZE_BYTES = {opdesc['size_bytes']};")
    for f in opdesc["fields"]:
        out.append(
            f"  localparam int unsigned CARBON_{opdesc['name']}_OFF_{str(f['name']).upper()} = {f['offset']};"
        )
    out.append("")

    tdesc = cai["tensor_descriptor"]
    out.append(f"  localparam int unsigned CARBON_{tdesc['name']}_VERSION = {tdesc['version']};")
    out.append(f"  localparam int unsigned CARBON_{tdesc['name']}_SIZE_BYTES = {tdesc['size_bytes']};")
    for f in tdesc["fields"]:
        out.append(
            f"  localparam int unsigned CARBON_{tdesc['name']}_OFF_{str(f['name']).upper()} = {f['offset']};"
        )
    out.append("")

    comp = cai["completion_record"]
    out.append(f"  localparam int unsigned CARBON_{comp['name']}_VERSION = {comp['version']};")
    out.append(f"  localparam int unsigned CARBON_{comp['name']}_SIZE_BYTES = {comp['size_bytes']};")
    for f in comp["fields"]:
        out.append(
            f"  localparam int unsigned CARBON_{comp['name']}_OFF_{str(f['name']).upper()} = {f['offset']};"
        )
    out.append("")

    out.append("  // CAI completion status codes")
    for s in cai["completion_status_codes"]:
        out.append(f"  localparam int unsigned CARBON_{s['name']} = {s['value']};")
    out.append("")

    out.append("  // Device class identifiers")
    for c in bdt_spec["device_classes"]["classes"]:
        out.append(f"  localparam int unsigned CARBON_{c['name']} = {int(c['value'])};")
    out.append("")

    out.append("  // Board Device Table (BDT) header")
    bdt = bdt_spec["bdt_header"]
    out.append(f"  localparam int unsigned CARBON_{bdt['name']}_VERSION = {bdt['version']};")
    out.append(f"  localparam int unsigned CARBON_{bdt['name']}_SIZE_BYTES = {bdt['size_bytes']};")
    for f in bdt["fields"]:
        out.append(
            f"  localparam int unsigned CARBON_{bdt['name']}_OFF_{str(f['name']).upper()} = {f['offset']};"
        )
    out.append("")

    out.append("  // Board Device Table (BDT) entry")
    bdt_entry = bdt_spec["bdt_entry"]
    out.append(f"  localparam int unsigned CARBON_{bdt_entry['name']}_VERSION = {bdt_entry['version']};")
    out.append(f"  localparam int unsigned CARBON_{bdt_entry['name']}_SIZE_BYTES = {bdt_entry['size_bytes']};")
    for f in bdt_entry["fields"]:
        out.append(
            f"  localparam int unsigned CARBON_{bdt_entry['name']}_OFF_{str(f['name']).upper()} = {f['offset']};"
        )
    out.append("")

    out.append("  // BDT IRQ routing entries")
    irq = bdt_spec["irq_routing_table"]
    out.append(f"  localparam int unsigned CARBON_{irq['name']}_ENTRY_SIZE_BYTES = {int(irq['entry_size_bytes'])};")
    for f in irq["fields"]:
        out.append(
            f"  localparam int unsigned CARBON_{irq['name']}_OFF_{str(f['name']).upper()} = {f['offset']};"
        )
    out.append("")

    out.append("  // Device capability descriptor")
    dcd = dev["device_capability_descriptor"]
    out.append(f"  localparam int unsigned CARBON_{dcd['name']}_VERSION = {dcd['version']};")
    out.append(f"  localparam int unsigned CARBON_{dcd['name']}_SIZE_BYTES = {dcd['size_bytes']};")
    for f in dcd["fields"]:
        out.append(
            f"  localparam int unsigned CARBON_{dcd['name']}_OFF_{str(f['name']).upper()} = {f['offset']};"
        )
    out.append("")

    out.append("  // Device compatibility feature bits")
    for feat in dev["compat_feature_bits"]["bits"]:
        b = int(feat["bit"])
        out.append(f"  localparam int unsigned CARBON_{feat['name']}_BIT = {b};")
        out.append(f"  localparam logic [31:0] CARBON_{feat['name']}_MASK = 32'h{1 << b:08x};")
    out.append("")

    out.append("  // Device turbo feature bits")
    for feat in dev["turbo_feature_bits"]["bits"]:
        b = int(feat["bit"])
        out.append(f"  localparam int unsigned CARBON_{feat['name']}_BIT = {b};")
        out.append(f"  localparam logic [31:0] CARBON_{feat['name']}_MASK = 32'h{1 << b:08x};")
    out.append("")

    out.append("  // Device feature field positions")
    for f in dev["feature_fields"]["fields"]:
        msb = int(f["bits"][0])
        lsb = int(f["bits"][1])
        width = msb - lsb + 1
        mask = ((1 << width) - 1) << lsb
        out.append(f"  localparam int unsigned CARBON_{f['name']}_WORD = {int(f['word'])};")
        out.append(f"  localparam int unsigned CARBON_{f['name']}_LSB = {lsb};")
        out.append(f"  localparam int unsigned CARBON_{f['name']}_WIDTH = {width};")
        out.append(f"  localparam logic [31:0] CARBON_{f['name']}_MASK = 32'h{mask:08x};")
    out.append("")

    out.append("  // Device common CSR register IDs")
    for r in dev["device_csr_common"]["registers"]:
        out.append(f"  localparam int unsigned CARBON_{r['name']} = {int(r['reg_id'])};")
    out.append("")

    out.append("  // Turbo queue descriptor formats")
    tdesc = dev["turbo_submission_descriptor"]
    out.append(f"  localparam int unsigned CARBON_{tdesc['name']}_VERSION = {tdesc['version']};")
    out.append(f"  localparam int unsigned CARBON_{tdesc['name']}_SIZE_BYTES = {tdesc['size_bytes']};")
    for f in tdesc["fields"]:
        out.append(
            f"  localparam int unsigned CARBON_{tdesc['name']}_OFF_{str(f['name']).upper()} = {f['offset']};"
        )
    out.append("")

    tcomp = dev["turbo_completion_record"]
    out.append(f"  localparam int unsigned CARBON_{tcomp['name']}_VERSION = {tcomp['version']};")
    out.append(f"  localparam int unsigned CARBON_{tcomp['name']}_SIZE_BYTES = {tcomp['size_bytes']};")
    for f in tcomp["fields"]:
        out.append(
            f"  localparam int unsigned CARBON_{tcomp['name']}_OFF_{str(f['name']).upper()} = {f['offset']};"
        )
    out.append("")

    out.append("  // Turbo queue completion status codes")
    for s in dev["turbo_completion_status_codes"]:
        out.append(f"  localparam int unsigned CARBON_{s['name']} = {s['value']};")
    out.append("")

    out.append("  // Z90 opcode pages and encodings")
    out.append("  // Opcode page prefixes")
    for page in isa_z90["opcode_pages"]:
        pfx = page["prefix_bytes"]
        out.append(
            f"  localparam logic [7:0] CARBON_{page['name']}_PREFIX0 = {_sv_hex(int(pfx[0]), 8)};"
        )
        out.append(
            f"  localparam logic [7:0] CARBON_{page['name']}_PREFIX1 = {_sv_hex(int(pfx[1]), 8)};"
        )
    out.append("")

    out.append("  // Page0 majors")
    for m in isa_z90["page0_majors"]:
        out.append(f"  localparam int unsigned CARBON_{m['name']} = {int(m['value'])};")
    out.append("")

    out.append("  // Page0 subops")
    for s in isa_z90["page0_subops"]:
        out.append(f"  localparam int unsigned CARBON_{s['name']} = {int(s['value'])};")
    out.append("")

    out.append("  // Page1 ops")
    for o in isa_z90["page1_ops"]:
        out.append(f"  localparam int unsigned CARBON_{o['name']} = {int(o['value'])};")
    out.append("")

    out.append("endpackage : carbon_arch_pkg")
    return "\n".join(out)


def _emit_c_header(specs: Dict[str, Dict[str, Any]], gen_info: Dict[str, str]) -> str:
    tiers = specs["tiers.yaml"]
    mode = specs["mode_switch.yaml"]
    profiles = specs["profiles.yaml"]
    topology = specs["topology.yaml"]
    bdt_spec = specs["bdt.yaml"]
    mem_attrs = specs["memory_attrs.yaml"]
    external_if = specs["external_if.yaml"]
    interfaces = specs["interfaces.yaml"]
    disc = specs["discovery.yaml"]
    csr = specs["csr_map.yaml"]
    dev = specs["device_model.yaml"]
    formats = specs["formats.yaml"]
    fabric = specs["fabric.yaml"]
    cai = specs["cai.yaml"]
    isa_z90 = specs["isa_z90.yaml"]

    out: List[str] = []
    out.append("/* GENERATED FILE — DO NOT EDIT. */")
    out.append(f"/* Specs: {gen_info['spec_summary']} */")
    out.append(f"/* Generated: {gen_info['timestamp']} */")
    out.append("/* Source: hdl/tools/gen_specs.py */")
    out.append("#pragma once")
    out.append("")
    out.append("#include <stdint.h>")
    out.append("")

    out.append("/* Tier ladder identifiers */")
    for ladder in tiers["ladders"]:
        out.append(f"#define CARBON_{ladder['id']} ({ladder['value']}u)")
    out.append("")

    out.append("/* Tier values */")
    for ladder in tiers["ladders"]:
        lname = str(ladder["name"]).upper()
        tier_by_value = {int(t["value"]): t for t in ladder["tiers"]}
        for value in range(16):
            tier = tier_by_value.get(value)
            if tier is None:
                tid = f"P{value}"
                mnemonic = "RESERVED"
            else:
                tid = tier["id"]
                mnemonic = tier["mnemonic"]
            out.append(f"#define CARBON_{lname}_TIER_{tid}_{mnemonic} ({value}u)")
    out.append("")

    out.append("/* Profile identifiers */")
    for prof in profiles["profiles"]:
        out.append(f"#define CARBON_{prof['id']} ({int(prof['value'])}u)")
    out.append("")

    out.append("/* MODEFLAGS */")
    modeflags = mode["modeflags"]
    mf_width = int(modeflags["width_bits"])
    out.append(f"#define CARBON_MODEFLAGS_WIDTH_BITS ({mf_width}u)")
    for bit in modeflags["bits"]:
        bit_name = bit["name"]
        b = int(bit["bit"])
        out.append(f"#define CARBON_{bit_name}_BIT ({b}u)")
        out.append(f"#define CARBON_{bit_name}_MASK (UINT32_C(1) << {b})")
    out.append(f"#define CARBON_MODESTACK_MIN_DEPTH ({mode['modestack']['min_depth']}u)")
    out.append(f"#define CARBON_MODESTACK_RECOMMENDED_DEPTH ({mode['modestack']['recommended_depth']}u)")
    out.append("")

    out.append("/* Memory attribute bits */")
    mem = mem_attrs["attributes"]
    mem_width = int(mem["width_bits"])
    out.append(f"#define CARBON_MEM_ATTR_WIDTH_BITS ({mem_width}u)")
    for field in mem["fields"]:
        name = field["name"]
        bit = int(field["bit"])
        out.append(f"#define CARBON_{name}_BIT ({bit}u)")
        out.append(f"#define CARBON_{name}_BIT_MASK (UINT32_C(1) << {bit})")
    out.append("")

    out.append("/* Interface identifiers */")
    for iface in interfaces["interfaces"]:
        name = str(iface["name"]).upper()
        out.append(f"#define CARBON_{name} ({int(iface['value'])}u)")
    out.append("")

    out.append("/* External interface profiles */")
    for profile in external_if["legacy_z80_bus_adapter"]["profiles"]:
        out.append(f"#define CARBON_EXTIF_{profile['name']} ({int(profile['value'])}u)")
    for profile in external_if["modern_soc_external"]["profiles"]:
        out.append(f"#define CARBON_EXTIF_{profile['name']} ({int(profile['value'])}u)")
    out.append("")

    out.append("/* Numeric format identifiers */")
    for f in formats["numeric_formats"]["formats"]:
        name = f["name"]
        out.append(f"#define CARBON_{name} ({int(f['value'])}u)")
        out.append(f"#define CARBON_{name}_WIDTH_BITS ({int(f['width_bits'])}u)")
        out.append(f"#define CARBON_{name}_EXP_BITS ({int(f['exp_bits'])}u)")
        out.append(f"#define CARBON_{name}_FRAC_BITS ({int(f['frac_bits'])}u)")
        out.append(f"#define CARBON_{name}_BIAS ({int(f['bias'])}u)")
    out.append("")

    out.append("/* IEEE rounding modes */")
    for rm in formats["rounding_modes"]["modes"]:
        out.append(f"#define CARBON_{rm['name']} ({int(rm['value'])}u)")
    out.append("")

    out.append("/* CPUID leaf identifiers */")
    for leaf in disc["leafs"]:
        out.append(f"#define CARBON_{leaf['name']} ({_c_hex_u32(int(leaf['id']))})")
    out.append("")

    out.append("/* Discovery table */")
    disc_table = disc["discovery_table"]
    out.append(f"#define CARBON_{disc_table['name']}_VERSION ({int(disc_table['version'])}u)")
    out.append(f"#define CARBON_{disc_table['name']}_SIZE_BYTES ({int(disc_table['size_bytes'])}u)")
    if "pointer_model" in disc_table and isinstance(disc_table["pointer_model"], dict):
        ptr_bits = disc_table["pointer_model"].get("pointer_width_bits")
        if isinstance(ptr_bits, int):
            out.append(f"#define CARBON_{disc_table['name']}_POINTER_BITS ({ptr_bits}u)")
    for f in disc_table["fields"]:
        out.append(f"#define CARBON_{disc_table['name']}_OFF_{str(f['name']).upper()} ({int(f['offset'])}u)")
    out.append("")

    out.append("/* Feature bitmap format */")
    bitmaps = disc["feature_bitmaps"]
    out.append(f"#define CARBON_FEATURE_BITMAP_WORD_BITS ({int(bitmaps['word_bits'])}u)")
    out.append(f"#define CARBON_FEATURE_BITMAP_WORDS ({int(bitmaps['words'])}u)")
    out.append("")

    out.append("/* Limits table */")
    limits = disc["limits_table"]
    out.append(f"#define CARBON_{limits['name']}_VERSION ({int(limits['version'])}u)")
    out.append(f"#define CARBON_{limits['name']}_SIZE_BYTES ({int(limits['size_bytes'])}u)")
    for f in limits["fields"]:
        out.append(f"#define CARBON_{limits['name']}_OFF_{str(f['name']).upper()} ({int(f['offset'])}u)")
    out.append("")

    out.append("/* Feature bit identifiers */")
    for fs in disc["feature_sets"]:
        out.append(f"/* {fs['id']} */")
        for feat in fs["bits"]:
            name = feat["name"]
            bit = int(feat["bit"])
            word = bit // 32
            bit_in_word = bit % 32
            out.append(f"#define CARBON_{name}_BIT ({bit}u)")
            out.append(f"#define CARBON_{name}_WORD ({word}u)")
            out.append(f"#define CARBON_{name}_MASK (UINT32_C(1) << {bit_in_word})")
        out.append("")

    out.append("/* Topology table */")
    topo = topology["topology_table"]
    topo_hdr = topo["header"]
    topo_ent = topo["entry"]
    out.append(f"#define CARBON_{topo_hdr['name']}_VERSION ({int(topo_hdr['version'])}u)")
    out.append(f"#define CARBON_{topo_hdr['name']}_SIZE_BYTES ({int(topo_hdr['size_bytes'])}u)")
    for f in topo_hdr["fields"]:
        out.append(f"#define CARBON_{topo_hdr['name']}_OFF_{str(f['name']).upper()} ({int(f['offset'])}u)")
    out.append(f"#define CARBON_{topo_ent['name']}_VERSION ({int(topo_ent['version'])}u)")
    out.append(f"#define CARBON_{topo_ent['name']}_SIZE_BYTES ({int(topo_ent['size_bytes'])}u)")
    for f in topo_ent["fields"]:
        out.append(f"#define CARBON_{topo_ent['name']}_OFF_{str(f['name']).upper()} ({int(f['offset'])}u)")
    out.append("")

    out.append("/* CSR addresses */")
    for reg in csr["csrs"]:
        out.append(f"#define CARBON_{reg['name']} ({_c_hex_u32(int(reg['address']))})")
    out.append("")

    out.append("/* Fabric transaction types */")
    for t in fabric["transaction_types"]:
        out.append(f"#define CARBON_{t['name']} ({t['value']}u)")
    out.append("")

    out.append("/* Fabric attribute fields */")
    attrs = fabric["fabric_attributes"]
    attr_width = int(attrs["width_bits"])
    out.append(f"#define CARBON_FABRIC_ATTR_WIDTH_BITS ({attr_width}u)")
    for field in attrs["fields"]:
        fname = field["name"]
        lsb = int(field["lsb"])
        width = int(field["width"])
        mask = ((1 << width) - 1) << lsb
        out.append(f"#define CARBON_{fname}_LSB ({lsb}u)")
        out.append(f"#define CARBON_{fname}_WIDTH ({width}u)")
        out.append(f"#define CARBON_{fname}_MASK ({_c_hex_u32(mask)})")
    out.append("")

    out.append("/* Fabric response codes */")
    for rc in fabric["response_codes"]:
        out.append(f"#define CARBON_{rc['name']} ({rc['value']}u)")
    out.append("")

    out.append("/* CAI opcode groups */")
    for group in cai["opcode_model"]["opcode_groups"]:
        out.append(f"#define CARBON_{group['name']} ({int(group['value'])}u)")
    out.append("")

    out.append("/* CAI descriptor formats */")
    submit = cai["submission_descriptor"]
    out.append(f"#define CARBON_{submit['name']}_VERSION ({submit['version']}u)")
    out.append(f"#define CARBON_{submit['name']}_SIZE_BYTES ({submit['size_bytes']}u)")
    for f in submit["fields"]:
        out.append(f"#define CARBON_{submit['name']}_OFF_{str(f['name']).upper()} ({f['offset']}u)")
    out.append("")

    opdesc = cai["operand_descriptor"]
    out.append(f"#define CARBON_{opdesc['name']}_VERSION ({opdesc['version']}u)")
    out.append(f"#define CARBON_{opdesc['name']}_SIZE_BYTES ({opdesc['size_bytes']}u)")
    for f in opdesc["fields"]:
        out.append(f"#define CARBON_{opdesc['name']}_OFF_{str(f['name']).upper()} ({f['offset']}u)")
    out.append("")

    tdesc = cai["tensor_descriptor"]
    out.append(f"#define CARBON_{tdesc['name']}_VERSION ({tdesc['version']}u)")
    out.append(f"#define CARBON_{tdesc['name']}_SIZE_BYTES ({tdesc['size_bytes']}u)")
    for f in tdesc["fields"]:
        out.append(f"#define CARBON_{tdesc['name']}_OFF_{str(f['name']).upper()} ({f['offset']}u)")
    out.append("")

    comp = cai["completion_record"]
    out.append(f"#define CARBON_{comp['name']}_VERSION ({comp['version']}u)")
    out.append(f"#define CARBON_{comp['name']}_SIZE_BYTES ({comp['size_bytes']}u)")
    for f in comp["fields"]:
        out.append(f"#define CARBON_{comp['name']}_OFF_{str(f['name']).upper()} ({f['offset']}u)")
    out.append("")

    out.append("/* CAI completion status codes */")
    for s in cai["completion_status_codes"]:
        out.append(f"#define CARBON_{s['name']} ({s['value']}u)")
    out.append("")

    out.append("/* Device class identifiers */")
    for c in bdt_spec["device_classes"]["classes"]:
        out.append(f"#define CARBON_{c['name']} ({int(c['value'])}u)")
    out.append("")

    out.append("/* Board Device Table (BDT) header */")
    bdt = bdt_spec["bdt_header"]
    out.append(f"#define CARBON_{bdt['name']}_VERSION ({int(bdt['version'])}u)")
    out.append(f"#define CARBON_{bdt['name']}_SIZE_BYTES ({int(bdt['size_bytes'])}u)")
    for f in bdt["fields"]:
        out.append(f"#define CARBON_{bdt['name']}_OFF_{str(f['name']).upper()} ({int(f['offset'])}u)")
    out.append("")

    out.append("/* Board Device Table (BDT) entry */")
    bdt_entry = bdt_spec["bdt_entry"]
    out.append(f"#define CARBON_{bdt_entry['name']}_VERSION ({int(bdt_entry['version'])}u)")
    out.append(f"#define CARBON_{bdt_entry['name']}_SIZE_BYTES ({int(bdt_entry['size_bytes'])}u)")
    for f in bdt_entry["fields"]:
        out.append(f"#define CARBON_{bdt_entry['name']}_OFF_{str(f['name']).upper()} ({int(f['offset'])}u)")
    out.append("")

    out.append("/* BDT IRQ routing entries */")
    irq = bdt_spec["irq_routing_table"]
    out.append(f"#define CARBON_{irq['name']}_ENTRY_SIZE_BYTES ({int(irq['entry_size_bytes'])}u)")
    for f in irq["fields"]:
        out.append(f"#define CARBON_{irq['name']}_OFF_{str(f['name']).upper()} ({int(f['offset'])}u)")
    out.append("")

    out.append("/* Device capability descriptor */")
    dcd = dev["device_capability_descriptor"]
    out.append(f"#define CARBON_{dcd['name']}_VERSION ({int(dcd['version'])}u)")
    out.append(f"#define CARBON_{dcd['name']}_SIZE_BYTES ({int(dcd['size_bytes'])}u)")
    for f in dcd["fields"]:
        out.append(f"#define CARBON_{dcd['name']}_OFF_{str(f['name']).upper()} ({int(f['offset'])}u)")
    out.append("")

    out.append("/* Device compatibility feature bits */")
    for feat in dev["compat_feature_bits"]["bits"]:
        bit = int(feat["bit"])
        out.append(f"#define CARBON_{feat['name']}_BIT ({bit}u)")
        out.append(f"#define CARBON_{feat['name']}_MASK (UINT32_C(1) << {bit})")
    out.append("")

    out.append("/* Device turbo feature bits */")
    for feat in dev["turbo_feature_bits"]["bits"]:
        bit = int(feat["bit"])
        out.append(f"#define CARBON_{feat['name']}_BIT ({bit}u)")
        out.append(f"#define CARBON_{feat['name']}_MASK (UINT32_C(1) << {bit})")
    out.append("")

    out.append("/* Device feature field positions */")
    for f in dev["feature_fields"]["fields"]:
        msb = int(f["bits"][0])
        lsb = int(f["bits"][1])
        width = msb - lsb + 1
        mask = ((1 << width) - 1) << lsb
        out.append(f"#define CARBON_{f['name']}_WORD ({int(f['word'])}u)")
        out.append(f"#define CARBON_{f['name']}_LSB ({lsb}u)")
        out.append(f"#define CARBON_{f['name']}_WIDTH ({width}u)")
        out.append(f"#define CARBON_{f['name']}_MASK ({_c_hex_u32(mask)})")
    out.append("")

    out.append("/* Device common CSR register IDs */")
    for r in dev["device_csr_common"]["registers"]:
        out.append(f"#define CARBON_{r['name']} ({int(r['reg_id'])}u)")
    out.append("")

    out.append("/* Turbo queue descriptor formats */")
    tdesc = dev["turbo_submission_descriptor"]
    out.append(f"#define CARBON_{tdesc['name']}_VERSION ({int(tdesc['version'])}u)")
    out.append(f"#define CARBON_{tdesc['name']}_SIZE_BYTES ({int(tdesc['size_bytes'])}u)")
    for f in tdesc["fields"]:
        out.append(f"#define CARBON_{tdesc['name']}_OFF_{str(f['name']).upper()} ({int(f['offset'])}u)")
    out.append("")

    tcomp = dev["turbo_completion_record"]
    out.append(f"#define CARBON_{tcomp['name']}_VERSION ({int(tcomp['version'])}u)")
    out.append(f"#define CARBON_{tcomp['name']}_SIZE_BYTES ({int(tcomp['size_bytes'])}u)")
    for f in tcomp["fields"]:
        out.append(f"#define CARBON_{tcomp['name']}_OFF_{str(f['name']).upper()} ({int(f['offset'])}u)")
    out.append("")

    out.append("/* Turbo queue completion status codes */")
    for s in dev["turbo_completion_status_codes"]:
        out.append(f"#define CARBON_{s['name']} ({int(s['value'])}u)")
    out.append("")

    out.append("/* Z90 opcode pages and encodings */")
    out.append("/* Opcode page prefixes */")
    for page in isa_z90["opcode_pages"]:
        pfx = page["prefix_bytes"]
        out.append(f"#define CARBON_{page['name']}_PREFIX0 ({_c_hex_u32(int(pfx[0]))})")
        out.append(f"#define CARBON_{page['name']}_PREFIX1 ({_c_hex_u32(int(pfx[1]))})")
    out.append("")

    out.append("/* Page0 majors */")
    for m in isa_z90["page0_majors"]:
        out.append(f"#define CARBON_{m['name']} ({_c_hex_u32(int(m['value']))})")
    out.append("")

    out.append("/* Page0 subops */")
    for s in isa_z90["page0_subops"]:
        out.append(f"#define CARBON_{s['name']} ({_c_hex_u32(int(s['value']))})")
    out.append("")

    out.append("/* Page1 ops */")
    for o in isa_z90["page1_ops"]:
        out.append(f"#define CARBON_{o['name']} ({_c_hex_u32(int(o['value']))})")
    out.append("")

    return "\n".join(out)


def _emit_arch_contracts_md(specs: Dict[str, Dict[str, Any]], gen_info: Dict[str, str]) -> str:
    tiers = specs["tiers.yaml"]
    mode = specs["mode_switch.yaml"]
    profiles = specs["profiles.yaml"]
    topology = specs["topology.yaml"]
    bdt_spec = specs["bdt.yaml"]
    mem_attrs = specs["memory_attrs.yaml"]
    external_if = specs["external_if.yaml"]
    interfaces = specs["interfaces.yaml"]
    disc = specs["discovery.yaml"]
    csr = specs["csr_map.yaml"]
    dev = specs["device_model.yaml"]
    formats = specs["formats.yaml"]
    fabric = specs["fabric.yaml"]
    cai = specs["cai.yaml"]
    isa_z90 = specs["isa_z90.yaml"]

    out: List[str] = []
    out.append("# Project Carbon — Frozen Architecture Contracts (v1.0)")
    out.append("")
    out.append("_GENERATED FILE — DO NOT EDIT._")
    out.append(f"_Specs: {gen_info['spec_summary']}._")
    out.append(f"_Generated: {gen_info['timestamp']}._")
    out.append("_Source: `hdl/tools/gen_specs.py`._")
    out.append("")

    out.append("## A) Compatibility Tier Ladders")
    out.append("")
    if "presentation_model" in tiers:
        pres = tiers["presentation_model"]
        out.append("### Presentation Model")
        out.append("")
        if isinstance(pres, dict):
            if "name" in pres:
                out.append(f"- Name: `{pres['name']}`")
            if "description" in pres:
                out.append(f"- Description: {_md_escape(pres['description'])}")
            rules = pres.get("rules")
            if isinstance(rules, list):
                for rule in rules:
                    out.append(f"- {_md_escape(rule)}")
        out.append("")
    for ladder in tiers["ladders"]:
        out.append(f"### {ladder['id']} ({_md_escape(ladder['description'])})")
        out.append("")
        out.append(f"- Reset default: `{ladder['reset_default']}`")
        out.append(f"- Upgrade rule: `{ladder['upgrade_rule']}`")
        out.append(f"- Downgrade rule: `{ladder['downgrade_rule']}`")
        out.append("")
        out.append("| Tier | Value | Label | Strict |")
        out.append("|---:|---:|---|:---:|")
        for t in ladder["tiers"]:
            strict = "true" if bool(t.get("strict", False)) else ""
            out.append(
                f"| `{t['id']}` | `{t['value']}` | `{_md_escape(t['label'])}` | {strict} |"
            )
        out.append("")
        overrides = ladder.get("presentation_overrides")
        if isinstance(overrides, list) and overrides:
            out.append("#### Presentation Overrides")
            out.append("")
            out.append("| Part | Presents As | Feature Bits | Description |")
            out.append("|---|---|---|---|")
            for ov in overrides:
                bits = ""
                if isinstance(ov, dict):
                    feat_bits = ov.get("feature_bits")
                    if isinstance(feat_bits, list):
                        bits = ", ".join([f"`{b}`" for b in feat_bits])
                    out.append(
                        f"| `{ov.get('part','')}` | `{ov.get('presents_as','')}` | {bits} | {_md_escape(ov.get('description',''))} |"
                    )
            out.append("")

    out.append("## B) Profiles")
    out.append("")
    out.append("| Profile | ID | Description |")
    out.append("|---|---:|---|")
    for prof in profiles["profiles"]:
        out.append(
            f"| `{prof['id']}` | `{prof['value']}` | {_md_escape(prof['description'])} |"
        )
    out.append("")
    out.append("### Profile Requirements")
    out.append("")
    out.append("| Profile | Blocks | Discovery Tables | Min Devices | Legacy Z80 Bus |")
    out.append("|---|---|---|---|:---:|")
    for prof in profiles["profiles"]:
        blocks = ", ".join([f"`{b}`" for b in prof["required_blocks"]]) if prof["required_blocks"] else ""
        tables = (
            ", ".join([f"`{t}`" for t in prof["required_discovery_tables"]])
            if prof["required_discovery_tables"]
            else ""
        )
        devices = (
            ", ".join([f"`{d}`" for d in prof["required_min_devices"]])
            if prof["required_min_devices"]
            else ""
        )
        legacy = "true" if prof["legacy_z80_bus_adapter"] else ""
        out.append(f"| `{prof['id']}` | {blocks} | {tables} | {devices} | {legacy} |")
    out.append("")

    out.append("## C) Mode Switching Contract")
    out.append("")
    out.append("### Instructions")
    out.append("")
    out.append("| Instruction | Signature | Description |")
    out.append("|---|---|---|")
    for inst in mode["instructions"]:
        out.append(f"| `{inst['name']}` | `{inst['signature']}` | {_md_escape(inst['description'])} |")
    out.append("")

    out.append("### MODEFLAGS")
    out.append("")
    out.append(f"- Width: `{mode['modeflags']['width_bits']}` bits")
    out.append("")
    out.append("| Name | Bit | Reset | Description |")
    out.append("|---|---:|---:|---|")
    for b in mode["modeflags"]["bits"]:
        out.append(f"| `{b['name']}` | `{b['bit']}` | `{b['reset']}` | {_md_escape(b['description'])} |")
    out.append("")
    out.append("### MODESTACK")
    out.append("")
    out.append(f"- Minimum depth: `{mode['modestack']['min_depth']}`")
    out.append(f"- Recommended depth: `{mode['modestack']['recommended_depth']}`")
    out.append("")

    out.append("## D) Discovery / CPUID / CAPS")
    out.append("")
    out.append(f"- Endianness: `{disc['packing']['endianness']}`")
    out.append(f"- Leaf return words: `{disc['packing']['leaf_return_words']}` x `{disc['packing']['word_bits']}`-bit")
    out.append(f"- Unknown leaf behavior: `{disc['leaf_rules']['unknown_leaf_behavior']}`")
    out.append("")
    out.append("### Discovery Table (V1)")
    out.append("")
    disc_table = disc["discovery_table"]
    out.append(
        f"- Format: `{disc_table['name']}`, version `{disc_table['version']}`, size `{disc_table['size_bytes']}` bytes"
    )
    out.append("")
    out.append("| Field | Offset | Width (bytes) | Type | Description |")
    out.append("|---|---:|---:|---|---|")
    for f in disc_table["fields"]:
        out.append(
            f"| `{f['name']}` | `{f['offset']}` | `{f['width_bytes']}` | `{f['type']}` | {_md_escape(f['description'])} |"
        )
    out.append("")
    out.append("### Feature Bitmap Format")
    out.append("")
    out.append(f"- Words: `{disc['feature_bitmaps']['words']}` x `{disc['feature_bitmaps']['word_bits']}`-bit")
    out.append("")
    out.append("### Limits Table (V1)")
    out.append("")
    limits = disc["limits_table"]
    out.append(
        f"- Format: `{limits['name']}`, version `{limits['version']}`, size `{limits['size_bytes']}` bytes"
    )
    out.append("")
    out.append("| Field | Offset | Width (bytes) | Type | Description |")
    out.append("|---|---:|---:|---|---|")
    for f in limits["fields"]:
        out.append(
            f"| `{f['name']}` | `{f['offset']}` | `{f['width_bytes']}` | `{f['type']}` | {_md_escape(f['description'])} |"
        )
    out.append("")
    out.append("### CPUID Leaf IDs")
    out.append("")
    out.append("| Leaf | ID | Description |")
    out.append("|---|---:|---|")
    for leaf in disc["leafs"]:
        out.append(f"| `{leaf['name']}` | `{_fmt_hex(int(leaf['id']), 32)}` | {_md_escape(leaf['description'])} |")
    out.append("")
    out.append("### Feature Bits")
    out.append("")
    out.append("| Feature | Bit | Description |")
    out.append("|---|---:|---|")
    for fs in disc["feature_sets"]:
        for feat in fs["bits"]:
            out.append(f"| `{feat['name']}` | `{feat['bit']}` | {_md_escape(feat['description'])} |")
    out.append("")
    out.append("### Example CPUID Leaf Table (IDs)")
    out.append("")
    out.append("| Leaf ID | Name |")
    out.append("|---:|---|")
    for ex in disc.get("examples", []):
        if isinstance(ex, dict) and ex.get("name") == "example_cpuid_leaf_table":
            for row in ex.get("rows", []):
                out.append(f"| `{_fmt_hex(int(row['leaf']), 32)}` | `{row['name']}` |")
    out.append("")

    out.append("## E) Topology Table")
    out.append("")
    topo = topology["topology_table"]
    topo_hdr = topo["header"]
    topo_ent = topo["entry"]
    out.append(f"- Header: `{topo_hdr['name']}`, version `{topo_hdr['version']}`, size `{topo_hdr['size_bytes']}` bytes")
    out.append("")
    out.append("| Field | Offset | Width (bytes) | Type | Description |")
    out.append("|---|---:|---:|---|---|")
    for f in topo_hdr["fields"]:
        out.append(
            f"| `{f['name']}` | `{f['offset']}` | `{f['width_bytes']}` | `{f['type']}` | {_md_escape(f['description'])} |"
        )
    out.append("")
    out.append(f"- Entry: `{topo_ent['name']}`, version `{topo_ent['version']}`, size `{topo_ent['size_bytes']}` bytes")
    out.append("")
    out.append("| Field | Offset | Width (bytes) | Type | Description |")
    out.append("|---|---:|---:|---|---|")
    for f in topo_ent["fields"]:
        out.append(
            f"| `{f['name']}` | `{f['offset']}` | `{f['width_bytes']}` | `{f['type']}` | {_md_escape(f['description'])} |"
        )
    out.append("")

    out.append("## F) CSR Namespace + Register Model")
    out.append("")
    out.append(f"- Unknown CSR behavior: `{csr['access_control']['unknown_csr_behavior']}`")
    out.append("")
    out.append("| CSR | Address | Access | Min Priv | Description |")
    out.append("|---|---:|---|---|---|")
    for r in csr["csrs"]:
        out.append(
            f"| `{r['name']}` | `{_fmt_hex(int(r['address']), 32)}` | `{r['access']}` | `{r['privilege_min']}` | {_md_escape(r['description'])} |"
        )
    out.append("")

    out.append("## G) Memory Attributes")
    out.append("")
    out.append(f"- Width: `{mem_attrs['attributes']['width_bits']}` bits")
    out.append("")
    out.append("| Name | Bit | Description |")
    out.append("|---|---:|---|")
    for f in mem_attrs["attributes"]["fields"]:
        out.append(f"| `{f['name']}` | `{f['bit']}` | {_md_escape(f['description'])} |")
    out.append("")
    out.append("### DMA Coherence Baseline")
    out.append("")
    dma = mem_attrs.get("dma_coherence", {})
    if isinstance(dma, dict):
        out.append(f"- Baseline: `{dma.get('baseline','')}`")
        for req in dma.get("requirements", []):
            out.append(f"- {_md_escape(req)}")
    out.append("")
    out.append("### P7 Cache Maintenance Hooks")
    out.append("")
    for op in mem_attrs.get("p7_requirements", {}).get("cache_maintenance_ops", []):
        out.append(f"- `{op['name']}`: {_md_escape(op['description'])}")
    out.append("")

    out.append("## H) Fabric Transaction Contract")
    out.append("")
    out.append("### Transaction Types")
    out.append("")
    out.append("| Name | Value | Description |")
    out.append("|---|---:|---|")
    for t in fabric["transaction_types"]:
        out.append(f"| `{t['name']}` | `{t['value']}` | {_md_escape(t['description'])} |")
    out.append("")
    out.append("### Attributes")
    out.append("")
    out.append("| Field | LSB | Width | Description |")
    out.append("|---|---:|---:|---|")
    for f in fabric["fabric_attributes"]["fields"]:
        out.append(f"| `{f['name']}` | `{f['lsb']}` | `{f['width']}` | {_md_escape(f['description'])} |")
    out.append("")
    out.append("### Response Codes")
    out.append("")
    out.append("| Name | Value | Description |")
    out.append("|---|---:|---|")
    for r in fabric["response_codes"]:
        out.append(f"| `{r['name']}` | `{r['value']}` | {_md_escape(r['description'])} |")
    out.append("")

    out.append("## I) Carbon Accelerator Interface (CAI)")
    out.append("")
    out.append("### Opcode Groups")
    out.append("")
    out.append("| Name | Value | Description |")
    out.append("|---|---:|---|")
    for group in cai["opcode_model"]["opcode_groups"]:
        out.append(
            f"| `{group['name']}` | `{group['value']}` | {_md_escape(group['description'])} |"
        )
    out.append("")

    out.append("### Submission Descriptor (V1)")
    out.append("")
    submit = cai["submission_descriptor"]
    out.append(f"- Format: `{submit['name']}`, version `{submit['version']}`, size `{submit['size_bytes']}` bytes")
    out.append("")
    out.append("| Field | Offset | Width (bytes) | Type | Description |")
    out.append("|---|---:|---:|---|---|")
    for f in submit["fields"]:
        out.append(
            f"| `{f['name']}` | `{f['offset']}` | `{f['width_bytes']}` | `{f['type']}` | {_md_escape(f['description'])} |"
        )
    out.append("")

    out.append("### Operand Descriptor (V1)")
    out.append("")
    opdesc = cai["operand_descriptor"]
    out.append(f"- Format: `{opdesc['name']}`, version `{opdesc['version']}`, size `{opdesc['size_bytes']}` bytes")
    out.append("")
    out.append("| Field | Offset | Width (bytes) | Type | Description |")
    out.append("|---|---:|---:|---|---|")
    for f in opdesc["fields"]:
        out.append(
            f"| `{f['name']}` | `{f['offset']}` | `{f['width_bytes']}` | `{f['type']}` | {_md_escape(f['description'])} |"
        )
    out.append("")

    out.append("### Tensor Descriptor (V1)")
    out.append("")
    tdesc = cai["tensor_descriptor"]
    out.append(
        f"- Format: `{tdesc['name']}`, version `{tdesc['version']}`, size `{tdesc['size_bytes']}` bytes"
    )
    out.append("")
    out.append("| Field | Offset | Width (bytes) | Type | Description |")
    out.append("|---|---:|---:|---|---|")
    for f in tdesc["fields"]:
        out.append(
            f"| `{f['name']}` | `{f['offset']}` | `{f['width_bytes']}` | `{f['type']}` | {_md_escape(f['description'])} |"
        )
    out.append("")

    out.append("### Completion Record (V1)")
    out.append("")
    comp = cai["completion_record"]
    out.append(f"- Format: `{comp['name']}`, version `{comp['version']}`, size `{comp['size_bytes']}` bytes")
    out.append("")
    out.append("| Field | Offset | Width (bytes) | Type | Description |")
    out.append("|---|---:|---:|---|---|")
    for f in comp["fields"]:
        out.append(
            f"| `{f['name']}` | `{f['offset']}` | `{f['width_bytes']}` | `{f['type']}` | {_md_escape(f['description'])} |"
        )
    out.append("")

    out.append("### Completion Status Codes")
    out.append("")
    out.append("| Name | Value | Description |")
    out.append("|---|---:|---|")
    for s in cai["completion_status_codes"]:
        out.append(f"| `{s['name']}` | `{s['value']}` | {_md_escape(s['description'])} |")
    out.append("")

    out.append("### Example Submission Descriptor")
    out.append("")
    for ex in cai.get("examples", []):
        if isinstance(ex, dict) and ex.get("name") == "example_descriptor":
            desc = ex.get("submit_desc", {})
            out.append("```text")
            for k in [
                "desc_version",
                "desc_size_dw",
                "opcode",
                "flags",
                "context_id",
                "operand_count",
                "tag",
                "opcode_group",
                "format_primary",
                "format_aux",
                "format_flags",
                "operands_ptr",
                "result_ptr",
                "result_len",
                "result_stride",
                "tensor_desc_ptr",
                "tensor_desc_len",
                "tensor_rank",
                "tensor_desc_flags",
            ]:
                if k in desc:
                    out.append(f"{k}: {desc[k]}")
            out.append("```")
            out.append("")

    out.append("## J) Device Model and BDT Schema")
    out.append("")
    dpm = dev["dual_personality_device_model"]
    out.append("### Dual Personality Device Model")
    out.append("")
    out.append(f"- {_md_escape(dpm['description'])}")
    out.append("")
    out.append("### Compatibility Personality")
    out.append("")
    for req in dpm.get("compatibility_personality", {}).get("requirements", []):
        out.append(f"- {_md_escape(req)}")
    out.append("")
    out.append("### Turbo Personality")
    out.append("")
    for req in dpm.get("turbo_personality", {}).get("requirements", []):
        out.append(f"- {_md_escape(req)}")
    out.append("")
    out.append("### Polling-Complete Semantics")
    out.append("")
    for req in dev.get("polling_completion", {}).get("requirements", []):
        out.append(f"- {_md_escape(req)}")
    out.append("")

    out.append("### Device Class IDs")
    out.append("")
    out.append("| Class | Value | Description |")
    out.append("|---|---:|---|")
    for c in bdt_spec["device_classes"]["classes"]:
        out.append(f"| `{c['name']}` | `{_fmt_hex(int(c['value']), 16)}` | {_md_escape(c['description'])} |")
    out.append("")

    out.append("### BDT Header (V1)")
    out.append("")
    bdt = bdt_spec["bdt_header"]
    out.append(f"- Format: `{bdt['name']}`, version `{bdt['version']}`, size `{bdt['size_bytes']}` bytes")
    out.append("")
    out.append("| Field | Offset | Width (bytes) | Type | Description |")
    out.append("|---|---:|---:|---|---|")
    for f in bdt["fields"]:
        out.append(
            f"| `{f['name']}` | `{f['offset']}` | `{f['width_bytes']}` | `{f['type']}` | {_md_escape(f['description'])} |"
        )
    out.append("")

    out.append("### BDT Entry (V1)")
    out.append("")
    bdt_entry = bdt_spec["bdt_entry"]
    out.append(
        f"- Format: `{bdt_entry['name']}`, version `{bdt_entry['version']}`, size `{bdt_entry['size_bytes']}` bytes"
    )
    out.append("")
    out.append("| Field | Offset | Width (bytes) | Type | Description |")
    out.append("|---|---:|---:|---|---|")
    for f in bdt_entry["fields"]:
        out.append(
            f"| `{f['name']}` | `{f['offset']}` | `{f['width_bytes']}` | `{f['type']}` | {_md_escape(f['description'])} |"
        )
    out.append("")

    out.append("### BDT IRQ Routing Entry (V1)")
    out.append("")
    irq = bdt_spec["irq_routing_table"]
    out.append(f"- Entry size: `{irq['entry_size_bytes']}` bytes")
    out.append("")
    out.append("| Field | Offset | Width (bytes) | Type | Description |")
    out.append("|---|---:|---:|---|---|")
    for f in irq["fields"]:
        out.append(
            f"| `{f['name']}` | `{f['offset']}` | `{f['width_bytes']}` | `{f['type']}` | {_md_escape(f['description'])} |"
        )
    out.append("")

    out.append("### Device Capability Descriptor (V1)")
    out.append("")
    dcd = dev["device_capability_descriptor"]
    out.append(f"- Format: `{dcd['name']}`, version `{dcd['version']}`, size `{dcd['size_bytes']}` bytes")
    out.append("")
    out.append("| Field | Offset | Width (bytes) | Type | Description |")
    out.append("|---|---:|---:|---|---|")
    for f in dcd["fields"]:
        out.append(
            f"| `{f['name']}` | `{f['offset']}` | `{f['width_bytes']}` | `{f['type']}` | {_md_escape(f['description'])} |"
        )
    out.append("")

    out.append("### Device Compatibility Feature Bits")
    out.append("")
    out.append("| Feature | Bit | Description |")
    out.append("|---|---:|---|")
    for feat in dev["compat_feature_bits"]["bits"]:
        out.append(f"| `{feat['name']}` | `{feat['bit']}` | {_md_escape(feat['description'])} |")
    out.append("")

    out.append("### Device Turbo Feature Bits")
    out.append("")
    out.append("| Feature | Bit | Description |")
    out.append("|---|---:|---|")
    for feat in dev["turbo_feature_bits"]["bits"]:
        out.append(f"| `{feat['name']}` | `{feat['bit']}` | {_md_escape(feat['description'])} |")
    out.append("")

    out.append("### Device Feature Fields")
    out.append("")
    out.append("| Field | Word | Bits | Description |")
    out.append("|---|---:|---|---|")
    for f in dev["feature_fields"]["fields"]:
        out.append(
            f"| `{f['name']}` | `{f['word']}` | `{f['bits'][0]}:{f['bits'][1]}` | {_md_escape(f['description'])} |"
        )
    out.append("")

    out.append("### Device Common CSR Register IDs")
    out.append("")
    out.append("| Register | Reg ID | Access | Description |")
    out.append("|---|---:|---|---|")
    for r in dev["device_csr_common"]["registers"]:
        out.append(
            f"| `{r['name']}` | `{_fmt_hex(int(r['reg_id']), 12)}` | `{r['access']}` | {_md_escape(r['description'])} |"
        )
    out.append("")

    out.append("### Turbo Queue Submission Descriptor (V1)")
    out.append("")
    tdesc = dev["turbo_submission_descriptor"]
    out.append(f"- Format: `{tdesc['name']}`, version `{tdesc['version']}`, size `{tdesc['size_bytes']}` bytes")
    out.append("")
    out.append("| Field | Offset | Width (bytes) | Type | Description |")
    out.append("|---|---:|---:|---|---|")
    for f in tdesc["fields"]:
        out.append(
            f"| `{f['name']}` | `{f['offset']}` | `{f['width_bytes']}` | `{f['type']}` | {_md_escape(f['description'])} |"
        )
    out.append("")

    out.append("### Turbo Queue Completion Record (V1)")
    out.append("")
    tcomp = dev["turbo_completion_record"]
    out.append(f"- Format: `{tcomp['name']}`, version `{tcomp['version']}`, size `{tcomp['size_bytes']}` bytes")
    out.append("")
    out.append("| Field | Offset | Width (bytes) | Type | Description |")
    out.append("|---|---:|---:|---|---|")
    for f in tcomp["fields"]:
        out.append(
            f"| `{f['name']}` | `{f['offset']}` | `{f['width_bytes']}` | `{f['type']}` | {_md_escape(f['description'])} |"
        )
    out.append("")

    out.append("### Turbo Queue Completion Status Codes")
    out.append("")
    out.append("| Name | Value | Description |")
    out.append("|---|---:|---|")
    for s in dev["turbo_completion_status_codes"]:
        out.append(f"| `{s['name']}` | `{s['value']}` | {_md_escape(s['description'])} |")
    out.append("")

    out.append("## K) External Interfaces")
    out.append("")
    out.append("### Legacy Z80 Bus Adapter Profiles")
    out.append("")
    out.append("| Profile | Value | Description |")
    out.append("|---|---:|---|")
    for profile in external_if["legacy_z80_bus_adapter"]["profiles"]:
        out.append(
            f"| `{profile['name']}` | `{profile['value']}` | {_md_escape(profile['description'])} |"
        )
    out.append("")
    out.append("### Modern SoC External Profiles")
    out.append("")
    out.append("| Profile | Value | Description |")
    out.append("|---|---:|---|")
    for profile in external_if["modern_soc_external"]["profiles"]:
        out.append(
            f"| `{profile['name']}` | `{profile['value']}` | {_md_escape(profile['description'])} |"
        )
    out.append("")
    out.append("### Debug Transport")
    out.append("")
    out.append(f"- Minimum: `{external_if['debug_transport']['minimum']}`")
    out.append("")

    out.append("## L) Common Interfaces")
    out.append("")
    out.append("| Interface | Value | Description |")
    out.append("|---|---:|---|")
    for iface in interfaces["interfaces"]:
        out.append(
            f"| `{iface['name']}` | `{iface['value']}` | {_md_escape(iface['description'])} |"
        )
    out.append("")

    out.append("## M) Z90 Fast-Path ISA (Opcode Pages)")
    out.append("")
    out.append("### Opcode Pages")
    out.append("")
    out.append("| Page | Prefix Bytes | Description |")
    out.append("|---|---|---|")
    for page in isa_z90["opcode_pages"]:
        pfx = page["prefix_bytes"]
        out.append(
            f"| `{page['name']}` | `{_md_escape(' '.join([hex(int(b)) for b in pfx]))}` | {_md_escape(page['description'])} |"
        )
    out.append("")

    out.append("### Page0 Majors")
    out.append("")
    out.append("| Name | Value | Description |")
    out.append("|---|---:|---|")
    for m in isa_z90["page0_majors"]:
        out.append(f"| `{m['name']}` | `{m['value']}` | {_md_escape(m['description'])} |")
    out.append("")

    out.append("### Page0 Subops")
    out.append("")
    out.append("| Name | Major | Value | Description |")
    out.append("|---|---|---:|---|")
    for s in isa_z90["page0_subops"]:
        out.append(f"| `{s['name']}` | `{s['major']}` | `{s['value']}` | {_md_escape(s['description'])} |")
    out.append("")

    out.append("### Page1 Ops")
    out.append("")
    out.append("| Name | Value | Description |")
    out.append("|---|---:|---|")
    for o in isa_z90["page1_ops"]:
        out.append(f"| `{o['name']}` | `{o['value']}` | {_md_escape(o['description'])} |")
    out.append("")

    out.append("## N) Numeric Formats")
    out.append("")
    out.append("| Name | Value | Width | Exp | Frac | Bias | Description |")
    out.append("|---|---:|---:|---:|---:|---:|---|")
    for f in formats["numeric_formats"]["formats"]:
        out.append(
            f"| `{f['name']}` | `{f['value']}` | `{f['width_bits']}` | `{f['exp_bits']}` | `{f['frac_bits']}` | `{f['bias']}` | {_md_escape(f['description'])} |"
        )
    out.append("")

    out.append("### Rounding Modes")
    out.append("")
    out.append("| Name | Value | Mnemonic | Description |")
    out.append("|---|---:|---|---|")
    for m in formats["rounding_modes"]["modes"]:
        out.append(f"| `{m['name']}` | `{m['value']}` | `{m['mnemonic']}` | {_md_escape(m['description'])} |")
    out.append("")

    return "\n".join(out)


def main(argv: Sequence[str]) -> int:
    parser = argparse.ArgumentParser(description="Generate Project Carbon architecture outputs.")
    parser.add_argument(
        "--repo-root",
        default=None,
        help="Path to repository root (defaults to auto-detect from script location).",
    )
    args = parser.parse_args(argv)

    repo_root = Path(args.repo_root) if args.repo_root else Path(__file__).resolve().parents[2]
    spec_dir = repo_root / "hdl" / "spec"
    out_gen = repo_root / "hdl" / "gen"
    out_docs = repo_root / "docs"

    try:
        specs = _load_specs(spec_dir)
        _validate_specs(specs)
        gen_info = _build_gen_info(specs)

        out_gen.mkdir(parents=True, exist_ok=True)
        out_docs.mkdir(parents=True, exist_ok=True)

        _write_text_unix(out_gen / "carbon_arch_pkg.sv", _emit_sv(specs, gen_info) + "\n")
        _write_text_unix(out_gen / "carbon_arch.h", _emit_c_header(specs, gen_info) + "\n")
        _write_text_unix(out_docs / "ARCH_CONTRACTS.md", _emit_arch_contracts_md(specs, gen_info) + "\n")
        return 0
    except SpecError as e:
        print(f"gen_specs.py: ERROR: {e}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
