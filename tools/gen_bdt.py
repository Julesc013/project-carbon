#!/usr/bin/env python3
from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path
from typing import Any, Dict, Iterable, List, Optional, Sequence, Tuple, Union


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


def _write_text_unix(path: Path, text: str) -> None:
    path.write_bytes(text.encode("utf-8"))


def _to_pascal(tokens: Iterable[str]) -> str:
    return "".join(t[:1].upper() + t[1:].lower() if t else "" for t in tokens)


def _const_name(prefix: str, name: str, drop: str) -> str:
    base = name
    if base.startswith(drop):
        base = base[len(drop):]
    return prefix + _to_pascal(base.split("_"))


def _load_yaml(path: Path) -> Dict[str, Any]:
    return parse_yaml_subset(path.read_text(encoding="utf-8"), source=path.as_posix())


def _build_class_map(dev: Dict[str, Any]) -> Dict[str, int]:
    classes = dev.get("device_classes", {}).get("classes", [])
    _expect_type(classes, list, where="device_model.yaml:device_classes")
    return {c["name"]: int(c["value"]) for c in classes if isinstance(c, dict)}


def _build_bit_map(bits: List[Dict[str, Any]]) -> Dict[str, int]:
    return {b["name"]: int(b["bit"]) for b in bits if isinstance(b, dict)}


def _build_feature_fields(dev: Dict[str, Any]) -> Dict[str, Tuple[int, int, int]]:
    fields = dev.get("feature_fields", {}).get("fields", [])
    _expect_type(fields, list, where="device_model.yaml:feature_fields")
    out: Dict[str, Tuple[int, int, int]] = {}
    for f in fields:
        if not isinstance(f, dict):
            continue
        bits = f.get("bits", [0, 0])
        if not isinstance(bits, list) or len(bits) != 2:
            raise SpecError("device_model.yaml:feature_fields.bits must be [hi, lo]")
        hi = int(bits[0])
        lo = int(bits[1])
        if hi < lo:
            hi, lo = lo, hi
        width = hi - lo + 1
        out[f["name"]] = (int(f["word"]), lo, width)
    return out


def _encode_flags(raw: Any, bit_map: Dict[str, int], *, where: str) -> int:
    if raw is None:
        return 0
    if isinstance(raw, int):
        return raw
    if isinstance(raw, str):
        raw = [raw]
    if not isinstance(raw, list):
        raise SpecError(f"{where}: flags must be list, string, or int")
    mask = 0
    for name in raw:
        if name not in bit_map:
            raise SpecError(f"{where}: unknown flag {name!r}")
        mask |= 1 << bit_map[name]
    return mask


def _pack_feature_fields(
    fields: Dict[str, Tuple[int, int, int]],
    values: Dict[str, Any],
    word: int,
    *,
    where: str,
) -> int:
    total = 0
    for name, raw_val in values.items():
        if name not in fields:
            raise SpecError(f"{where}: unknown feature field {name!r}")
        f_word, lsb, width = fields[name]
        if f_word != word:
            raise SpecError(f"{where}: field {name} belongs to word {f_word}, not {word}")
        if not isinstance(raw_val, int):
            raise SpecError(f"{where}: field {name} value must be int")
        mask = (1 << width) - 1
        total |= (raw_val & mask) << lsb
    return total


def _resolve_class(dev: Dict[str, Any], class_map: Dict[str, int], *, where: str) -> int:
    if "class" in dev:
        value = dev["class"]
    elif "class_id" in dev:
        value = dev["class_id"]
    else:
        raise SpecError(f"{where}: missing class/class_id")
    if isinstance(value, int):
        return value
    if isinstance(value, str):
        if value not in class_map:
            raise SpecError(f"{where}: unknown class {value!r}")
        return class_map[value]
    raise SpecError(f"{where}: class must be string or int")


def _parse_device(
    dev: Dict[str, Any],
    index: int,
    class_map: Dict[str, int],
    compat_bits: Dict[str, int],
    turbo_bits: Dict[str, int],
    feat_fields: Dict[str, Tuple[int, int, int]],
) -> Dict[str, int]:
    name = dev.get("name", f"device[{index}]")
    where = f"BDT[{name}]"

    class_id = _resolve_class(dev, class_map, where=where)
    device_id = dev.get("device_id")
    if device_id is None or not isinstance(device_id, int):
        raise SpecError(f"{where}: device_id required (u16)")

    compat_flags = _encode_flags(dev.get("compat_flags"), compat_bits, where=where)
    turbo_flags = _encode_flags(dev.get("turbo_flags"), turbo_bits, where=where)

    feature_word0 = int(dev.get("feature_word0", 0))
    feature_word1 = int(dev.get("feature_word1", 0))

    if "feature_word0_fields" in dev:
        vals = dev["feature_word0_fields"]
        _expect_type(vals, dict, where=f"{where}:feature_word0_fields")
        feature_word0 |= _pack_feature_fields(feat_fields, vals, 0, where=where)
    if "feature_word1_fields" in dev:
        vals = dev["feature_word1_fields"]
        _expect_type(vals, dict, where=f"{where}:feature_word1_fields")
        feature_word1 |= _pack_feature_fields(feat_fields, vals, 1, where=where)

    return {
        "class_id": class_id,
        "subclass_id": int(dev.get("subclass_id", 0)),
        "vendor_id": int(dev.get("vendor_id", 0)),
        "device_id": int(device_id),
        "instance_id": int(dev.get("instance_id", 0)),
        "revision_id": int(dev.get("revision_id", 1)),
        "compat_flags": compat_flags,
        "turbo_flags": turbo_flags,
        "feature_word0": feature_word0,
        "feature_word1": feature_word1,
        "csr_base": int(dev.get("csr_base", 0)),
        "compat_io_base": int(dev.get("compat_io_base", 0)),
        "mmio_base": int(dev.get("mmio_base", 0)),
        "mmio_size": int(dev.get("mmio_size", 0)),
        "queue_count": int(dev.get("queue_count", 0)),
        "irq_count": int(dev.get("irq_count", 0)),
    }


def _write_u16(buf: List[int], off: int, value: int) -> None:
    buf[off + 0] = value & 0xFF
    buf[off + 1] = (value >> 8) & 0xFF


def _write_u32(buf: List[int], off: int, value: int) -> None:
    buf[off + 0] = value & 0xFF
    buf[off + 1] = (value >> 8) & 0xFF
    buf[off + 2] = (value >> 16) & 0xFF
    buf[off + 3] = (value >> 24) & 0xFF


def _write_u64(buf: List[int], off: int, value: int) -> None:
    _write_u32(buf, off, value & 0xFFFF_FFFF)
    _write_u32(buf, off + 4, (value >> 32) & 0xFFFF_FFFF)


def _emit_sv_bdt(path: Path, image: List[int]) -> None:
    tokens = [f"8'h{b:02x}" for b in reversed(image)]
    lines = [", ".join(tokens[i : i + 16]) for i in range(0, len(tokens), 16)]
    body = "  " + ",\n  ".join(lines)
    out = [
        "// AUTO-GENERATED by tools/gen_bdt.py; do not edit manually.",
        f"localparam int unsigned BDT_IMAGE_BYTES = {len(image)};",
        "localparam logic [BDT_IMAGE_BYTES*8-1:0] BDT_IMAGE = {",
        body,
        "};",
        "",
    ]
    _write_text_unix(path, "\n".join(out))


def _emit_carbon_constants(
    path: Path,
    dev: Dict[str, Any],
    disc: Dict[str, Any],
    class_map: Dict[str, int],
    compat_bits: Dict[str, int],
    turbo_bits: Dict[str, int],
    feat_fields: Dict[str, Tuple[int, int, int]],
) -> None:
    bdt_signature = 0x54444243
    bdt_header = dev["bdt_header"]
    bdt_entry_size = dev["device_capability_descriptor"]["size_bytes"]

    lines: List[str] = []
    lines.append("// AUTO-GENERATED by tools/gen_bdt.py; do not edit manually.")
    lines.append("#pragma once")
    lines.append("")
    lines.append("#include <cstdint>")
    lines.append("")
    lines.append("namespace carbon_sim {")
    lines.append("")
    lines.append(f"constexpr std::uint32_t kBdtSignature = 0x{bdt_signature:08x}u;")
    lines.append(f"constexpr std::uint16_t kBdtHeaderVersion = {int(bdt_header['version'])};")
    lines.append(f"constexpr std::uint16_t kBdtHeaderSizeBytes = {int(bdt_header['size_bytes'])};")
    lines.append(f"constexpr std::uint16_t kBdtEntrySizeBytes = {int(bdt_entry_size)};")
    lines.append("")

    for name, value in sorted(class_map.items(), key=lambda item: item[1]):
        const_name = _const_name("kDevClass", name, "DEVCLASS_")
        lines.append(f"constexpr std::uint16_t {const_name} = 0x{value:04x};")
    lines.append("")

    for name, bit in sorted(compat_bits.items(), key=lambda item: item[1]):
        const_name = _const_name("kCompat", name, "DEVFEAT_COMPAT_")
        lines.append(f"constexpr std::uint32_t {const_name} = (1u << {bit});")
    lines.append("")

    for name, bit in sorted(turbo_bits.items(), key=lambda item: item[1]):
        const_name = _const_name("kTurbo", name, "DEVFEAT_TURBO_")
        lines.append(f"constexpr std::uint32_t {const_name} = (1u << {bit});")
    lines.append("")

    features = disc.get("feature_sets", [])
    feat_bits: Dict[str, int] = {}
    for fs in features:
        if not isinstance(fs, dict):
            continue
        for bit in fs.get("bits", []):
            if not isinstance(bit, dict):
                continue
            name = bit.get("name")
            if name is None:
                continue
            feat_bits[name] = int(bit["bit"])
    for name, bit in sorted(feat_bits.items(), key=lambda item: item[1]):
        if bit >= 32:
            continue
        const_name = _const_name("kFeat", name, "FEAT_") + "Mask"
        lines.append(f"constexpr std::uint32_t {const_name} = (1u << {bit});")
    lines.append("")

    field_overrides = {
        "DEVFEAT_FIELD_RX_FIFO_DEPTH": "kFeatWord0RxFifoLsb",
        "DEVFEAT_FIELD_TX_FIFO_DEPTH": "kFeatWord0TxFifoLsb",
        "DEVFEAT_FIELD_DMA_CHANNELS": "kFeatWord0DmaChannelsLsb",
        "DEVFEAT_FIELD_TIMER_COUNT": "kFeatWord0TimerCountLsb",
        "DEVFEAT_FIELD_TIMESTAMP_BITS": "kFeatWord1TimestampBitsLsb",
        "DEVFEAT_FIELD_QUEUE_COUNT": "kFeatWord1QueueCountLsb",
        "DEVFEAT_FIELD_QUEUE_DEPTH": "kFeatWord1QueueDepthLsb",
    }
    for name, (word, lsb, _width) in feat_fields.items():
        if name in field_overrides:
            const_name = field_overrides[name]
        else:
            const_name = f"kFeatWord{word}" + _to_pascal(name.replace("DEVFEAT_FIELD_", "").split("_")) + "Lsb"
        lines.append(f"constexpr unsigned {const_name} = {lsb};")
    lines.append("")
    lines.append("} // namespace carbon_sim")
    lines.append("")

    _write_text_unix(path, "\n".join(lines))


def _load_bdt_manifest(
    path: Path,
    class_map: Dict[str, int],
    compat_bits: Dict[str, int],
    turbo_bits: Dict[str, int],
    feat_fields: Dict[str, Tuple[int, int, int]],
) -> Tuple[Dict[str, Any], List[Dict[str, int]]]:
    data = _load_yaml(path)
    if "bdt" not in data or not isinstance(data["bdt"], dict):
        raise SpecError(f"{path.as_posix()}: missing top-level bdt mapping")
    bdt = data["bdt"]
    _require_keys(bdt, ["base_addr", "region_bytes", "devices"], where=path.as_posix())
    devices_raw = bdt["devices"]
    _expect_type(devices_raw, list, where=f"{path.as_posix()}:devices")

    devices = [
        _parse_device(
            dev,
            index,
            class_map,
            compat_bits,
            turbo_bits,
            feat_fields,
        )
        for index, dev in enumerate(devices_raw)
    ]
    return bdt, devices


def _build_bdt_image(
    bdt: Dict[str, Any],
    devices: List[Dict[str, int]],
    bdt_header: Dict[str, Any],
    desc: Dict[str, Any],
) -> List[int]:
    region_bytes = int(bdt["region_bytes"])
    entry_size = int(desc["size_bytes"])
    header_size = int(bdt_header["size_bytes"])
    header_version = int(bdt_header["version"])
    desc_version = int(desc["version"])

    total_size = header_size + entry_size * len(devices)
    if total_size > region_bytes:
        raise SpecError(
            f"BDT image exceeds region_bytes ({total_size} > {region_bytes})"
        )

    image = [0 for _ in range(region_bytes)]
    _write_u32(image, 0, 0x54444243)
    _write_u16(image, 4, header_version)
    _write_u16(image, 6, header_size)
    _write_u16(image, 8, entry_size)
    _write_u16(image, 10, len(devices))
    _write_u32(image, 12, total_size)

    for i, dev in enumerate(devices):
        base = header_size + i * entry_size
        _write_u16(image, base + 0, desc_version)
        _write_u16(image, base + 2, entry_size)
        _write_u16(image, base + 4, dev["class_id"])
        _write_u16(image, base + 6, dev["subclass_id"])
        _write_u16(image, base + 8, dev["vendor_id"])
        _write_u16(image, base + 10, dev["device_id"])
        _write_u16(image, base + 12, dev["instance_id"])
        _write_u16(image, base + 14, dev["revision_id"])
        _write_u32(image, base + 16, dev["compat_flags"])
        _write_u32(image, base + 20, dev["turbo_flags"])
        _write_u32(image, base + 24, dev["feature_word0"])
        _write_u32(image, base + 28, dev["feature_word1"])
        _write_u64(image, base + 32, dev["csr_base"])
        _write_u64(image, base + 40, dev["compat_io_base"])
        _write_u64(image, base + 48, dev["mmio_base"])
        _write_u32(image, base + 56, dev["mmio_size"])
        _write_u16(image, base + 60, dev["queue_count"])
        _write_u16(image, base + 62, dev["irq_count"])

    return image


def main(argv: Sequence[str]) -> int:
    parser = argparse.ArgumentParser(description="Generate BDT ROM images and Carbon constants.")
    parser.add_argument(
        "--repo-root",
        default=None,
        help="Path to repository root (defaults to auto-detect from script location).",
    )
    args = parser.parse_args(argv)

    repo_root = Path(args.repo_root) if args.repo_root else Path(__file__).resolve().parents[1]
    spec_dir = repo_root / "hdl" / "spec"
    systems_dir = repo_root / "hdl" / "systems"

    try:
        dev = _load_yaml(spec_dir / "device_model.yaml")
        disc = _load_yaml(spec_dir / "discovery.yaml")

        class_map = _build_class_map(dev)
        compat_bits = _build_bit_map(dev["compat_feature_bits"]["bits"])
        turbo_bits = _build_bit_map(dev["turbo_feature_bits"]["bits"])
        feat_fields = _build_feature_fields(dev)

        _emit_carbon_constants(
            repo_root / "source" / "sim" / "carbon_sim" / "include" / "carbon_sim" / "util" / "carbon_constants.h",
            dev,
            disc,
            class_map,
            compat_bits,
            turbo_bits,
            feat_fields,
        )

        bdt_header = dev["bdt_header"]
        desc = dev["device_capability_descriptor"]

        manifests = list(systems_dir.glob("*/docs/BDT.yaml"))
        if not manifests:
            raise SpecError("No BDT manifests found under hdl/systems/*/docs/BDT.yaml")

        for manifest in manifests:
            bdt, devices = _load_bdt_manifest(
                manifest, class_map, compat_bits, turbo_bits, feat_fields
            )
            image = _build_bdt_image(bdt, devices, bdt_header, desc)
            out_dir = manifest.parents[1] / "rtl"
            out_dir.mkdir(parents=True, exist_ok=True)
            _emit_sv_bdt(out_dir / "bdt_image.svh", image)

        return 0
    except SpecError as exc:
        print(f"gen_bdt.py: ERROR: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
