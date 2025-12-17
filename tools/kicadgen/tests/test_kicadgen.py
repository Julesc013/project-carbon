import json
import os
import tempfile
import unittest
from pathlib import Path
from subprocess import PIPE, run


def _parse_sexp(text: str):
    """
    Minimal S-expression parser sufficient for validating our generated KiCad files.
    Atoms are returned as strings, lists as Python lists.
    """

    tokens = []
    i = 0
    n = len(text)
    while i < n:
        ch = text[i]
        if ch.isspace():
            i += 1
            continue
        if ch == "(" or ch == ")":
            tokens.append(ch)
            i += 1
            continue
        if ch == '"':
            i += 1
            out = []
            while i < n:
                ch = text[i]
                if ch == '"':
                    i += 1
                    break
                if ch == "\\":
                    i += 1
                    if i >= n:
                        raise ValueError("unterminated escape")
                    esc = text[i]
                    if esc == "n":
                        out.append("\n")
                    elif esc == "r":
                        out.append("\r")
                    elif esc == "t":
                        out.append("\t")
                    else:
                        out.append(esc)
                    i += 1
                    continue
                out.append(ch)
                i += 1
            tokens.append("".join(out))
            continue

        # bare atom
        j = i
        while j < n and (not text[j].isspace()) and text[j] not in "()":
            j += 1
        tokens.append(text[i:j])
        i = j

    def parse_list(idx: int):
        if tokens[idx] != "(":
            raise ValueError("expected (")
        idx += 1
        out = []
        while idx < len(tokens) and tokens[idx] != ")":
            if tokens[idx] == "(":
                node, idx = parse_list(idx)
                out.append(node)
            else:
                out.append(tokens[idx])
                idx += 1
        if idx >= len(tokens) or tokens[idx] != ")":
            raise ValueError("expected )")
        return out, idx + 1

    tree, next_idx = parse_list(0)
    if next_idx != len(tokens):
        raise ValueError("trailing tokens")
    return tree


class TestKicadGen(unittest.TestCase):
    def test_generates_minimal_core_and_system_files(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            (root / "schem/kicad9/spec").mkdir(parents=True)
            (root / "schem/kicad9/generated").mkdir(parents=True)

            common = {
                "schema_version": 1,
                "kicad": {"version": 20250114, "generator": "kicadgen", "generator_version": "0.1"},
                "layout": {"paper": "A4", "title_block": {"company": "TestCo"}},
                "interfaces": {
                    "fabric_if": {
                        "ports": [
                            {"name": "FAB_ADDR[31:0]", "dir": "output"},
                            {"name": "FAB_RDATA[31:0]", "dir": "input"},
                        ]
                    }
                },
            }
            cores = {
                "schema_version": 1,
                "cores": [
                    {
                        "name": "Z85",
                        "out_dir": "schem/kicad9/generated/cores/Z85",
                        "top_schematic": "Z85.kicad_sch",
                        "interfaces": ["fabric_if"],
                        "blocks": [{"name": "frontend", "sheet_file": "blk_frontend.kicad_sch"}],
                    }
                ],
            }
            systems = {
                "schema_version": 1,
                "systems": [
                    {
                        "name": "CarbonZ80",
                        "out_dir": "schem/kicad9/generated/systems/CarbonZ80",
                        "top_schematic": "CarbonZ80.kicad_sch",
                        "cpu_core": "Z85",
                        "accel_core": "",
                        "memory": ["ROM"],
                        "adapters": [],
                    }
                ],
            }

            (root / "schem/kicad9/spec/kicadgen_common.yaml").write_text(json.dumps(common), encoding="utf-8")
            (root / "schem/kicad9/spec/kicadgen_cores.yaml").write_text(json.dumps(cores), encoding="utf-8")
            (root / "schem/kicad9/spec/kicadgen_systems.yaml").write_text(json.dumps(systems), encoding="utf-8")

            script = Path(__file__).resolve().parents[1] / "src" / "kicadgen.py"
            proc = run(
                ["python", str(script), "--root", str(root)],
                stdout=PIPE,
                stderr=PIPE,
                encoding="utf-8",
            )
            self.assertEqual(proc.returncode, 0, msg=proc.stderr)

            top = root / "schem/kicad9/generated/cores/Z85/Z85.kicad_sch"
            self.assertTrue(top.exists())
            data = top.read_text(encoding="utf-8")
            tree = _parse_sexp(data)
            self.assertEqual(tree[0], "kicad_sch")

            # Ensure a hierarchical label exists.
            self.assertIn("hierarchical_label", data)
            self.assertIn("FAB_ADDR[31:0]", data)

            sys_top = root / "schem/kicad9/generated/systems/CarbonZ80/CarbonZ80.kicad_sch"
            self.assertTrue(sys_top.exists())
            sys_text = sys_top.read_text(encoding="utf-8")
            self.assertIn("sheet", sys_text)
            self.assertIn("blk_cpu", sys_text)
