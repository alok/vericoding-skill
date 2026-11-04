"""Packaging checks: the manifests parse, and every place that states the version agrees."""

from __future__ import annotations

import json
import re
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SKILL = ROOT / "skills" / "vericoding"


def versions() -> dict[str, str]:
    out: dict[str, str] = {}
    for rel in ["plugin.json", ".claude-plugin/plugin.json", "gemini-extension.json"]:
        out[rel] = json.loads((ROOT / rel).read_text())["version"]
    market = json.loads((ROOT / ".claude-plugin/marketplace.json").read_text())
    out["marketplace metadata"] = market["metadata"]["version"]
    for p in market["plugins"]:
        out[f"marketplace plugin {p['name']}"] = p["version"]
    m = re.search(r'^VERSION = "([^"]+)"', (SKILL / "scripts/vc_check.py").read_text(), re.MULTILINE)
    out["vc_check.py"] = m.group(1) if m else "missing"
    m = re.search(r"^  version: (\S+)", (SKILL / "SKILL.md").read_text(), re.MULTILINE)
    out["SKILL.md"] = m.group(1) if m else "missing"
    return out


class ManifestTest(unittest.TestCase):
    def test_versions_agree(self) -> None:
        v = versions()
        self.assertEqual(len(set(v.values())), 1, v)

    def test_names(self) -> None:
        self.assertEqual(json.loads((ROOT / ".claude-plugin/plugin.json").read_text())["name"], "vericoding")
        front = (SKILL / "SKILL.md").read_text().split("---")[1]
        self.assertRegex(front, r"(?m)^name: vericoding$")

    def test_every_example_has_a_solution(self) -> None:
        tasks = [p for p in (SKILL / "examples").glob("*/*") if p.is_file()]
        self.assertGreaterEqual(len(tasks), 7)
        for t in tasks:
            with self.subTest(task=t.name):
                self.assertTrue((t.parent / "solved" / t.name).is_file())

    def test_skill_md_mentions_every_example(self) -> None:
        text = (SKILL / "SKILL.md").read_text()
        for t in (SKILL / "examples").glob("*/*"):
            if t.is_file():
                with self.subTest(task=t.name):
                    self.assertIn(t.stem, text)


if __name__ == "__main__":
    unittest.main()
