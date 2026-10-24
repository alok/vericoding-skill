"""Tests for scripts/vc_check.py. Run with `python3 -m unittest discover -s tests`."""

from __future__ import annotations

import contextlib
import io
import shutil
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SKILL = ROOT / "skills" / "vericoding"
sys.path.insert(0, str(SKILL / "scripts"))

import vc_check as vc  # noqa: E402

L, D, V = vc.Lang.LEAN, vc.Lang.DAFNY, vc.Lang.VERUS
HAVE_LEAN = shutil.which("lean") is not None


def errors(text: str, lang: vc.Lang) -> list[str]:
    return [f.why for f in vc.scan_text(text, lang) if f.severity == "error"]


def warnings(text: str, lang: vc.Lang) -> list[str]:
    return [f.why for f in vc.scan_text(text, lang) if f.severity == "warning"]


class MaskTest(unittest.TestCase):
    def assert_same_shape(self, a: str, b: str) -> None:
        self.assertEqual(len(a), len(b))
        self.assertEqual([i for i, c in enumerate(a) if c == "\n"], [i for i, c in enumerate(b) if c == "\n"])

    def test_lean_comments_and_strings(self) -> None:
        src = 'def x := "sorry" -- sorry\n/- outer /- sorry -/ still -/ theorem t : True := trivial\n'
        m = vc.mask(src, L)
        self.assert_same_shape(src, m)
        self.assertNotIn("sorry", m)
        self.assertIn("theorem t", m)

    def test_lean_primes_are_not_char_literals(self) -> None:
        src = "theorem h' (x' : Nat) : x' = x' := rfl\ndef c := 'a'\n"
        m = vc.mask(src, L)
        self.assertIn("x' = x'", m)
        self.assertNotIn("'a'", m.replace("' '", ""))

    def test_dafny_verbatim_string(self) -> None:
        src = 'method M() { var s := @"a ""assume"" b"; } // assume\n'
        self.assertNotIn("assume", vc.mask(src, D))

    def test_rust_raw_string_and_lifetime(self) -> None:
        src = 'fn f<\'a>(x: &\'a str) -> &\'a str { let s = r#"admit()"#; x }\n'
        m = vc.mask(src, V)
        self.assertNotIn("admit", m)
        self.assertIn("&'a str", m)

    def test_comments_only_keeps_strings(self) -> None:
        src = 'ensures s == "abc" // note\n'
        m = vc.mask(src, D, strings=False)
        self.assertIn('"abc"', m)
        self.assertNotIn("note", m)


class ScanTest(unittest.TestCase):
    def test_lean_errors(self) -> None:
        for src in [
            "theorem t : False := by sorry",
            "theorem t : False := by admit",
            "axiom cheat : False",
            "@[implemented_by foo] def f := 1",
            "@[extern \"c_f\"] opaque f : Nat",
            "unsafe def f : Nat := 1",
            "set_option debug.skipKernelTC true",
            "#exit",
            "run_cmd pure ()",
            "#eval (1 : Nat)",
        ]:
            with self.subTest(src=src):
                self.assertTrue(errors(src, L), src)

    def test_lean_clean_or_warning_only(self) -> None:
        clean = [
            "#print axioms foo",
            "theorem t (cur : List.Cursor xs) : cur.prefix.length ≤ xs.length := sorryless",
            "set_option maxHeartbeats 400000 in\ntheorem t : True := trivial",
            "set_option linter.deprecated.syntax false",
            "-- a comment saying sorry\ntheorem t : True := trivial",
        ]
        for src in clean:
            with self.subTest(src=src):
                self.assertEqual(errors(src, L), [])
                self.assertEqual(warnings(src, L), [])
        for src in ["set_option autoImplicit true", "local instance : Mul Nat := ⟨Nat.add⟩",
                    "notation \"⊕\" => Nat.add", "def f := by native_decide", "noncomputable def f : Nat := 0"]:
            with self.subTest(src=src):
                self.assertEqual(errors(src, L), [])
                self.assertTrue(warnings(src, L), src)

    def test_dafny(self) -> None:
        self.assertTrue(errors("method M() { assume false; }", D))
        self.assertTrue(errors("lemma {:axiom} L() ensures false {}", D))
        self.assertTrue(errors("method {:verify false} M() {}", D))
        self.assertTrue(errors("method M(x: int) { expect x > 0; }", D))
        self.assertTrue(errors("lemma L(x: int)\n  ensures x > x + 1\n\nmethod M() {}\n", D))
        self.assertEqual(errors("lemma L(x: int)\n  ensures x + 0 == x\n{}\n", D), [])
        self.assertTrue(warnings("method M(n: int) decreases * { while true decreases * {} }", D))

    def test_verus(self) -> None:
        self.assertTrue(errors("fn f() { assume(false); }", V))
        self.assertTrue(errors("proof fn p() ensures false { admit(); }", V))
        self.assertTrue(errors("#[verifier::external_body]\nfn f() {}", V))
        self.assertTrue(errors("fn f() -> u8 { unimplemented!() }", V))
        self.assertEqual(errors("fn f() -> (r: u8) ensures r == 0 { 0 }", V), [])
        self.assertTrue(warnings("use std::collections::HashMap;", V))


LEAN_TASK = (SKILL / "examples/lean/SumOdds.lean").read_text()
LEAN_SOLVED = (SKILL / "examples/lean/solved/SumOdds.lean").read_text()
BENCH_TASK = (SKILL / "examples/lean/FindFirst.lean").read_text()
BENCH_SOLVED = (SKILL / "examples/lean/solved/FindFirst.lean").read_text()

DAFNY_TASK = """\
function Sum(s: seq<int>): int
{
  if |s| == 0 then 0 else s[0] + Sum(s[1..])
}

method SumArray(a: array<int>) returns (r: int)
  ensures r == Sum(a[..])
  ensures r in {r, 0}
{
  assume false;
}
"""
DAFNY_SOLVED = DAFNY_TASK.replace(
    "{\n  assume false;\n}",
    "{\n  r := 0;\n  var k := a.Length;\n  while k > 0\n    invariant 0 <= k <= a.Length\n"
    "    invariant r == Sum(a[k..])\n  {\n    k := k - 1;\n    r := r + a[k];\n  }\n}",
).replace("method SumArray", "lemma Helper()\n  ensures true\n{}\n\nmethod SumArray")

VERUS_TASK = """\
use vstd::prelude::*;
verus! {
spec fn double(x: int) -> int { 2 * x }

fn twice(x: u8) -> (r: u16)
    ensures
        r == double(x as int),
{
    assume(false);
    0
}

fn main() {}
}
"""
VERUS_SOLVED = VERUS_TASK.replace("    assume(false);\n    0\n", "    (x as u16) * 2\n")


class HolesTest(unittest.TestCase):
    def kinds(self, text: str, lang: vc.Lang) -> tuple[str, list[str]]:
        mode, holes = vc.compute_holes(text, lang)
        return mode, [h.kind for h in holes]

    def test_lean_general(self) -> None:
        mode, kinds = self.kinds(LEAN_TASK, L)
        self.assertEqual(mode, "general")
        self.assertEqual(kinds.count("sorry"), 2)
        self.assertIn("insert", kinds)

    def test_lean_benchmark(self) -> None:
        mode, holes = vc.compute_holes(BENCH_TASK, L)
        self.assertEqual(mode, "benchmark")
        self.assertEqual(sorted(h.kind for h in holes), ["region", "sorry", "sorry"])

    def test_lean_preamble_sorry_is_frozen(self) -> None:
        text = BENCH_TASK.replace("def findFirst_precond (xs : List Int) (target : Int) : Prop := True",
                                  "def findFirst_precond (xs : List Int) (target : Int) : Prop := True\n"
                                  "theorem given : True := sorry")
        _, holes = vc.compute_holes(text, L)
        given = text.index("theorem given")
        self.assertFalse(any(h.start <= given + 25 < h.end for h in holes))

    def test_dafny_general(self) -> None:
        _, holes = vc.compute_holes(DAFNY_TASK, D)
        bodies = [h for h in holes if h.kind == "body"]
        self.assertEqual(len(bodies), 1)
        self.assertIn("assume false", DAFNY_TASK[bodies[0].start : bodies[0].end])
        self.assertTrue(DAFNY_TASK[bodies[0].start : bodies[0].end].startswith("{\n  assume"))

    def test_verus_general(self) -> None:
        _, holes = vc.compute_holes(VERUS_TASK, V)
        bodies = [VERUS_TASK[h.start : h.end] for h in holes if h.kind == "body"]
        self.assertTrue(any("assume(false)" in b for b in bodies))
        self.assertFalse(any("2 * x" in b for b in bodies))


class FreezeTest(unittest.TestCase):
    def ok(self, orig: str, cur: str, lang: vc.Lang) -> bool:
        return vc.freeze_check(orig, cur, lang).ok

    def test_lean_solution_passes(self) -> None:
        self.assertTrue(self.ok(LEAN_TASK, LEAN_SOLVED, L))
        self.assertTrue(self.ok(BENCH_TASK, BENCH_SOLVED, L))

    def test_lean_weakened_statement_fails(self) -> None:
        cur = LEAN_SOLVED.replace("sumOdds n = n * n", "sumOdds n = sumOdds n")
        self.assertFalse(self.ok(LEAN_TASK, cur, L))

    def test_lean_continuation_insert_fails(self) -> None:
        # Text at an insertion point that doesn't start a declaration would extend the frozen
        # definition before it: here it would weaken `post` to `n > 0 ∨ True`.
        task = "def post (n : Nat) : Prop := n > 0\n\ntheorem t : post 1 := by\n  sorry\n"
        cur = "def post (n : Nat) : Prop := n > 0\n∨ True\n\ntheorem t : post 1 := by\n  simp [post]\n"
        r = vc.freeze_check(task, cur, L)
        self.assertFalse(r.ok)
        self.assertIn("must start a new declaration", r.problems[0])

    def test_lean_helper_and_import_inserts_pass(self) -> None:
        cur = "import Std.Tactic.Do\n" + LEAN_SOLVED.replace(
            "/-- The closed form. -/", "theorem helper : 1 + 1 = 2 := rfl\n\n/-- The closed form. -/")
        self.assertTrue(self.ok(LEAN_TASK, cur, L))

    def test_lean_comment_edits_pass(self) -> None:
        cur = LEAN_SOLVED.replace("/-- The closed form. -/", "/-- The closed form, proved. -/")
        self.assertTrue(self.ok(LEAN_TASK, cur, L))

    def test_lean_benchmark_postcond_edit_fails(self) -> None:
        cur = BENCH_SOLVED.replace("| none => target ∉ xs\n\ntheorem findFirst_spec", "| none => True\n\ntheorem findFirst_spec")
        self.assertNotEqual(cur, BENCH_SOLVED)
        self.assertFalse(self.ok(BENCH_TASK, cur, L))

    def test_dafny(self) -> None:
        self.assertTrue(self.ok(DAFNY_TASK, DAFNY_SOLVED, D))
        self.assertFalse(self.ok(DAFNY_TASK, DAFNY_SOLVED.replace("ensures r == Sum(a[..])", "ensures true"), D))
        self.assertFalse(self.ok(DAFNY_TASK, DAFNY_SOLVED.replace("s[0] + Sum(s[1..])", "0"), D))
        self.assertFalse(self.ok(DAFNY_TASK, DAFNY_SOLVED.replace("lemma Helper()", "  requires false\nlemma Helper()"), D))

    def test_verus(self) -> None:
        self.assertTrue(self.ok(VERUS_TASK, VERUS_SOLVED, V))
        self.assertFalse(self.ok(VERUS_TASK, VERUS_SOLVED.replace("r == double(x as int)", "true"), V))
        self.assertFalse(self.ok(VERUS_TASK, VERUS_SOLVED.replace("{ 2 * x }", "{ x }"), V))

    def test_benchmark_dafny(self) -> None:
        task = ("// <vc-preamble>\nfunction F(x: int): int { x + 1 }\n// </vc-preamble>\n\n"
                "// <vc-helpers>\n// </vc-helpers>\n\n// <vc-spec>\nmethod M(x: int) returns (r: int)\n"
                "  ensures r == F(x)\n// </vc-spec>\n// <vc-code>\n{\n  assume {:axiom} false;\n}\n// </vc-code>\n")
        solved = task.replace("{\n  assume {:axiom} false;\n}", "{\n  r := x + 1;\n}")
        self.assertTrue(self.ok(task, solved, D))
        self.assertFalse(self.ok(task, solved.replace("ensures r == F(x)", "ensures true"), D))


class SnapshotTest(unittest.TestCase):
    def test_refreeze_refused_after_change(self) -> None:
        with tempfile.TemporaryDirectory() as d:
            f = Path(d) / "T.lean"
            f.write_text(LEAN_TASK)
            store = str(Path(d) / ".vc")
            quiet = contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO())
            with quiet[0], quiet[1]:
                self.assertEqual(vc.main(["freeze", str(f), "--store", store]), 0)
                f.write_text(LEAN_TASK.replace("n * n", "n"))
                self.assertEqual(vc.main(["freeze", str(f), "--store", store]), 2)
                self.assertEqual(vc.main(["freeze", str(f), "--store", store, "--force"]), 0)


@unittest.skipUnless(HAVE_LEAN, "lean not installed")
class LeanEndToEndTest(unittest.TestCase):
    def check(self, task: str, cur: str, *extra: str) -> int:
        with tempfile.TemporaryDirectory() as d:
            base, f = Path(d) / "Base.lean", Path(d) / "Cur.lean"
            base.write_text(task)
            f.write_text(cur)
            with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
                return vc.main(["check", str(f), "--base", str(base), *extra])

    def test_examples_verify(self) -> None:
        for name in ["SumOdds", "SumList", "FindFirst"]:
            with self.subTest(name=name):
                task = (SKILL / f"examples/lean/{name}.lean").read_text()
                solved = (SKILL / f"examples/lean/solved/{name}.lean").read_text()
                self.assertEqual(self.check(task, solved), 0)

    def test_untouched_task_is_not_verified(self) -> None:
        self.assertEqual(self.check(LEAN_TASK, LEAN_TASK), 1)

    def test_axiom_cheat(self) -> None:
        cur = LEAN_TASK.replace("/-- The closed form. -/", "axiom magic (n : Nat) : sumOdds n = n * n\n\n/-- The closed form. -/")
        cur = cur.replace("def sumOdds (n : Nat) : Nat := sorry", "def sumOdds (n : Nat) : Nat := n * n")
        cur = cur.replace("  sorry", "  exact magic n")
        self.assertEqual(self.check(LEAN_TASK, cur), 1)

    def test_sorry_hidden_in_macro(self) -> None:
        cur = LEAN_SOLVED.replace("/-- The closed form. -/", "macro \"trust_me\" : tactic => `(tactic| sorry)\n\n/-- The closed form. -/")
        cur = cur.replace("  induction n with\n  | zero => rfl\n  | succ k ih => simp only [sumOdds, ih]; grind", "  trust_me")
        self.assertEqual(self.check(LEAN_TASK, cur), 1)

    def test_instance_changes_meaning(self) -> None:
        cur = LEAN_SOLVED.replace(
            "/-- The closed form. -/",
            "local instance (priority := high) : Mul Nat := ⟨fun a b => Nat.mul a b + 0⟩\n\n/-- The closed form. -/")
        self.assertEqual(self.check(LEAN_TASK, cur), 1)

    def test_native_decide_needs_flag(self) -> None:
        task = "theorem big : 2 ^ 20 = 1048576 := by\n  sorry\n"
        cur = "theorem big : 2 ^ 20 = 1048576 := by\n  native_decide\n"
        self.assertEqual(self.check(task, cur), 1)
        self.assertEqual(self.check(task, cur, "--allow-native"), 0)


if __name__ == "__main__":
    unittest.main()
