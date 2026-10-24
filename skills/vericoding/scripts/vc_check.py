#!/usr/bin/env python3
# /// script
# requires-python = ">=3.10"
# dependencies = []
# ///
"""vc_check: the vericoding gate for Lean 4, Dafny and Verus.

A file counts as verified only when the verifier accepts it, nothing the agent
wrote is a verification bypass, and the spec is exactly what it was before the
agent started.

    vc_check.py freeze FILE         snapshot the spec before editing
    vc_check.py holes FILE          show what may be edited
    vc_check.py check FILE          the gate: freeze + bypass scan + verifier
    vc_check.py scan FILE           bypass scan only (no snapshot needed)

Exit status: 0 verified (or scan clean), 1 not verified, 2 tool or usage error.
Standard library only; runs with `python3` or `uv run`.
"""

from __future__ import annotations

import argparse
import datetime as _dt
import enum
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import time
from dataclasses import asdict, dataclass, field
from pathlib import Path
from typing import Sequence

VERSION = "0.1.0"


class Lang(str, enum.Enum):
    LEAN = "lean"
    DAFNY = "dafny"
    VERUS = "verus"


EXTENSIONS: dict[str, Lang] = {".lean": Lang.LEAN, ".dfy": Lang.DAFNY, ".rs": Lang.VERUS}


def detect_lang(path: Path, override: str | None = None) -> Lang:
    if override:
        return Lang(override)
    try:
        return EXTENSIONS[path.suffix]
    except KeyError:
        raise UsageError(f"can't tell the language of {path}; pass --lang lean|dafny|verus") from None


class UsageError(Exception):
    pass


# ---------------------------------------------------------------------------
# Lexing: blank out comments and/or string literals, keeping every offset.
# ---------------------------------------------------------------------------

_CHAR_LIT = re.compile(r"'(?:\\(?:x[0-9a-fA-F]{2}|u\{?[0-9a-fA-F]+\}?|.)|[^'\\\n])'")
_RAW_STR = re.compile(r'b?r(#*)"')


def _is_ident(ch: str, lang: Lang) -> bool:
    return ch.isalnum() or ch in "_'" or (lang is Lang.LEAN and ch in "!?.")


def _blank(buf: list[str], a: int, b: int) -> None:
    for k in range(a, b):
        if buf[k] != "\n":
            buf[k] = " "


def mask(text: str, lang: Lang, *, comments: bool = True, strings: bool = True) -> str:
    """Replace comment and/or string-literal characters with spaces.

    Newlines survive, so offsets and line numbers in the result match `text`.
    Block comments nest in all three languages.
    """
    buf = list(text)
    n = len(text)
    line_c = "--" if lang is Lang.LEAN else "//"
    open_c, close_c = ("/-", "-/") if lang is Lang.LEAN else ("/*", "*/")
    i = 0
    while i < n:
        if text.startswith(line_c, i):
            j = text.find("\n", i)
            j = n if j < 0 else j
            if comments:
                _blank(buf, i, j)
            i = j
            continue
        if text.startswith(open_c, i):
            depth, j = 1, i + 2
            while j < n and depth:
                if text.startswith(open_c, j):
                    depth, j = depth + 1, j + 2
                elif text.startswith(close_c, j):
                    depth, j = depth - 1, j + 2
                else:
                    j += 1
            if comments:
                _blank(buf, i, j)
            i = j
            continue
        ch = text[i]
        prev_ident = i > 0 and _is_ident(text[i - 1], lang)
        if not prev_ident and ch in "rb" and lang is not Lang.DAFNY:
            m = _RAW_STR.match(text, i)
            if m:
                close = '"' + m.group(1)
                j = text.find(close, m.end())
                j = n if j < 0 else j + len(close)
                if strings:
                    _blank(buf, m.end(), max(m.end(), j - len(close)))
                i = j
                continue
        if ch == '"' or (lang is Lang.DAFNY and text.startswith('@"', i)):
            verbatim = ch == "@"
            j = i + (2 if verbatim else 1)
            while j < n:
                if verbatim and text.startswith('""', j):
                    j += 2
                elif not verbatim and text[j] == "\\":
                    j += 2
                elif text[j] == '"':
                    break
                else:
                    j += 1
            j = min(j + 1, n)
            if strings:
                _blank(buf, i + (2 if verbatim else 1), j - 1)
            i = j
            continue
        if ch == "'" and not prev_ident:
            m = _CHAR_LIT.match(text, i)
            if m:
                if strings:
                    _blank(buf, i + 1, m.end() - 1)
                i = m.end()
                continue
        i += 1
    return "".join(buf)


def line_col(text: str, offset: int) -> tuple[int, int]:
    line = text.count("\n", 0, offset) + 1
    col = offset - (text.rfind("\n", 0, offset) + 1) + 1
    return line, col


def match_brace(m: str, j: int) -> int:
    """Index of the `}` closing the `{` at `j` in masked text (or len-1)."""
    depth = 0
    for k in range(j, len(m)):
        if m[k] == "{":
            depth += 1
        elif m[k] == "}":
            depth -= 1
            if depth == 0:
                return k
    return len(m) - 1


# ---------------------------------------------------------------------------
# Bypass rules.
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class Rule:
    pattern: re.Pattern[str]
    severity: str  # "error" | "warning"
    why: str


def _r(p: str, severity: str, why: str) -> Rule:
    return Rule(re.compile(p, re.MULTILINE), severity, why)


RULES: dict[Lang, list[Rule]] = {
    Lang.LEAN: [
        _r(r"\bsorry\b", "error", "`sorry` leaves the goal unproved"),
        _r(r"\badmit\b", "error", "`admit` leaves the goal unproved"),
        _r(r"\baxiom\b", "error", "an `axiom` is an unproved assumption"),
        _r(r"\bsorryAx\b|\blcProof\b", "error", "direct use of an unsound primitive"),
        _r(r"\bunsafe\b", "error", "`unsafe` code is outside the logic"),
        _r(r"\bimplemented_by\b", "error", "`implemented_by` runs code the proof never saw"),
        _r(r"@\[[^\]]*\bextern\b", "error", "`@[extern]` runs code the proof never saw"),
        _r(r"\bdebug\.skipKernelTC\b", "error", "skips kernel type checking"),
        _r(r"^\s*#exit\b", "error", "`#exit` stops Lean before the rest of the file is checked"),
        _r(r"\b(?:run_cmd|run_elab|run_meta)\b|^\s*#eval\b", "error",
           "metaprograms can change the environment behind the kernel's back"),
        _r(r"\b(?:addDecl|addAndCompile|modifyEnv|setEnv)\b", "error",
           "editing the environment directly bypasses elaboration"),
        _r(r"\bnative_decide\b|\bofReduceBool\b|\bdecide\s*\+\s*native\b", "warning",
           "trusts the compiler (axiom `Lean.ofReduceBool`); say so in the report"),
        _r(r"\bnoncomputable\b", "warning",
           "a noncomputable implementation can't run; make sure it isn't the spec's own witness"),
        _r(r"\bClassical\.(?:choose|choice|epsilon|indefiniteDescription)\b|\bExists\.choose\b",
           "warning", "choice in an implementation usually means the spec was copied, not implemented"),
        _r(r"\bpartial\s+def\b", "warning",
           "`partial def` bodies are opaque, so nothing can be proved about them"),
        _r(r"^\s*(?:@\[[^\]]*\]\s*)?(?:(?:local|scoped|private)\s+)*(?:macro|macro_rules|syntax|notation|"
           r"infixl?|infixr|prefix|postfix|elab|elab_rules|declare_syntax_cat|simproc|dsimproc)\b", "warning",
           "new syntax can change what frozen text means; justify it"),
        _r(r"^\s*(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|scoped|local)\s+)*instance\b", "warning",
           "a new instance can change how a frozen statement elaborates"),
        _r(r"^\s*set_option\b(?!\s+(?:maxHeartbeats|maxRecDepth|synthInstance\.maxHeartbeats|linter\.[\w.]+|"
           r"mvcgen\.warning|grind\.warning|trace\.[\w.]+|diagnostics)\b)",
           "warning", "options can change how later frozen text elaborates"),
        _r(r"^\s*attribute\s*\[\s*-", "warning", "removing attributes can change elaboration"),
    ],
    Lang.DAFNY: [
        _r(r"\bassume\b", "error", "`assume` is an unproved assumption"),
        _r(r"\{:\s*axiom\b", "error", "`{:axiom}` marks an unproved assumption"),
        _r(r"\{:\s*verify\s+false\s*\}", "error", "`{:verify false}` turns verification off"),
        _r(r"\{:\s*only\b", "error", "`{:only}` skips verifying everything else"),
        _r(r"\{:\s*extern\b", "error", "`{:extern}` trusts code outside Dafny"),
        _r(r"\{:\s*termination\s+false\s*\}", "error", "`{:termination false}` skips termination"),
        _r(r"\bexpect\b", "error", "the verifier assumes an `expect` holds; it's a runtime check, not a proof"),
        _r(r"\bdecreases\s*\*", "warning", "`decreases *` gives up on termination"),
        _r(r"\{:\s*compile\s+false\s*\}", "warning", "code that is never compiled"),
    ],
    Lang.VERUS: [
        _r(r"\bassume\s*\(", "error", "`assume` is an unproved assumption"),
        _r(r"\badmit\s*\(", "error", "`admit()` leaves the goal unproved"),
        _r(r"\bexternal_body\b", "error", "`external_body` trusts an unverified body"),
        _r(r"verifier\s*::\s*external\b|verifier\s*\(\s*external\s*\)", "error",
           "`external` code is never verified"),
        _r(r"\bassume_specification\b|\bexternal_fn_specification\b", "error",
           "trusted specification with no proof"),
        _r(r"\b(?:unimplemented|todo)!\s*\(", "error", "placeholder body"),
        _r(r"\bunsafe\b", "error", "`unsafe` code is outside the logic"),
        _r(r"\bexec_allows_no_decreases_clause\b", "warning", "allows non-termination"),
        _r(r"verifier\s*::\s*truncate\b", "warning", "truncating cast; check the spec allows it"),
        _r(r"\buninterp\b", "warning", "an uninterpreted function is an assumption about nothing"),
        _r(r"#\s*\[\s*cfg\b|\bverus_keep_ghost\b", "warning", "cfg can hide code from the verifier"),
        _r(r"^\s*(?:pub\s+)?use\b", "warning", "a new import can shadow names a frozen spec uses"),
        _r(r"\bmacro_rules!", "warning", "new macros can change what frozen text means"),
    ],
}


@dataclass
class Finding:
    severity: str
    line: int
    col: int
    text: str
    why: str


def scan_text(text: str, lang: Lang, spans: Sequence[tuple[int, int]] | None = None) -> list[Finding]:
    """Bypass findings in `text`, limited to `spans` (offsets) when given."""
    masked = mask(text, lang)
    if spans is None:
        spans = [(0, len(text))]
    found: list[Finding] = []
    for a, b in spans:
        if a >= b:
            continue
        for rule in RULES[lang]:
            for m in rule.pattern.finditer(masked, a, b):
                start = m.start() + (len(m.group(0)) - len(m.group(0).lstrip()))
                line, col = line_col(text, start)
                snippet = text[start : text.find("\n", start) if "\n" in text[start:] else len(text)]
                found.append(Finding(rule.severity, line, col, snippet.strip()[:100], rule.why))
        if lang is Lang.DAFNY:
            for d in dafny_decls(masked):
                if a <= d.kw_start < b and d.body is None and d.kind in ("lemma", "method", "function", "predicate"):
                    line, col = line_col(text, d.kw_start)
                    found.append(Finding("error", line, col, f"{d.kind} {d.name}",
                                         f"a {d.kind} with no body is an axiom"))
    found.sort(key=lambda f: (f.line, f.col))
    return found


# ---------------------------------------------------------------------------
# Declarations, for finding bodies (Dafny, Verus) and names (Lean).
# ---------------------------------------------------------------------------


@dataclass
class Decl:
    kind: str
    name: str
    kw_start: int  # offset of the declaration's first keyword
    body: tuple[int, int] | None  # [open brace, close brace] inclusive offsets, or None


_DAFNY_DECL = re.compile(
    r"(?<![\w'?])(?:(?:ghost|static|opaque|twostate|least|greatest|abstract|private)\s+)*"
    r"(method|lemma|function|predicate|constructor|copredicate|inductive\s+predicate)\b"
    r"(?:\s+method\b)?\s*(?:\{:[^}]*\}\s*)*([\w'?.]*)"
)
_DAFNY_EXPR_KW = {
    "in", "requires", "ensures", "reads", "modifies", "decreases", "invariant", "then", "else",
    "return", "yield", "returns", "assert", "assume", "case", "var", "if", "while", "match", "by",
}


def _prev_sig(m: str, j: int) -> str:
    k = j - 1
    while k >= 0 and m[k].isspace():
        k -= 1
    if k < 0:
        return ""
    if m[k].isalnum() or m[k] in "_'?":
        e = k + 1
        while k >= 0 and (m[k].isalnum() or m[k] in "_'?"):
            k -= 1
        return m[k + 1 : e]
    return m[k]


def _find_body(m: str, start: int, lang: Lang, stop: re.Pattern[str]) -> tuple[int, int] | None:
    depth = 0
    j = start
    n = len(m)
    while j < n:
        c = m[j]
        if c in "([":
            depth += 1
        elif c in ")]":
            depth = max(0, depth - 1)
        elif c == "{":
            if depth == 0:
                if lang is Lang.DAFNY:
                    if m.startswith("{:", j):
                        j = match_brace(m, j) + 1
                        continue
                    prev = _prev_sig(m, j)
                    is_expr = prev in _DAFNY_EXPR_KW or (
                        prev != "" and not (prev[0].isalnum() or prev[0] in "_'?") and prev not in ")]}>"
                    )
                    if is_expr:
                        j = match_brace(m, j) + 1
                        continue
                return (j, match_brace(m, j))
            j = match_brace(m, j) + 1
            continue
        elif c == "}" and depth == 0:
            return None
        elif c == ";" and depth == 0 and lang is Lang.VERUS:
            return None
        elif depth == 0 and (j == 0 or not (m[j - 1].isalnum() or m[j - 1] == "_")) and stop.match(m, j):
            return None
        j += 1
    return None


_DAFNY_STOP = re.compile(
    r"(?:method|lemma|function|predicate|datatype|codatatype|class|trait|module|import|const|"
    r"type|newtype|iterator|constructor|ghost|static|twostate)\b"
)


def dafny_decls(masked: str) -> list[Decl]:
    out: list[Decl] = []
    pos = 0
    for mt in _DAFNY_DECL.finditer(masked):
        if mt.start() < pos:
            continue
        kind = mt.group(1).split()[-1]
        body = _find_body(masked, mt.end(), Lang.DAFNY, _DAFNY_STOP)
        out.append(Decl(kind, mt.group(2), mt.start(), body))
        if body:
            pos = body[1] + 1
            by = re.compile(r"\s*by\s+method\s*\{").match(masked, pos)
            if by:
                ob = by.end() - 1
                out.append(Decl("by-method", mt.group(2), by.start(), (ob, match_brace(masked, ob))))
                pos = match_brace(masked, ob) + 1
    return out


_VERUS_FN = re.compile(
    r"(?<![\w])(?:pub(?:\s*\([^)]*\))?\s+)?((?:(?:open|closed|uninterp|broadcast|spec|proof|exec|"
    r"const|async|axiom)\s+)*)fn\s+(\w+)"
)
_VERUS_STOP = re.compile(r"(?:fn|struct|enum|impl|trait|mod|use|type|pub)\b")


def verus_decls(masked: str) -> list[Decl]:
    out: list[Decl] = []
    pos = 0
    for mt in _VERUS_FN.finditer(masked):
        if mt.start() < pos:
            continue
        mods = mt.group(1).split()
        kind = "spec fn" if "spec" in mods else "proof fn" if "proof" in mods else "fn"
        body = _find_body(masked, mt.end(), Lang.VERUS, _VERUS_STOP)
        out.append(Decl(kind, mt.group(2), mt.start(), body))
        if body:
            pos = body[1] + 1
    return out


_LEAN_DECL = re.compile(
    r"^(?:@\[[^\]]*\][ \t]*\n?[ \t]*)?(?:(?:private|protected|noncomputable|partial|nonrec|unsafe|public|meta)"
    r"[ \t]+)*(theorem|lemma|def|abbrev|instance|opaque)[ \t]+([^\s:({\[⦃]+)",
    re.MULTILINE,
)
_LEAN_NS = re.compile(r"^[ \t]*(namespace|section|end)\b[ \t]*([^\s]*)", re.MULTILINE)


@dataclass
class LeanDecl:
    kind: str
    name: str  # fully qualified
    start: int
    end: int  # start of the next top-level declaration


def lean_decls(masked: str) -> list[LeanDecl]:
    events: list[tuple[int, str, str]] = []
    for m in _LEAN_NS.finditer(masked):
        events.append((m.start(), m.group(1), m.group(2)))
    for m in _LEAN_DECL.finditer(masked):
        if m.group(1) == "instance" and m.group(2) in (":", "where") or m.group(2).startswith("("):
            continue
        events.append((m.start(), m.group(1), m.group(2)))
    events.sort()
    stack: list[str | None] = []
    decls: list[LeanDecl] = []
    for off, kind, arg in events:
        if kind == "namespace":
            stack.append(arg)
        elif kind == "section":
            stack.append(None)
        elif kind == "end":
            if stack:
                stack.pop()
        else:
            if arg.startswith("_root_."):
                full = arg[len("_root_.") :]
            else:
                full = ".".join([s for s in stack if s] + [arg])
            decls.append(LeanDecl(kind, full, off, len(masked)))
    starts = sorted(o for o, _, _ in events)
    for d in decls:
        later = [s for s in starts if s > d.start]
        d.end = later[0] if later else len(masked)
    return decls


# ---------------------------------------------------------------------------
# Holes: the parts of the original the agent may change.
# ---------------------------------------------------------------------------


@dataclass
class Hole:
    start: int
    end: int
    kind: str  # "region" | "sorry" | "body" | "insert"
    label: str


_TAG = re.compile(r"^[ \t]*(?:--|//)[ \t]*<(/?)(vc-[a-z-]+)>[ \t]*\r?$", re.MULTILINE)
WHOLE_HOLE_REGIONS = {"vc-helpers", "vc-code"}
FROZEN_REGIONS = {"vc-preamble", "vc-spec", "vc-postamble", "vc-description"}

_LEAN_INSERT = re.compile(
    r"^(?=@\[|#(?!exit)|/--|(?:(?:private|protected|noncomputable|partial|nonrec|unsafe|public|meta)\s+)*"
    r"(?:theorem|lemma|def|abbrev|instance|structure|inductive|class|example|opaque|namespace|section|"
    r"open|variable|universe|set_option|attribute|mutual|macro|syntax|notation|infixl?|infixr|prefix|"
    r"postfix|elab|deriving)\b)",
    re.MULTILINE,
)
_DAFNY_INSERT_KW = (
    r"(?:\{:[^}\n]*\}\s*)*(?:(?:ghost|static|opaque|twostate|least|greatest|abstract|private)\s+)*"
    r"(?:method|lemma|function|predicate|datatype|codatatype|class|trait|module|import|const|type|newtype|"
    r"iterator|constructor)\b"
)
_VERUS_INSERT_KW = (
    r"(?:#\s*!?\[|(?:pub(?:\s*\([^)]*\))?\s+)?(?:(?:open|closed|broadcast|spec|proof|exec|const|tracked|ghost)\s+)*"
    r"(?:fn|struct|enum|impl|trait|mod|const|type|global|broadcast)\b)"
)
INSERT_START: dict[Lang, re.Pattern[str]] = {
    Lang.LEAN: re.compile(
        r"(?:@\[|#(?!exit)|(?:(?:private|protected|noncomputable|partial|nonrec|public|meta)\s+)*"
        r"(?:theorem|lemma|def|abbrev|instance|structure|inductive|class|example|namespace|section|open|"
        r"variable|universe|set_option|attribute|mutual|macro|syntax|notation|infixl?|infixr|prefix|postfix|"
        r"elab|deriving)\b)"
    ),
    Lang.DAFNY: re.compile(_DAFNY_INSERT_KW),
    Lang.VERUS: re.compile(_VERUS_INSERT_KW),
}


def regions(text: str) -> list[tuple[str, int, int]]:
    """Benchmark `<vc-…>` regions as (name, content_start, content_end)."""
    out: list[tuple[str, int, int]] = []
    open_at: dict[str, int] = {}
    for m in _TAG.finditer(text):
        closing, name = m.group(1) == "/", m.group(2)
        if not closing:
            nl = text.find("\n", m.end())
            open_at[name] = len(text) if nl < 0 else nl + 1
        elif name in open_at:
            out.append((name, open_at.pop(name), m.start()))
    out.sort(key=lambda r: r[1])
    return out


def compute_holes(text: str, lang: Lang) -> tuple[str, list[Hole]]:
    """Return (mode, holes) for an original file."""
    m = mask(text, lang)
    holes: list[Hole] = []
    regs = regions(text)
    if regs:
        mode = "benchmark"
        for name, a, b in regs:
            if name in WHOLE_HOLE_REGIONS:
                holes.append(Hole(a, b, "region", name))
            elif lang is Lang.LEAN and name not in FROZEN_REGIONS:
                for s in re.finditer(r"\bsorry\b", m[a:b]):
                    holes.append(Hole(a + s.start(), a + s.end(), "sorry", f"sorry in {name}"))
        return mode, _normalize(holes, m)
    mode = "general"
    if lang is Lang.LEAN:
        for s in re.finditer(r"\bsorry\b", m):
            holes.append(Hole(s.start(), s.end(), "sorry", "sorry"))
        for s in _LEAN_INSERT.finditer(m):
            holes.append(Hole(s.start(), s.start(), "insert", "new declarations"))
    else:
        decls = dafny_decls(m) if lang is Lang.DAFNY else verus_decls(m)
        editable = ("method", "lemma", "constructor", "by-method") if lang is Lang.DAFNY else ("fn", "proof fn")
        for d in decls:
            if d.kind in editable:
                if d.body:
                    holes.append(Hole(d.body[0], d.body[1] + 1, "body", f"body of {d.kind} {d.name}"))
                else:
                    end = _sig_end(m, d.kw_start, lang)
                    holes.append(Hole(end, end, "body", f"missing body of {d.kind} {d.name}"))
        insert_kw = _DAFNY_INSERT_KW if lang is Lang.DAFNY else _VERUS_INSERT_KW
        for s in re.finditer(r"^[ \t]*(?=" + insert_kw + ")", m, re.MULTILINE):
            holes.append(Hole(s.end(), s.end(), "insert", "new declarations"))
    holes.append(Hole(len(text), len(text), "insert", "new declarations"))
    return mode, _normalize(holes, m)


def _sig_end(m: str, start: int, lang: Lang) -> int:
    """End of a bodyless declaration's signature: just before the next declaration."""
    stop = _DAFNY_STOP if lang is Lang.DAFNY else _VERUS_STOP
    nxt = stop.search(m, start + 1)
    end = nxt.start() if nxt else len(m)
    while end > start and m[end - 1].isspace():
        end -= 1
    return end


def _normalize(holes: list[Hole], masked: str) -> list[Hole]:
    """Sort, drop holes inside other holes, merge holes separated only by whitespace or comments."""
    holes.sort(key=lambda h: (h.start, -(h.end - h.start)))
    out: list[Hole] = []
    for h in holes:
        if out and h.start < out[-1].end:
            continue  # inside the previous hole
        if out and masked[out[-1].end : h.start].strip() == "":
            prev = out[-1]
            if prev.end == h.start and prev.kind == h.kind == "insert":
                continue
            if prev.kind != "insert" or h.kind != "insert":
                kind = prev.kind if prev.kind != "insert" else h.kind
                label = prev.label if prev.kind != "insert" else h.label
                out[-1] = Hole(prev.start, max(prev.end, h.end), kind, label)
                continue
        out.append(h)
    return out


# ---------------------------------------------------------------------------
# Freeze check: every frozen segment of the original, in order, in the current.
# ---------------------------------------------------------------------------


@dataclass
class FreezeResult:
    ok: bool
    mode: str
    holes: int
    edited_holes: int
    free_spans: list[tuple[int, int]]  # offsets in the current text the agent wrote
    problems: list[str] = field(default_factory=list)


def _seg_pattern(seg: str) -> re.Pattern[str]:
    parts = [re.escape(p) for p in seg.split()]
    body = r"\s+".join(parts)
    return re.compile(r"\s*" + body + r"\s*" if parts else r"\s*")


def freeze_check(orig: str, cur: str, lang: Lang) -> FreezeResult:
    mode, holes = compute_holes(orig, lang)
    mo = mask(orig, lang, strings=False)
    mc = mask(cur, lang, strings=False)
    bounds: list[tuple[int, int]] = []
    pos = 0
    for h in holes:
        bounds.append((pos, h.start))
        pos = h.end
    bounds.append((pos, len(orig)))  # frozen segments: len(holes) + 1 of them
    res = FreezeResult(True, mode, len(holes), 0, [])
    cpos = 0
    for idx, (a, b) in enumerate(bounds):
        seg = mo[a:b]
        pat = _seg_pattern(seg)
        if idx == 0:
            mt = pat.match(mc, 0)
        else:
            mt = pat.search(mc, cpos)
        last = idx == len(bounds) - 1
        if mt and last and mc[mt.end() :].strip():
            # trailing frozen segment must end the file; try a later occurrence
            later = [x for x in pat.finditer(mc, cpos) if not mc[x.end() :].strip()]
            mt = later[0] if later else None
        if not mt:
            res.ok = False
            line_a, _ = line_col(orig, a + (len(seg) - len(seg.lstrip())))
            line_b, _ = line_col(orig, max(a, b - 1))
            res.problems.append(_describe_missing(orig[a:b], seg, mc[cpos:], line_a, line_b, cur, cpos))
            return res
        if idx > 0:
            h = holes[idx - 1]
            span = (cpos, mt.start())
            res.free_spans.append(span)
            new = mc[span[0] : span[1]]
            if new.strip() != mo[h.start : h.end].strip():
                res.edited_holes += 1
            if h.kind == "insert" and new.strip() and not INSERT_START[lang].match(new.strip()):
                res.ok = False
                line, _ = line_col(cur, span[0] + (len(new) - len(new.lstrip())))
                res.problems.append(
                    f"line {line}: text inserted between declarations must start a new declaration; "
                    f"this would extend the frozen text before it: {new.strip()[:80]!r}"
                )
        cpos = mt.end()
    return res


def _describe_missing(seg: str, mseg: str, rest: str, la: int, lb: int, cur: str, cpos: int) -> str:
    """Name the first line of a frozen segment that can't be found in the current file."""
    where = f"line {la}" if la == lb else f"lines {la}-{lb}"
    have_line, _ = line_col(cur, cpos)
    flat_rest = " ".join(rest.split())
    for raw, masked in zip(seg.splitlines(), mseg.splitlines()):
        if masked.strip() and " ".join(masked.split()) not in flat_rest:
            return (f"frozen text from the original ({where}) was changed or moved; first missing line "
                    f"(searching from current line {have_line}): {raw.strip()[:100]!r}")
    first = next((r.strip() for r, m in zip(seg.splitlines(), mseg.splitlines()) if m.strip()), seg.strip())
    return f"frozen text from the original ({where}) was changed, reordered or moved: starts {first[:80]!r}"


# ---------------------------------------------------------------------------
# Verifiers.
# ---------------------------------------------------------------------------


@dataclass
class VerifierResult:
    ran: bool
    ok: bool
    command: str
    seconds: float
    summary: str
    errors: list[str] = field(default_factory=list)
    warnings: list[str] = field(default_factory=list)
    axioms: dict[str, list[str]] = field(default_factory=dict)
    signatures: dict[str, str] = field(default_factory=dict)


def _which(name: str, env: str) -> str | None:
    return os.environ.get(env) or shutil.which(name)


def lean_root(path: Path) -> Path | None:
    for d in [path.parent, *path.parent.parents]:
        if (d / "lakefile.lean").exists() or (d / "lakefile.toml").exists():
            return d
    return None


STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
COMPILER_AXIOMS = {"Lean.ofReduceBool", "Lean.ofReduceNat", "Lean.trustCompiler"}


def run_lean(path: Path, text: str, probe_names: dict[str, bool], timeout: int,
             extra: Sequence[str]) -> VerifierResult:
    """Run Lean on `text` (as if it were `path`) plus probes for each name.

    probe_names maps a fully qualified name to whether its value is frozen too
    (so `#print` it) or only its type (`#check`).
    """
    root = lean_root(path)
    lake = _which("lake", "VC_LAKE")
    lean = _which("lean", "VC_LEAN")
    if root and lake:
        cmd, cwd = [lake, "env", "lean", "--json", "--stdin", *extra], root
    elif lean:
        cmd, cwd = [lean, "--json", "--stdin", *extra], path.parent
    else:
        return VerifierResult(False, False, "lean", 0.0, "lean not found (install elan, or set VC_LEAN)")
    lines = text.rstrip("\n").split("\n")
    base = len(lines)
    probe_line: dict[int, tuple[str, str]] = {}
    for name, value_frozen in probe_names.items():
        q = name if re.fullmatch(r"[\w.'!?]+", name) else "«" + name + "»"
        lines.append(f"set_option pp.all true in set_option pp.proofs false in #check @{q}")
        probe_line[len(lines)] = ("sig", name)
        if value_frozen:
            lines.append(f"set_option pp.all true in set_option pp.proofs false in #print {q}")
            probe_line[len(lines)] = ("val", name)
        lines.append(f"#print axioms {q}")
        probe_line[len(lines)] = ("ax", name)
    t0 = time.monotonic()
    try:
        p = subprocess.run(cmd, input="\n".join(lines) + "\n", cwd=cwd, capture_output=True,
                           text=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        return VerifierResult(True, False, " ".join(cmd), float(timeout), f"timed out after {timeout}s")
    dt = time.monotonic() - t0
    res = VerifierResult(True, True, " ".join(cmd), dt, "")
    for raw in p.stdout.splitlines():
        try:
            msg = json.loads(raw)
        except json.JSONDecodeError:
            if raw.strip():
                res.errors.append(raw.strip())
            continue
        ln = msg.get("pos", {}).get("line", 0)
        sev = msg.get("severity", "")
        data = str(msg.get("data", "")).strip()
        if ln in probe_line:
            what, name = probe_line[ln]
            if sev == "error":
                res.warnings.append(f"probe for {name} failed: {data[:200]}")
            elif what == "ax":
                mm = re.search(r"depends on axioms:\s*\[(.*)\]", data, re.DOTALL)
                res.axioms[name] = [a.strip() for a in mm.group(1).split(",")] if mm else []
            else:
                res.signatures[f"{what}:{name}"] = data
            continue
        where = f"line {ln}" if ln <= base else "end of file"
        if sev == "error":
            res.errors.append(f"{where}: {data[:400]}")
        elif sev == "warning":
            if msg.get("kind") == "hasSorry" or "declaration uses 'sorry'" in data or "declaration uses `sorry`" in data:
                res.errors.append(f"{where}: {data}")
            else:
                res.warnings.append(f"{where}: {data[:200]}")
    if p.stderr.strip():
        res.errors.extend(l for l in p.stderr.strip().splitlines()[:20])
    if p.returncode != 0 and not res.errors:
        res.errors.append(f"lean exited with status {p.returncode}")
    res.ok = not res.errors
    res.summary = f"{len(res.errors)} errors, {len(res.warnings)} warnings"
    return res


def run_dafny(path: Path, timeout: int, extra: Sequence[str]) -> VerifierResult:
    dafny = _which("dafny", "VC_DAFNY")
    if not dafny:
        return VerifierResult(False, False, "dafny", 0.0, "dafny not found (brew install dafny, or set VC_DAFNY)")
    cmd = [dafny, "verify", *extra, str(path)]
    t0 = time.monotonic()
    try:
        p = subprocess.run(cmd, cwd=path.parent, capture_output=True, text=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        return VerifierResult(True, False, " ".join(cmd), float(timeout), f"timed out after {timeout}s")
    out = p.stdout + p.stderr
    res = VerifierResult(True, False, " ".join(cmd), time.monotonic() - t0, "")
    mm = re.search(r"finished with (\d+) verified, (\d+) errors?", out)
    for l in out.splitlines():
        if re.search(r"\b[Ee]rror\b", l) and "finished with" not in l:
            res.errors.append(l.strip())
        elif re.search(r"\b[Ww]arning\b", l):
            res.warnings.append(l.strip())
    if mm:
        res.summary = f"{mm.group(1)} verified, {mm.group(2)} errors"
        if mm.group(2) != "0" and not res.errors:
            res.errors.append(res.summary)
    else:
        res.summary = "no verifier summary line"
        if not res.errors:
            res.errors.append(out.strip()[-400:] or f"dafny exited with status {p.returncode}")
    if p.returncode != 0 and not res.errors:
        res.errors.append(f"dafny exited with status {p.returncode}")
    res.ok = p.returncode == 0 and bool(mm) and mm.group(2) == "0" and not res.errors
    return res


def run_verus(path: Path, text: str, timeout: int, extra: Sequence[str]) -> VerifierResult:
    verus = _which("verus", "VC_VERUS")
    if not verus:
        return VerifierResult(False, False, "verus", 0.0, "verus not found (install a verus-lang/verus release, or set VC_VERUS)")
    has_main = re.search(r"\bfn\s+main\s*\(", mask(text, Lang.VERUS)) is not None
    cmd = [verus, str(path), *([] if has_main else ["--crate-type=lib"]), *extra]
    t0 = time.monotonic()
    try:
        p = subprocess.run(cmd, cwd=path.parent, capture_output=True, text=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        return VerifierResult(True, False, " ".join(cmd), float(timeout), f"timed out after {timeout}s")
    out = p.stdout + p.stderr
    res = VerifierResult(True, False, " ".join(cmd), time.monotonic() - t0, "")
    mm = re.search(r"verification results::\s*(\d+) verified,\s*(\d+) errors?", out)
    for l in out.splitlines():
        if l.startswith("error"):
            res.errors.append(l.strip())
        elif l.startswith("warning"):
            res.warnings.append(l.strip())
    res.summary = f"{mm.group(1)} verified, {mm.group(2)} errors" if mm else "no verifier summary line"
    if p.returncode != 0 and not res.errors:
        res.errors.append(out.strip()[-400:] or f"verus exited with status {p.returncode}")
    res.ok = p.returncode == 0 and bool(mm) and mm.group(2) == "0" and not res.errors
    return res


# ---------------------------------------------------------------------------
# Snapshots.
# ---------------------------------------------------------------------------


def git_root(path: Path) -> Path | None:
    try:
        out = subprocess.run(["git", "rev-parse", "--show-toplevel"], cwd=path.parent,
                             capture_output=True, text=True, check=True).stdout.strip()
        return Path(out) if out else None
    except (OSError, subprocess.CalledProcessError):
        return None


def store_dir(path: Path, override: str | None) -> Path:
    if override:
        return Path(override)
    root = git_root(path)
    return (root or path.parent) / ".vericoding"


def snapshot_path(path: Path, store: Path) -> Path:
    key = hashlib.sha1(str(path.resolve()).encode()).hexdigest()[:12]
    return store / f"{key}-{path.name}.json"


def load_base(path: Path, base: str | None, store: Path) -> tuple[str, str]:
    """Return (original text, description of where it came from)."""
    if base and base.startswith("git:"):
        rev = base[4:] or "HEAD"
        root = git_root(path)
        if not root:
            raise UsageError(f"{path} is not in a git repository, so --base {base} can't work")
        rel = path.resolve().relative_to(root.resolve())
        try:
            text = subprocess.run(["git", "show", f"{rev}:{rel.as_posix()}"], cwd=root, capture_output=True,
                                  text=True, check=True).stdout
        except subprocess.CalledProcessError as e:
            raise UsageError(f"git show {rev}:{rel} failed: {e.stderr.strip()}") from None
        return text, f"git {rev}"
    if base:
        bp = Path(base)
        if bp.suffix == ".json":
            snap = json.loads(bp.read_text())
            return snap["content"], f"snapshot {bp}"
        return bp.read_text(), f"file {bp}"
    sp = snapshot_path(path, store)
    if sp.exists():
        snap = json.loads(sp.read_text())
        return snap["content"], f"snapshot {sp} ({snap.get('created', '?')})"
    if git_root(path):
        try:
            return load_base(path, "git:HEAD", store)[0], "git HEAD (no snapshot found; run `freeze` first next time)"
        except UsageError:
            pass
    raise UsageError(f"no snapshot for {path}. Run `vc_check.py freeze {path}` before editing, "
                     f"or pass --base git:REV or --base ORIGINAL_FILE")


# ---------------------------------------------------------------------------
# Commands.
# ---------------------------------------------------------------------------


def cmd_freeze(args: argparse.Namespace) -> int:
    path = Path(args.file)
    text = path.read_text()
    lang = detect_lang(path, args.lang)
    store = store_dir(path, args.store)
    sp = snapshot_path(path, store)
    if sp.exists() and not args.force:
        old = json.loads(sp.read_text())
        if old.get("content") == text:
            print(f"already frozen: {sp}")
            return 0
        print(f"refusing to re-freeze {path}: a snapshot from {old.get('created')} exists and the file has "
              f"changed since. Re-freezing after edits would launder spec changes. Delete {sp} or pass "
              f"--force only if a human changed the spec on purpose.", file=sys.stderr)
        return 2
    store.mkdir(parents=True, exist_ok=True)
    gi = store / ".gitignore"
    if not gi.exists():
        gi.write_text("*\n")
    mode, holes = compute_holes(text, lang)
    snap = {
        "vc_check": VERSION,
        "path": str(path.resolve()),
        "lang": lang.value,
        "mode": mode,
        "sha256": hashlib.sha256(text.encode()).hexdigest(),
        "created": _dt.datetime.now(_dt.timezone.utc).isoformat(timespec="seconds"),
        "content": text,
    }
    sp.write_text(json.dumps(snap, indent=1))
    print(f"frozen {path} ({lang.value}, {mode} mode, {len(holes)} holes) -> {sp}")
    return 0


def cmd_holes(args: argparse.Namespace) -> int:
    path = Path(args.file)
    text = path.read_text()
    lang = detect_lang(path, args.lang)
    mode, holes = compute_holes(text, lang)
    if args.json:
        print(json.dumps({"mode": mode, "holes": [asdict(h) | {
            "line": line_col(text, h.start)[0], "end_line": line_col(text, h.end)[0]} for h in holes]}, indent=1))
        return 0
    print(f"{path} ({lang.value}, {mode} mode): you may edit {len(holes)} places; everything else is frozen")
    for h in holes:
        la, ca = line_col(text, h.start)
        lb, cb = line_col(text, h.end)
        if h.kind == "insert":
            nxt = text[h.start : text.find("\n", h.start) if "\n" in text[h.start:] else len(text)].strip()
            print(f"  line {la:>4}         insert before: {nxt[:60] or '(end of file)'}")
        elif h.start == h.end:
            print(f"  line {la:>4}         {h.label} (empty now)")
        elif la == lb:
            print(f"  line {la:>4}:{ca:<3}-{cb:<4} {h.label}")
        else:
            print(f"  lines {la}-{lb}{'':<5} {h.label}")
    return 0


def cmd_scan(args: argparse.Namespace) -> int:
    worst = 0
    report: dict[str, list[dict[str, object]]] = {}
    for f in args.files:
        path = Path(f)
        lang = detect_lang(path, args.lang)
        found = scan_text(path.read_text(), lang)
        report[f] = [asdict(x) for x in found]
        if any(x.severity == "error" for x in found) or (args.strict and found):
            worst = 1
        if not args.json:
            for x in found:
                print(f"{f}:{x.line}:{x.col}: {x.severity}: {x.why}: {x.text}")
    if args.json:
        print(json.dumps(report, indent=1))
    elif worst == 0:
        print("no bypasses found" + (" (warnings above)" if any(report.values()) else ""))
    return worst


def cmd_check(args: argparse.Namespace) -> int:
    path = Path(args.file)
    lang = detect_lang(path, args.lang)
    cur = path.read_text()
    store = store_dir(path, args.store)
    orig, base_desc = load_base(path, args.base, store)
    out: dict[str, object] = {"file": str(path), "lang": lang.value, "base": base_desc}
    lines: list[str] = []
    failed: list[str] = []
    notes: list[str] = []

    fr = freeze_check(orig, cur, lang)
    out["freeze"] = asdict(fr)
    if fr.ok:
        lines.append(f"[ok]   spec frozen ({fr.mode} mode): every frozen segment intact; "
                     f"{fr.edited_holes} of {fr.holes} editable places changed")
    else:
        lines.append(f"[FAIL] spec changed ({fr.mode} mode)")
        lines += [f"         {p}" for p in fr.problems]
        failed.append("spec")

    spans = fr.free_spans if fr.ok else None
    found = scan_text(cur, lang, spans)
    errs = [x for x in found if x.severity == "error"]
    warns = [x for x in found if x.severity == "warning"]
    out["bypasses"] = [asdict(x) for x in found]
    scope = "in the text you wrote" if fr.ok else "in the whole file"
    if errs or (args.strict and warns):
        lines.append(f"[FAIL] {len(errs)} bypasses {scope}" + (f", {len(warns)} warnings (strict)" if args.strict else ""))
        failed.append("bypass")
    else:
        lines.append(f"[ok]   no bypasses {scope}" + (f"; {len(warns)} warnings to justify" if warns else ""))
    for x in errs + warns:
        lines.append(f"         line {x.line}: {x.severity}: {x.why}: {x.text}")

    if args.no_verify:
        lines.append("[skip] verifier not run (--no-verify)")
        failed.append("not-run")
    else:
        vr, mismatches = _verify(path, lang, cur, orig, fr, args, notes)
        out["verifier"] = asdict(vr)
        out["meaning_changed"] = mismatches
        if not vr.ran:
            lines.append(f"[FAIL] verifier did not run: {vr.summary}")
            failed.append("verifier-missing")
        elif vr.ok:
            lines.append(f"[ok]   {lang.value}: {vr.summary} ({vr.seconds:.1f}s)")
        else:
            lines.append(f"[FAIL] {lang.value}: {vr.summary or 'rejected'} ({vr.seconds:.1f}s)")
            lines += [f"         {e}" for e in vr.errors[:30]]
            failed.append("verifier")
        if lang is Lang.LEAN and vr.ran:
            ax_fail, ax_lines = _judge_axioms(vr.axioms, orig, args.allow_native)
            lines += ax_lines
            if ax_fail:
                failed.append("axioms")
            if mismatches:
                lines.append(f"[FAIL] {len(mismatches)} frozen declarations mean something different now")
                lines += [f"         {m}" for m in mismatches]
                failed.append("spec-meaning")
            elif vr.signatures:
                n = len({k.split(':', 1)[1] for k in vr.signatures})
                lines.append(f"[ok]   {n} frozen declarations elaborate exactly as in the original")
        if vr.warnings and args.verbose:
            lines += [f"         verifier warning: {w}" for w in vr.warnings[:20]]
    lines += [f"[note] {n}" for n in notes]

    verdict = "VERIFIED" if not failed else "NOT VERIFIED"
    out["verdict"] = verdict
    out["failed"] = failed
    if args.json:
        print(json.dumps(out, indent=1, default=str))
    else:
        print(f"vc_check {path} ({lang.value})  base: {base_desc}")
        print("\n".join(lines))
        print(verdict + ("" if not failed else f"  ({', '.join(failed)})"))
    return 0 if not failed else (2 if failed == ["verifier-missing"] else 1)


def _verify(path: Path, lang: Lang, cur: str, orig: str, fr: FreezeResult,
            args: argparse.Namespace, notes: list[str]) -> tuple[VerifierResult, list[str]]:
    """Run the verifier; for Lean also compare how frozen declarations elaborate."""
    extra = args.verifier_arg or []
    if lang is Lang.DAFNY:
        return run_dafny(path, args.timeout, extra), []
    if lang is Lang.VERUS:
        return run_verus(path, cur, args.timeout, extra), []
    mo = mask(orig, Lang.LEAN)
    _, holes = compute_holes(orig, Lang.LEAN)
    probes: dict[str, bool] = {}
    for d in lean_decls(mo):
        if d.kind == "instance":
            continue
        if any(h.start <= d.start < h.end and h.kind != "sorry" for h in holes):
            continue  # declared inside an editable region, so not part of the spec
        has_sorry_hole = any(d.start <= h.start < d.end and h.kind == "sorry" for h in holes)
        probes[d.name] = d.kind in ("def", "abbrev", "opaque") and not has_sorry_hole
    vr = run_lean(path, cur, probes, args.timeout, extra)
    mismatches: list[str] = []
    if vr.ran and probes and fr.ok:
        ref = run_lean(path, orig, probes, args.timeout, extra)
        if not ref.ran or not ref.signatures:
            notes.append(f"could not elaborate the original to compare statements: {ref.summary}")
        pending: list[tuple[str, str, list[tuple[str, str]]]] = []
        for key, want in ref.signatures.items():
            kind, name = key.split(":", 1)
            what = "type" if kind == "sig" else "definition"
            got = vr.signatures.get(key)
            if got is None:
                mismatches.append(f"{name}: no longer elaborates (renamed, removed, or broken)")
            elif " ".join(got.split()) != " ".join(want.split()):
                pairs = _matcher_pairs(want, got)
                if pairs is None:
                    mismatches.append(f"{name}: its {what} elaborates differently than in the original, so "
                                      f"something you added changed its meaning")
                else:
                    pending.append((name, what, pairs))
        if pending:
            mismatches += _reconcile_matchers(path, orig, cur, pending, args.timeout, extra)
    return vr, mismatches


_MATCHER = re.compile(r"[\w.'«»]+\.match_\d+")


_BINDERS = re.compile(r"(?<=[({⦃\[])\s*([^\s:(){}\[\]⦃⦄,@]+(?:\s+[^\s:(){}\[\]⦃⦄,@]+)*)\s+:(?!=)|\blet\s+([^\s:]+)\s*:")
_TOKEN = re.compile(r"[^\s(){}\[\]⦃⦄,:]+")


def _alpha(term: str) -> str:
    """Rename bound variables in a `pp.all` term to v0, v1, ... in order of first binding.

    Whitespace is collapsed too, since the pretty-printer wraps lines by width.
    """
    term = " ".join(term.split())
    names: dict[str, str] = {}
    for m in _BINDERS.finditer(term):
        for n in (m.group(1) or m.group(2) or "").split():
            names.setdefault(n, f"v{len(names)}")
    return _TOKEN.sub(lambda t: names.get(t.group(0), t.group(0)), term)


def _matcher_pairs(want: str, got: str) -> list[tuple[str, str]] | None:
    """If two printed terms differ only in auxiliary matcher names, pair those names up.

    Lean reuses an identical `match` compiled for an earlier declaration, so the
    same spec can print as `foo.match_1` in one file and `bar.match_1` in another.
    """
    if _alpha(_MATCHER.sub("MATCHER", want)) != _alpha(_MATCHER.sub("MATCHER", got)):
        return None
    return [(a, b) for a, b in zip(_MATCHER.findall(want), _MATCHER.findall(got)) if a != b]


def _reconcile_matchers(path: Path, orig: str, cur: str, pending: list[tuple[str, str, list[tuple[str, str]]]],
                        timeout: int, extra: Sequence[str]) -> list[str]:
    """Accept renamed matchers only if their types agree up to bound-variable names.

    A matcher's type lists its alternatives with their patterns in order, and
    the compiler derives its body from that, so equal types mean equal matchers.
    """
    want_names = {a for _, _, ps in pending for a, _ in ps}
    got_names = {b for _, _, ps in pending for _, b in ps}
    ref = run_lean(path, orig, {n: False for n in want_names}, timeout, extra)
    now = run_lean(path, cur, {n: False for n in got_names}, timeout, extra)
    out: list[str] = []
    for name, what, pairs in pending:
        same = all(
            _alpha((ref.signatures.get(f"sig:{a}") or "").replace(a, "MATCHER"))
            == _alpha((now.signatures.get(f"sig:{b}") or "?").replace(b, "MATCHER"))
            for a, b in pairs
        )
        if not same:
            out.append(f"{name}: its {what} elaborates differently than in the original, so something you "
                       f"added changed its meaning")
    return out


def _judge_axioms(axioms: dict[str, list[str]], orig: str, allow_native: bool) -> tuple[bool, list[str]]:
    if not axioms:
        return False, []
    _, holes = compute_holes(orig, Lang.LEAN)
    orig_has_sorry = any(not any(h.start <= s.start() < h.end for h in holes)
                         for s in re.finditer(r"\bsorry\b", mask(orig, Lang.LEAN)))
    bad: list[str] = []
    soft: list[str] = []
    for name, axs in axioms.items():
        extra = [a for a in axs if a and a not in STANDARD_AXIOMS]
        for a in extra:
            if a == "sorryAx":
                bad.append(f"{name} depends on sorryAx")
            elif a in COMPILER_AXIOMS:
                (soft if allow_native else bad).append(f"{name} trusts the compiler ({a}, from native_decide)")
            else:
                bad.append(f"{name} depends on non-standard axiom {a}")
    lines: list[str] = []
    if bad:
        lines.append(f"[FAIL] axioms: {len(bad)} problems")
        lines += [f"         {b}" for b in bad]
        if orig_has_sorry and all("sorryAx" in b for b in bad):
            lines.append("         (the frozen part of the original has sorry too; if the proof relies on a lemma "
                         "you were told to leave unproved, say so in the report)")
    else:
        lines.append(f"[ok]   axioms: {len(axioms)} declarations use only propext, Classical.choice, Quot.sound"
                     + (f"; {len(soft)} trust native_decide (allowed by --allow-native)" if soft else ""))
    return bool(bad), lines


def main(argv: Sequence[str] | None = None) -> int:
    ap = argparse.ArgumentParser(prog="vc_check.py", description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--version", action="version", version=f"vc_check {VERSION}")
    sub = ap.add_subparsers(dest="cmd", required=True)

    def common(p: argparse.ArgumentParser) -> None:
        p.add_argument("--lang", choices=[l.value for l in Lang])
        p.add_argument("--json", action="store_true", help="machine-readable output")

    p = sub.add_parser("freeze", help="snapshot a file's spec before editing it")
    p.add_argument("file")
    p.add_argument("--store", help="snapshot directory (default: .vericoding at the git root or next to the file)")
    p.add_argument("--force", action="store_true", help="overwrite an existing snapshot (humans only)")
    common(p)
    p.set_defaults(fn=cmd_freeze)

    p = sub.add_parser("holes", help="list the places you may edit")
    p.add_argument("file")
    common(p)
    p.set_defaults(fn=cmd_holes)

    p = sub.add_parser("scan", help="report verification bypasses anywhere in the files")
    p.add_argument("files", nargs="+")
    p.add_argument("--strict", action="store_true", help="fail on warnings too")
    common(p)
    p.set_defaults(fn=cmd_scan)

    p = sub.add_parser("check", help="the gate: spec frozen, no bypasses, verifier accepts")
    p.add_argument("file")
    p.add_argument("--base", help="original to compare against: git:REV, a file, or a snapshot .json "
                                  "(default: the snapshot from `freeze`, else git HEAD)")
    p.add_argument("--store", help="snapshot directory")
    p.add_argument("--timeout", type=int, default=900, help="verifier timeout in seconds (default 900)")
    p.add_argument("--verifier-arg", action="append", help="extra argument for the verifier (repeatable)")
    p.add_argument("--no-verify", action="store_true", help="skip the verifier (the verdict is then NOT VERIFIED)")
    p.add_argument("--strict", action="store_true", help="treat bypass warnings as failures")
    p.add_argument("--allow-native", action="store_true", help="accept Lean.ofReduceBool (native_decide)")
    p.add_argument("--verbose", action="store_true", help="show verifier warnings")
    common(p)
    p.set_defaults(fn=cmd_check)

    args = ap.parse_args(argv)
    try:
        return int(args.fn(args))
    except UsageError as e:
        print(f"vc_check: {e}", file=sys.stderr)
        return 2
    except FileNotFoundError as e:
        print(f"vc_check: {e}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(main())
