# vericoding skill: design spec

Status: draft 1, 2026-10-24. Owner: Alok Singh (`alok` on GitHub).

## What it is

An [Agent Skill](https://agentskills.io) that makes a coding agent good at
**vericoding**: writing an implementation *and* a machine-checked proof that it
meets a formal specification, then handing both to a verifier. It targets
Lean 4, Dafny and Verus.

Vibe coding hopes the tests catch the bugs. Vericoding asks the verifier, which
does not care how confident the model sounds. The skill exists because agents
are good at producing *something the verifier accepts* and bad at noticing
when that something is a cheat.

## Who it is for

- People using Claude Code, Codex, Cursor, Gemini CLI and other skill-aware
  agents to write verified code in their own projects.
- Researchers running vericoding benchmarks with the `vc-*` tagged task format
  (Dafny / Lean / Verus files split into preamble, helpers, spec, code).

## The contract the skill enforces

A run counts as **verified** only when all of these hold:

1. The verifier accepts the file (exit status and output both checked, because
   Lean reports `sorry` as a warning and exits 0).
2. No verification bypass appears anywhere the agent wrote: `sorry`, `admit`,
   `axiom`, `assume`, `{:axiom}`, `{:verify false}`, bodyless Dafny lemmas,
   `#[verifier::external_body]`, `assume_specification`, `unimplemented!()`,
   `@[implemented_by]`, `@[extern]`, `unsafe`, and the rest of the list in
   `scripts/vc_check.py`.
3. The spec is byte-for-byte what it was before the agent started (modulo
   whitespace), checked against a snapshot or a git revision.
4. For Lean, `#print axioms` on every frozen theorem shows only the standard
   axioms (`propext`, `Classical.choice`, `Quot.sound`). `Lean.ofReduceBool`
   (from `native_decide`) is reported, not silently accepted.

Anything weaker gets reported as what it is: partial, with the holes named.

## Pieces

| Piece | Job |
|---|---|
| `SKILL.md` | The loop: read and restate the spec, sanity-check it, freeze it, implement, prove in small verified steps, run the gate, report. Under 500 lines. |
| `references/lean.md` | Lean 4 tactics and patterns for implementation + proof: structural recursion, `fun_induction`, `grind`, `omega`, `simp` discipline, `Std.Do` Hoare triples with `mvcgen`, `decreasing_by`. |
| `references/dafny.md` | Loop invariants, `decreases`, ghost state, lemma calls, triggers, `calc`, sequences and multisets, timeouts. |
| `references/verus.md` | `requires`/`ensures` syntax, `@` views, `proof { }` blocks, invariants, `decreases`, overflow, `vstd` lemmas, `by (nonlinear_arith)`. |
| `references/spec-review.md` | When the spec is the problem: vacuous preconditions, trivially satisfiable postconditions, "verified but wrong". Writing a spec from intent, with positive and negative example checks. |
| `references/benchmark-format.md` | The `vc-*` tag format: what is frozen, what is a hole, per language. |
| `scripts/vc_check.py` | The gate. Stdlib-only Python 3.10+, typed, PEP 723 header so `uv run` works. Subcommands `scan`, `freeze`, `check`. |
| `examples/` | One small solved task per language plus deliberate cheats, used as test fixtures. |
| `tests/` | Unit tests for the checker; CI runs them plus the Lean examples. |

## The freeze model

The original file is cut into **frozen segments** separated by **holes**. The
check passes when the current file contains every frozen segment, in order,
with only hole positions changed. Whitespace runs compare equal.

Holes, by mode:

- **Benchmark mode** (file has `<vc-…>` tags): Dafny and Verus holes are the
  contents of `vc-helpers` and `vc-code`. Lean holes are the contents of
  `vc-helpers` plus each `sorry` inside `vc-definitions` and `vc-theorems`.
  Everything else, including `sorry`s inside `vc-preamble`, is frozen.
- **General mode** (no tags):
  - Lean: each `sorry` is a hole, and new declarations may be inserted between
    top-level declarations.
  - Dafny: bodies of `method`s and `lemma`s are holes; signatures and
    contracts are frozen; `function` and `predicate` bodies are frozen because
    they are part of the spec. New declarations may be inserted between
    top-level declarations.
  - Verus: bodies of `fn` and `proof fn` are holes; `spec fn` bodies,
    signatures and contracts are frozen. New items may be inserted between
    top-level items.

Inserted text is still scanned, so an inserted `axiom` or `assume` fails the
gate. Lean metaprogramming in inserted text (`macro`, `notation`, `elab`,
`syntax`, `set_option ... in`, instance overrides) is reported as a warning
that needs a human look, because it can change what frozen text means.

The original comes from `vc_check.py freeze` (a JSON snapshot under
`.vericoding/`) or from git (`--base git:HEAD`), so a forgotten freeze is
recoverable in a repo.

## Non-goals

- Not a prover or a model. It is instructions plus a gate.
- No network calls, telemetry, or model API use from the script.
- No benchmark harness; the BAIF vericoding repo has one. The skill reads the
  task format and nothing else from it.

## Distribution

- GitHub `alok/vericoding-skill`, MIT.
- Repo root is both a Claude Code plugin marketplace and the plugin itself
  (`.claude-plugin/marketplace.json` + `.claude-plugin/plugin.json`), with the
  skill at `skills/vericoding/SKILL.md` so `npx skills add alok/vericoding-skill`
  and other auto-indexers find it.
- Listings: whichever marketplaces and directories accept it (see
  `docs/publishing.md`).

## Success criteria

- `vc_check.py check` passes on every solved example and fails on every cheat
  fixture, for every language whose verifier is installed.
- With-skill agent runs on held-out Lean tasks beat no-skill runs on "verified
  with no cheat" rate, or at least never cheat where the baseline does.
- A stranger can install it with one command and get value without reading the
  design doc.
