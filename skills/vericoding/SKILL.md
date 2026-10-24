---
name: vericoding
description: >-
  Vericoding: write code together with a machine-checked proof that it meets a frozen formal spec,
  Lean 4 first (Dafny and Verus experimental), and refuse to call it done until a gate confirms the
  verifier accepted it, the spec is untouched, and no sorry/admit/axiom/assume or other bypass was
  slipped in. Use whenever the user wants verified, proven-correct or correct-by-construction code;
  asks to implement a def and prove its spec theorem; to fill `sorry` placeholders in a program and
  its correctness theorems; to solve vericoding benchmark tasks (`<vc-preamble>`, `<vc-helpers>`,
  `<vc-definitions>`, `<vc-theorems>`, `<vc-spec>`, `<vc-code>` tags, Verina, FVAPPS, CLEVER,
  DafnyBench); to prove a Hoare triple about a monadic Lean program with mvcgen; to write a formal
  spec from intent before implementing it; or to audit whether an agent's "verified" result cheated.
  Not for pure mathematics with no program in it.
license: MIT
compatibility: >-
  Needs Python 3.10+ for scripts/vc_check.py and a Lean 4 toolchain (elan; lake for projects).
  Dafny and Verus support in the checker is experimental and untested against real verifiers.
metadata:
  author: Alok Singh
  version: 0.1.0
  homepage: https://github.com/alok/vericoding-skill
---

# Vericoding

Vibe coding asks a model for code and hopes the tests catch the bugs. Vericoding asks for code
*and a proof* that it meets a formal specification, then hands both to a verifier that doesn't
care how confident anyone sounds. If the proof checks, the code does what the spec says, and the
only remaining questions are whether the spec says what was meant and whether the verifier is
trustworthy.

That only works if nobody quietly moves the goalposts. Agents under pressure to make the build
green will weaken an `ensures`, rewrite a theorem statement, leave a `sorry` that Lean reports as a
mere warning, or slip in an `axiom`. Each of those produces a green check that proves nothing. The
spec is usually the only part a human actually reviewed, so it is the part you must never touch.

This skill gives you a workflow and a gate (`scripts/vc_check.py`) that catches those failures
mechanically, so "verified" means verified.

## What "done" means

A result is **VERIFIED** only when all of these hold, and `vc_check.py check` is what decides it:

1. The verifier accepts the file. For Lean that means no errors *and* no "declaration uses
   `sorry`" warning, since Lean exits 0 with a sorry in the file.
2. Nothing you wrote is a verification bypass (`sorry`, `admit`, `axiom`, `implemented_by`,
   `@[extern]`, `unsafe`, `#exit`, `run_cmd`, `debug.skipKernelTC`; Dafny `assume`, `{:axiom}`,
   bodyless lemmas; Verus `assume`, `admit`, `external_body`, and the rest).
3. Every frozen part of the original is still there, unchanged and in order.
4. (Lean) Every frozen declaration elaborates exactly as before, so no new instance, notation or
   option changed what the spec means, and `#print axioms` shows only `propext`,
   `Classical.choice` and `Quot.sound`.

Anything short of that is **partial**. Say so in plain words and name what's left. An honest
"not verified, two goals remain, here they are" is worth far more than a fake green, because the
user can act on it.

## Workflow

### 1. Find the spec and the holes

Read the whole file. Identify what is spec (signatures, theorem statements, `requires`/`ensures`,
postcondition definitions, everything in `vc-preamble`/`vc-spec`) and what you're meant to fill.
Then ask the gate, since it's the authority on what you may touch:

```bash
python3 scripts/vc_check.py holes path/to/File.lean
```

`scripts/` is relative to this skill's directory; use the absolute path when running from a
project. `uv run scripts/vc_check.py ...` also works. The script uses only the standard library.

What counts as a hole depends on the file:

- **Benchmark files** (with `<vc-…>` tags): `vc-helpers` and `vc-code` contents, plus (Lean) each
  `sorry` inside `vc-definitions` and `vc-theorems`. Everything else is frozen. See
  `references/benchmark-format.md`.
- **Lean, general**: each `sorry`, plus new declarations inserted between top-level commands
  (at column 0) and new imports right after the existing ones.
- **Dafny / Verus, general**: method, lemma, `fn` and `proof fn` bodies, plus new declarations.
  Contracts and `function`/`predicate`/`spec fn` bodies are frozen, because they *are* the spec.

### 2. Freeze before the first edit

```bash
python3 scripts/vc_check.py freeze path/to/File.lean
```

This snapshots the original under `.vericoding/` (git-ignored). The gate compares against it later.
It refuses to re-freeze a file that changed since its snapshot. That's deliberate: re-freezing
after an edit would launder a spec change. If you forgot to freeze and the file is in git, `check`
falls back to `git HEAD`, or pass `--base git:REV`.

### 3. Understand the spec before writing code

Restate the spec in one to three plain sentences. Then sanity-check it, because a wrong spec makes
the whole exercise pointless and you're the first one positioned to notice:

- Is the precondition satisfiable? A precondition that's always false makes any proof vacuous.
- Could a trivial output satisfy the postcondition (empty list, `0`, `none`, the input itself)?
  Then the spec is weak, and a "verified" trivial implementation would be technically correct and
  useless.
- Does it match the docstring, the `vc-description`, the function name and the user's words?

In Lean, check the spec on concrete inputs before you implement anything. It takes a minute and
catches most spec bugs:

```lean
example : post [1, -2, 3] 2 := by simp [post]        -- a right answer is accepted
example : ¬ post [1, -2, 3] 3 := by simp [post]      -- a wrong answer is rejected
example : ¬ post [1, -2, 3] 0 := by simp [post]      -- a trivial answer is rejected too
```

If the trivial answer turns out to be accepted, the spec is weak.

Do this in a scratch file, not the task file. If the spec looks wrong, don't fix it silently.
Finish under the spec as given and report the concern, or ask first if the user is around.
`references/spec-review.md` covers the common failure modes and how to write a spec from intent.

### 4. Implement first, prove second

Write an implementation that compiles with proofs still `sorry`, and test it on examples with
`#guard f [1, 2, 3] = 6` in a scratch file. A wrong implementation can burn an hour of failed
proof attempts before you notice, and `#guard` takes a second.

Shape the implementation for the proof, not for speed, unless the user asked for speed:

- Mirror the spec's structure. If the spec talks about `List.filter`, recursing over the list
  the same way makes the proof a short induction.
- Prefer structural recursion over well-founded recursion, and functional code over `Id.run do`
  loops, unless the spec is itself a Hoare triple about a monadic program.
- Never make the implementation the spec's own witness (`Classical.choose`, `noncomputable`). That
  passes the type checker and implements nothing.

### 5. Prove in small, checked steps

Split the main theorem into lemmas, check after every step, and read the actual goal instead of
guessing. If the `lean-lsp-mcp` tools are available, use `lean_goal` to see the goal at a line,
`lean_diagnostic_messages` for errors, and `lean_multi_attempt` to try several tactics at once.
Without them, compile the single file:

```bash
lake env lean path/to/File.lean     # inside a Lake project (needed for Mathlib)
lean path/to/File.lean              # standalone file, core library only
```

`sorry` is a fine scaffold while you work. The count has to reach zero, but use it to check that
the rest of the proof structure works before filling each piece.

`references/lean.md` holds the Lean playbook: implementation patterns, the tactic toolkit
(`simp`, `omega`, `grind`, `fun_induction`, `decide`), `mvcgen` for loops, arrays and indices, and
how to read common errors. Read it before the first proof attempt on a nontrivial task.

### 6. Run the gate

```bash
python3 scripts/vc_check.py check path/to/File.lean
```

Iterate until it prints `VERIFIED`. Don't substitute your own reading of the verifier output: the
gate checks things that are easy to miss by eye (the sorry warning, inherited axioms, a frozen
statement that now elaborates differently). Useful flags: `--timeout SECONDS` (default 900),
`--allow-native` to accept `native_decide`, `--strict` to fail on warnings, `--json` for machine
output. Exit status is 0 for verified, 1 for not verified, 2 when the verifier couldn't run.

Warnings are not failures, but each one needs a sentence in your report saying why it's fine
(for example, "the `open List in` only shortens names in my helper lemma").

### 7. Report

End with this, filled in:

```
Verdict: VERIFIED | NOT VERIFIED (<reasons from the gate>)
What is proven: <the spec in one or two plain sentences>
Implementation: <approach in a sentence; any helper lemmas worth knowing about>
Trusted base: <toolchain version; Mathlib if used; native_decide or other non-standard axioms, if any>
Warnings: <each gate warning and why it's acceptable, or "none">
Spec concerns: <weak/vacuous/mismatched spec observations, or "none">
Remaining work: <goals left open, if not verified>
```

## Rules, and why they exist

- **Leave frozen text alone, including "harmless" fixes.** A changed statement isn't the
  statement the user asked for, however reasonable the change. Whitespace changes are fine; the gate
  ignores them.
- **Don't add bypasses, even temporarily in the final file.** Lean's `sorry` is a warning, not an
  error, so a single leftover one turns the whole result into "unproved" while the build stays
  green.
- **Don't change the meaning of frozen text from the outside.** A new instance, notation, `open`,
  `set_option` or macro placed before a spec can change what the spec elaborates to without
  touching its text. The gate compares elaborated statements to catch this. Keep helpers plain.
- **Don't claim results you didn't run.** If no verifier is installed, say "not verified, no
  verifier available" and stop there.
- **Stop when stuck.** After several genuinely different attempts at one goal, report partial
  progress with the exact remaining goal instead of escalating to cheats. Give the next person
  the goal state, what you tried, and your best guess at the missing lemma.

## Dafny and Verus (experimental)

The workflow is the same. The gate's bypass scan and spec freeze are unit-tested for both
languages, but its verifier runners (`dafny verify`, `verus`) have not yet been exercised against
real installs, so double-check its output against the raw verifier output. See
`references/dafny.md` and `references/verus.md` for loop invariants, termination, ghost code and
the per-language bypass lists.

## Files in this skill

| Path | Read it when |
|---|---|
| `references/lean.md` | Before the first proof attempt on any nontrivial Lean task |
| `references/spec-review.md` | The spec looks weak, vacuous or wrong, or you must write one from intent |
| `references/benchmark-format.md` | The file has `<vc-…>` tags, or the task came from a benchmark |
| `references/dafny.md`, `references/verus.md` | The task is in Dafny or Verus |
| `examples/lean/` | You want a worked task and solution: `SumOdds` (recursion), `SumList` (loop with `mvcgen`), `FindFirst` (benchmark format) |
| `scripts/vc_check.py` | Always: `holes`, `freeze`, `check`, `scan` |
