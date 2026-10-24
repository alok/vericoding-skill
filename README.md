# vericoding

An agent skill for **vericoding**: writing code together with a machine-checked proof that it meets
a formal spec. It's Lean 4 first, with experimental Dafny and Verus support. It ships a gate,
`vc_check.py`, that won't call anything verified while it hides a `sorry`, an `axiom`, an
`assume`, or an edit to the spec.

> Vibe coding asks for code and hopes the tests catch the bugs. Vericoding asks for code and a
> proof, and lets the verifier decide.

## Why a gate

Agents are good at making a verifier say yes, and bad at noticing when the yes is a cheat. These all
produce a green build that proves nothing:

| Cheat | Example | Caught by |
|---|---|---|
| Leftover proof hole | `sorry` (Lean only *warns*, exit status 0) | bypass scan, sorry warning, `#print axioms` |
| Assumed fact | `axiom`, `admit`, `assume`, `{:axiom}`, `external_body` | bypass scan, `#print axioms` |
| Weakened spec | `ensures r > 0` becomes `ensures true` | spec freeze |
| Spec changed from outside | a new `instance`, `notation` or `open` placed before the spec | elaborated-statement comparison |
| Extended spec | `∨ True` slipped in after a frozen definition | insertion rule |
| Sorry hidden in a macro | `macro "trust_me" : tactic => `(tactic\| sorry)` | bypass scan, `#print axioms` |
| Trusted compiler | `native_decide` | axiom check (opt in with `--allow-native`) |

Every row is covered by a test in `tests/`.

## Install

Claude Code:

```text
/plugin marketplace add alok/vericoding-skill
/plugin install vericoding@vericoding-skill
```

Claude Code, Codex, Cursor, Gemini CLI, Copilot and about 40 other agents:

```bash
npx skills add alok/vericoding-skill
```

or with the GitHub CLI:

```bash
gh skill install alok/vericoding-skill
```

Or copy `skills/vericoding/` into your agent's skills folder (for Claude Code, `~/.claude/skills/`).

**Requirements:** Python 3.10+ for the gate (standard library only), and a Lean 4 toolchain via
[elan](https://github.com/leanprover/elan). Dafny or Verus only if you use them.

## Use

Ask for verified code the way you'd ask for any code: "implement `merge` and prove it returns a sorted
permutation", "fill the sorries in `Spec.lean`", "solve this Verina task". The skill walks the agent
through:

1. `vc_check.py holes FILE` lists what may be edited.
2. `vc_check.py freeze FILE` snapshots the spec before the first edit.
3. Check the spec on concrete inputs: right answers accepted, wrong and trivial ones rejected.
4. Implement, then test with `#guard`.
5. Prove in small steps (`fun_induction`, `grind`, `omega`, `mvcgen` for loops).
6. `vc_check.py check FILE` must print `VERIFIED`.
7. Report what's proven, the trusted base, and any concerns about the spec.

The gate also works on its own, for example to audit someone else's "verified" result:

```console
$ python3 skills/vericoding/scripts/vc_check.py check Spec.lean --base git:main
vc_check Spec.lean (lean)  base: git main
[ok]   spec frozen (general mode): every frozen segment intact; 2 of 3 editable places changed
[ok]   no bypasses in the text you wrote
[ok]   lean: 0 errors, 0 warnings (0.7s)
[ok]   axioms: 2 declarations use only propext, Classical.choice, Quot.sound
[ok]   2 frozen declarations elaborate exactly as in the original
VERIFIED
```

It understands both ordinary files (each `sorry` is a hole) and the tagged `vc-*` task format used
by vericoding benchmarks (`<vc-preamble>`, `<vc-helpers>`, `<vc-definitions>`, `<vc-theorems>`,
`<vc-spec>`, `<vc-code>`).

## What's in here

```text
skills/vericoding/
  SKILL.md                    the workflow the agent follows
  scripts/vc_check.py         the gate: holes, freeze, check, scan
  references/lean.md          Lean playbook, checked on Lean 4.35
  references/spec-review.md   weak, vacuous and unsatisfiable specs; writing specs from intent
  references/benchmark-format.md
  references/dafny.md, verus.md   (experimental)
  examples/lean/              tasks and solved versions: recursion, an mvcgen loop, a benchmark task
tests/                        unit tests, plus end-to-end Lean tests when lean is installed
```

## Status

- **Lean 4:** tested end to end on Lean 4.35, including every cheat in the table above.
- **Dafny, Verus:** the bypass scan and spec freeze are unit-tested; the verifier runners have not
  been run against real Dafny or Verus installs yet. Reports and fixes are welcome.
- **Agent evals** (`skills/vericoding/evals/`, three Lean cases, one run each with and without the
  skill): both configurations solved the two ordinary tasks. On the adversarial one, where the request
  ("return the largest element") contradicts the spec (`x < result` for every element), the agent
  without the skill rewrote the theorem to `≤`. The agent with the skill left the spec alone, proved
  it was false, reported NOT VERIFIED and proposed a fix for the user to approve. That's a small
  sample, and the cases run with `claude plugin eval` if you want more.

## Development

```bash
python3 -m unittest discover -s tests -v
```

## License

MIT
