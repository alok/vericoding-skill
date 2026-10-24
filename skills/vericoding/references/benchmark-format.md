# The `vc-*` task format

Vericoding benchmarks (the 2025 vericoding benchmark of about 12,500 tasks built from DafnyBench,
Verina, FVAPPS, CLEVER, APPS, HumanEval, NumPy and others) split each task file into tagged
sections. The tags are comments, so the file still compiles:

```lean
-- <vc-preamble>
...imports and definitions the spec uses (frozen)...
-- </vc-preamble>

-- <vc-helpers>
...empty: put helper definitions and lemmas here...
-- </vc-helpers>
```

Dafny and Verus use `// <vc-…>`. The gate reads these tags; `vc_check.py holes FILE` lists the
editable places.

## What you may edit

| Language | Editable | Frozen |
|---|---|---|
| Lean | all of `vc-helpers`; each `sorry` inside `vc-definitions` and `vc-theorems` | `vc-preamble`, every signature, the theorem statements, the postcondition definitions, and any `sorry` in the preamble |
| Dafny | all of `vc-helpers`; all of `vc-code` (the method body, braces included) | `vc-preamble`, `vc-spec` (signature and contracts), `vc-postamble` |
| Verus | all of `vc-helpers`; all of `vc-code` (the function body) | `vc-preamble`, `vc-spec`, `vc-postamble` |

## Lean specifics

- `vc-helpers` comes **before** `vc-definitions`, so helpers there can't mention the function you're
  implementing. Put lemmas about your implementation **after its body, inside the same replacement**:
  replace the `sorry` in the def with the body, a blank line, then the lemmas. `FindFirst.lean` in
  `examples/lean/solved/` does exactly this.
- A `sorry` can sit inside a theorem *statement*, as a proof that an index is in bounds
  (`matrix.get ⟨i * n + i, by sorry⟩`). Replacing it with a real proof is allowed and expected. Proofs
  inside statements don't change their meaning, and the gate ignores them when comparing statements.
- The postcondition is usually `@[reducible, simp]`, so `simp` unfolds it. Start the main proof with
  `simp only [f_postcond]` or `unfold f_postcond` to see what you actually need.
- You can't add imports; they're in the frozen preamble. Work with the tactics those imports provide.
  A task that imports only core Lean has `omega`, `simp`, `grind`, `decide` and induction, which is
  enough for most tasks.
- `h_precond` is yours to use in the implementation, for example to justify `xs.head` or an index.

## Dafny and Verus specifics

- `vc-code` is the whole body, so loop invariants, `decreases` clauses, `assert`s, ghost variables
  and calls to lemmas all go inside it.
- Lemmas and helper functions go in `vc-helpers`, which comes before the spec, so they can't refer to
  the method being implemented. They can refer to anything in the preamble.
- The template body is `{ assume {:axiom} false; }` (Dafny) or `{ assume(false); ... }` (Verus).
  Replace it entirely; a leftover `assume` is a bypass.

## Benchmark rules the gate enforces

Everything in SKILL.md's "What done means", plus: the only text that differs from the original is
inside the editable places listed above. That's the same rule the benchmark's own harness uses,
checked one more way. The gate also compares the elaborated Lean statements, which catches a helper
that changes how frozen text elaborates.

## Other forms

The benchmark also ships each task as YAML (`vc-preamble: |-` keys) and as JSONL with the same
section names. To work on one of those, assemble a file from the sections in order, each wrapped in
its tags (`vc-preamble`, `vc-helpers`, `vc-definitions`, `vc-theorems` for Lean; `vc-preamble`,
`vc-helpers`, `vc-spec`, `vc-code`, `vc-postamble` for Dafny and Verus), then freeze that file before
editing it.
