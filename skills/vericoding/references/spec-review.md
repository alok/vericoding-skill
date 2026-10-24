# When the spec is the problem

A proof only shows the code meets the spec. If the spec is wrong, a verified program is wrong with
a certificate. Specs written by people, translated by tools or drafted by models fail in a few
recurring ways, and the vericoder is the first one positioned to notice.

## Contents

1. Failure modes
2. Quick checks, in Lean
3. What to do when the spec is wrong
4. Writing a spec from intent

## 1. Failure modes

**Weak (underconstrained).** Some useless output satisfies it. A sort spec that says "the output is
sorted" but not "it's a permutation of the input" is met by `[]`. A search spec that says "if the
result is `some i` then `a[i] = x`" is met by always returning `none`.

**Vacuous.** The precondition is unsatisfiable, so every implementation is "correct". Watch for
contradictory conjuncts and preconditions that quantify over an empty range in a way that makes
them false.

**Unsatisfiable.** No implementation can meet the postcondition, for example a postcondition that
contradicts the input type, or that demands `result < x` for `x = 0` in `Nat`. You'll fail to prove
it, and that failure is the finding.

**Off by one, or wrong boundary.** `<` versus `≤`, inclusive versus exclusive ranges, the first
versus the last occurrence.

**Silent truncation and defaults.** `Nat` subtraction stops at 0, `Int.toNat` maps negatives to 0,
`a[i]!` returns `default` out of bounds, `/` by zero is 0. A spec that relies on these can say
something different from what it appears to say.

**Floats.** Lean's `Float` operations are opaque to the kernel, so almost nothing about them is
provable, not even `x + 0.0 = x`. A spec over `Float` with real-number intent is usually not
provable as written. Report it rather than fighting it.

**Mismatch with the description.** The formal spec disagrees with the docstring, the
`vc-description`, the function name or the user's words.

## 2. Quick checks, in Lean

Run these in a scratch file that imports or copies the spec. They take minutes and catch most
problems.

```lean
-- A right answer is accepted:
example : findFirst_postcond [3, 1, 3] 3 (some 0) trivial := by simp
-- A wrong answer is rejected:
example : ¬ findFirst_postcond [3, 1, 3] 3 (some 2) trivial := by decide
-- A trivial answer is rejected too:
example : ¬ findFirst_postcond [3, 1, 3] 3 none trivial := by simp
```

Use `simp [defs]`, `decide`, or `unfold defs; decide` for these; when `simp` leaves an existential
over a small range, `decide` usually finishes it. If instead you can prove the postcondition holds
for a trivial output, the spec is weak, and if you can prove that *for all inputs*, it's weak, full
stop. If you can prove the precondition is
`False`, it's vacuous. If you can prove `¬ ∃ r, post x r` for some valid `x`, it's unsatisfiable.

With Mathlib, `plausible` searches randomly for counterexamples to a proposition, which is a fast
way to test a postcondition against your implementation before trying to prove it.

## 3. What to do when the spec is wrong

**In a benchmark task, or when told not to touch the spec:** don't edit it. Implement what the
description and the function name clearly intend, which also satisfies the spec when the spec is
merely weak. Prove it, and in the report's "Spec concerns" line say exactly what's wrong, for
example "the postcondition is also satisfied by `none` for every input, so it doesn't require the
search to find anything". If the spec is unsatisfiable, report that, ideally with a proof of the
negation, instead of a fake success.

**In the user's own project:** stop and show the user the problem and a proposed fix as a diff to
the spec, with a one-line reason. Changing the spec is their decision, because the spec is the
part they're trusting. If they approve, they (or you, at their request) edit it, and a human
re-freezes with `vc_check.py freeze --force`.

## 4. Writing a spec from intent

When the user describes what they want and there's no spec yet, write the spec first and get it
approved before writing any implementation. The implementation can be redone cheaply; a spec that
silently says the wrong thing can't be detected later.

1. **Signature first.** Pick types that make bad states unrepresentable: `Fin n` for indices,
   `List.Nodup` or a subtype for distinctness, `Nat` only when negative values are truly
   impossible.
2. **Separate pre- and postconditions** as named definitions (`f_precond`, `f_postcond`) so they
   can be tested on their own.
3. **Pin the output down.** A postcondition that determines the output uniquely can't be weak.
   The strongest simple form is equality to an obviously correct reference implementation, even a
   slow one: `f x = refImpl x`. When uniqueness isn't wanted, say exactly which outputs are allowed.
4. **Test the spec** with section 2's three checks: a right answer, a wrong answer and a trivial
   answer.
5. **Show it to the user** in plain words next to the Lean, with the examples, and get a yes.
   Then freeze it and start implementing.
