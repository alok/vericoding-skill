# Dafny (experimental)

Status: the gate's Dafny bypass scan and spec freeze are unit-tested; its `dafny verify` runner has
not yet been run against a real Dafny install. Read the raw verifier output alongside the gate's
verdict, and report any disagreement.

## Running

```bash
dafny verify File.dfy          # Dafny 4.x
```

Success ends with `Dafny program verifier finished with N verified, 0 errors`. Don't pass
`--allow-axioms` or `--allow-warnings`; their warnings are exactly the ones you need to see.

## What's frozen

Signatures and contracts (`requires`, `ensures`, `reads`, `modifies`, `decreases` in the header),
and the bodies of `function` and `predicate`, since those define the spec. Method and lemma bodies
are yours. New declarations may be added between existing ones.

## Bypasses the gate rejects

`assume`, `{:axiom}`, `{:verify false}`, `{:only}`, `{:extern}`, `{:termination false}`, `expect`
(the verifier assumes it after the check), and any lemma, method or function without a body (an
axiom in disguise). `decreases *` is a warning: it gives up on termination, which the spec may need.

## Proof patterns

**Loops need invariants.** Dafny forgets everything about a loop except its invariants. State
the bounds on the index, what the accumulator means for the processed prefix, and anything about
untouched parts of the array that the postcondition needs (`a[..] == old(a[..])` when the method
must not modify it).

```dafny
method MaxArray(a: array<int>) returns (m: int)
  requires a.Length > 0
  ensures forall i :: 0 <= i < a.Length ==> a[i] <= m
  ensures exists i :: 0 <= i < a.Length && a[i] == m
{
  m := a[0];
  var k := 1;
  while k < a.Length
    invariant 1 <= k <= a.Length
    invariant forall i :: 0 <= i < k ==> a[i] <= m
    invariant exists i :: 0 <= i < k && a[i] == m
  {
    if a[k] > m { m := a[k]; }
    k := k + 1;
  }
}
```

**Termination.** Loops and recursion need a `decreases` measure when Dafny can't guess it, such as
`decreases a.Length - k` or `decreases hi - lo`.

**Sequences and multisets.** Permutation specs are usually `multiset(a[..]) == multiset(old(a[..]))`.
Taking slices (`a[..k]`) and asserting how they extend (`assert a[..k+1] == a[..k] + [a[k]];`) is
often the missing step.

**Lemmas.** A `lemma` is a ghost method whose `ensures` is the fact; call it like a statement to
bring the fact into scope. Prove recursive facts with a recursive lemma (induction) whose
`decreases` matches the structure.

**Triggers and quantifiers.** If an `exists` or `forall` won't go through, assert the instance you
need explicitly (`assert a[j] == m;`). Timeouts usually mean a quantifier is matching too broadly;
split the method, add intermediate `assert`s, or move facts into lemmas.

**`calc` blocks** make long equational steps checkable one at a time.
