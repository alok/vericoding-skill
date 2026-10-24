# Verus (experimental)

Status: the gate's Verus bypass scan and spec freeze are unit-tested; its `verus` runner has not yet
been run against a real Verus install. Read the raw verifier output alongside the gate's verdict,
and report any disagreement.

## Running

```bash
verus file.rs                  # add --crate-type=lib when there's no fn main (the gate does this)
```

Success prints `verification results:: N verified, 0 errors`.

## What's frozen

`fn` signatures, `requires`, `ensures` and `decreases` clauses, and the bodies of `spec fn`, since
those define the spec. Bodies of exec `fn` and `proof fn` are yours. New items may be added between
existing ones.

## Bypasses the gate rejects

`assume(...)`, `admit()`, `#[verifier::external_body]`, `#[verifier::external]`,
`assume_specification`, `external_fn_specification`, `unimplemented!()`, `todo!()` and `unsafe`.
Warnings: `exec_allows_no_decreases_clause`, `#[verifier::truncate]`, `uninterp`, `cfg` attributes
(they can hide code from the verifier), new `use` imports (they can shadow names the spec uses) and
new `macro_rules!`.

## Syntax that trips people up

- Each of `requires`, `ensures` and `invariant` appears once per item, followed by comma-separated
  clauses:

  ```rust
  fn max_array(a: &Vec<i32>) -> (m: i32)
      requires
          a.len() > 0,
      ensures
          forall|i: int| 0 <= i < a.len() ==> a[i] <= m,
          exists|i: int| 0 <= i < a.len() && a[i] == m,
  {
      let mut m = a[0];
      let mut k: usize = 1;
      while k < a.len()
          invariant
              1 <= k <= a.len(),
              forall|i: int| 0 <= i < k ==> a[i] <= m,
              exists|i: int| 0 <= i < k && a[i] == m,
          decreases a.len() - k,
      {
          if a[k] > m {
              m = a[k];
          }
          k += 1;
      }
      m
  }
  ```

- Spec code uses mathematical `int` and `nat`; exec code uses machine integers. Convert with
  `x as int`. Use the `@` view (`v@`, `v@[i]`, `v@.len()`) to talk about a `Vec` as a `Seq`.
- Arithmetic in exec code must be shown not to overflow: add bounds to `requires` and invariants
  (`s + x <= i32::MAX`) or use a wider type.
- Put assertions and lemma calls in `proof { ... }` blocks inside exec code.
- Nonlinear facts need `by (nonlinear_arith)`; bit-vector facts need `by (bit_vector)`. Look in
  `vstd` (for example `vstd::arithmetic`) for lemmas before writing your own.
- Inside a loop, assume Verus knows only the invariant. Depending on the version and the
  `loop_isolation` setting, it may also see the function's preconditions, but restating the facts
  you need in the invariant is cheap and always works.
