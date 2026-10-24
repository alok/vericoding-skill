# Lean 4 vericoding playbook

Checked against Lean 4.35 (October 2026). Tactic names and lemma names drift between releases, so
when something here fails with "unknown identifier", search for the current name (`exact?`,
`lean_loogle`, `#check @Name`) instead of assuming the approach is wrong.

## Contents

1. Running Lean
2. Task shapes you'll meet
3. Implementation patterns
4. Proof toolkit
5. Loops and Hoare triples with `mvcgen`
6. Arrays, indices and `!`
7. Reading the common errors
8. Trust: axioms and `native_decide`

## 1. Running Lean

- `lean --version` tells you the toolchain; the project's `lean-toolchain` file pins it.
- Inside a Lake project (a `lakefile.lean` or `lakefile.toml` above the file), compile one file with
  `lake env lean path/File.lean` from the project root. A standalone `lean File.lean` can't see
  Mathlib or other dependencies. The gate finds the root on its own.
- Don't run `lake build` on a whole project to check one file; it's slower and it builds things
  you didn't touch. If Mathlib oleans are missing, `lake exe cache get` fetches them in Mathlib
  projects.
- With `lean-lsp-mcp` connected, prefer it for the inner loop:
  - `lean_goal` (goal at a line/column), `lean_diagnostic_messages` (errors for a file)
  - `lean_multi_attempt` (try several tactics at one position and see which close the goal)
  - `lean_hover_info` (types and docs), `lean_local_search` (names in the project)
  - `lean_loogle` (search by type pattern, e.g. `List.length (List.filter _ _) ≤ _`)
  - `lean_leansearch` / `lean_leanfinder` (natural-language lemma search)
  - `lean_state_search`, `lean_hammer_premise` (lemmas that might close the current goal)

## 2. Task shapes you'll meet

**Def plus theorem.** The implementation is a `def ... := sorry` and the spec is one or more
theorems about it. Only the `sorry`s are yours.

```lean
def sumOdds (n : Nat) : Nat := sorry
theorem sumOdds_spec (n : Nat) : sumOdds n = n * n := by sorry
```

**Precondition-carrying defs** (Verina-style benchmarks). The function takes
`(h_precond : f_precond x)` and the postcondition is a separate `@[reducible]` def. The theorem is
`f_spec_satisfied : f_postcond x (f x h_precond) h_precond`. You may use `h_precond` in the
implementation, for example to justify an array index or a `head`.

**Subtype results.** `def f (x : α) : {r : β // P x r} := sorry` asks for the value and its proof
together. Build it as `⟨value, proof⟩`, and prove the hard part as a separate lemma about a plain
helper function.

**Hoare triples about monadic code.** The spec is `⦃⌜P⌝⦄ prog ⦃⇓ r => ⌜Q r⌝⦄` (from `Std.Do`) or an
equation about `Id.run do ...`. See section 5.

**Mathlib specs.** `Finset.sum`, `Nat.Prime`, real numbers and so on. You need a Lake project with
Mathlib, and you get its tactics (`ring`, `linarith`, `nlinarith`, `positivity`, `norm_num`,
`aesop`, `plausible`).

## 3. Implementation patterns

**Mirror the spec.** If the spec is phrased with `List.filter`, `List.foldl` or structural
recursion, an implementation with the same shape makes the proof an induction that follows the
code. A cleverer implementation needs a lemma that it agrees with the obvious one, and that lemma
is usually most of the work.

**Structural recursion first.** Pattern-match on the argument (`| [] => ... | x :: xs => ...`,
`| 0 => ... | n + 1 => ...`). When you need well-founded recursion, give the measure explicitly and
discharge it:

```lean
def f (lo hi : Nat) : Nat :=
  if h : lo < hi then f (lo + 1) hi + lo else 0
termination_by hi - lo
decreasing_by omega
```

Avoid `partial def`. Lean can't unfold it, so nothing about it is provable, and the gate warns.

**Recursion with a precondition.** If `f xs (h : P xs)` recurses on `rest`, you must prove
`P rest` at the call. When that's awkward, write a total helper without the precondition (return a
default on bad input), define `f xs h := helper xs`, and prove everything about `helper`. In a
benchmark file the helper can live in `vc-helpers`, since it doesn't mention `f`.

**Accumulators.** Tail-recursive or `foldl` implementations need a generalized invariant. Prove
`∀ acc, go xs acc = acc + spec xs` by `induction xs generalizing acc`, then specialize at the
initial accumulator. Forgetting `generalizing` is the most common reason such inductions get
stuck.

**Executable, honest implementations.** No `noncomputable`, no `Classical.choose`, no
`Exists.choose` in the implementation. Those type-check and implement nothing. The gate warns.

**Test before proving.** In a scratch file:

```lean
#guard sumOdds 4 = 16
#guard findFirst [3, 1, 3] 3 trivial = some 0
```

`#guard` fails at compile time if the boolean is false. Use `#eval` only in scratch files; the gate
rejects it in the task file because `#eval` can run arbitrary metaprograms.

## 4. Proof toolkit

**Unfolding.** `simp [f]` or `simp only [f]` unfolds `f` using its equation lemmas; `unfold f` does
it without simplifying; `rw [f]` rewrites one occurrence; `f.eq_def` is the unfolding equation.
Run `simp?` to turn a working `simp` into a stable `simp only [...]`.

**Arithmetic.**
- `omega` decides linear arithmetic over `Nat` and `Int`, including `/` and `%` by literals and
  `Nat` subtraction. It doesn't do nonlinear terms.
- `grind` combines congruence closure, case splits, linear arithmetic and commutative-ring
  normalization. It closes `sumOdds k + (2 * k + 1) = (k + 1) * (k + 1)` directly. Give it lemmas
  with `grind [foo, bar]`.
- `decide` evaluates a closed decidable proposition. It fails on non-reducible definitions; use
  `unfold f; decide` or `simp [f]`. `decide +kernel` checks by kernel reduction and adds no axiom.

**Induction.**
- `induction xs with | nil => ... | cons x xs ih => ...`, with `generalizing acc` when other
  variables change in the recursive call.
- `fun_induction f x` does induction along `f`'s own recursion, with one case per branch of `f`
  (named `case1`, `case2`, ...). It is usually the right first move for a theorem about a recursive
  implementation.

  ```lean
  theorem sumOdds_spec (n : Nat) : sumOdds n = n * n := by
    fun_induction sumOdds n with
    | case1 => rfl
    | case2 k ih => grind
  ```

**Case analysis.** `split` handles the `if` or `match` in the goal; `by_cases h : p`;
`cases h : e with ...` keeps the equation; `obtain ⟨i, hi, rfl⟩ := h` destructures and substitutes.
If `split` splits the wrong thing, `by_cases` on the `if` condition first, then `simp [h]`.

**Existentials and conjunctions.** `refine ⟨w, ?_, ?_⟩` leaves the side goals; `constructor`;
`exact ⟨_, _⟩`.

**Finding lemmas.** `exact?` (closes the goal with one lemma if it can), `try?` (suggests whole
tactic scripts), `simp?`/`grind?`, then `lean_loogle` and `lean_leansearch` from the LSP tools.
Never leave `apply?` in a final proof; it can close goals with `sorry`.

**Mathlib only.** `ring`, `linarith`, `nlinarith`, `positivity`, `norm_num`, `aesop`, `plausible`
(random testing for counterexamples), and big-operator lemmas such as `Finset.sum_range_succ`.

**Benchmark files can't add imports.** Imports live in the frozen `vc-preamble`, so use only what
it already imports. In general mode you may add imports right after the existing ones.

## 5. Loops and Hoare triples with `mvcgen`

`Std.Do` turns a monadic program into verification conditions. The pattern for an `Id.run do`
loop:

```lean
import Std.Tactic.Do
open Std.Do

def sumList (xs : List Nat) : Nat := Id.run do
  let mut acc := 0
  for x in xs do
    acc := acc + x
  return acc

theorem sumList_spec (xs : List Nat) : sumList xs = xs.sum := by
  generalize h : sumList xs = r
  apply Id.of_wp_run_eq h
  mvcgen
  case inv1 => exact ⇓⟨cur, acc⟩ => ⌜acc = cur.prefix.sum⌝
  all_goals mleave; grind
```

- The invariant gets the loop cursor (`cur.prefix` is what's been visited, `cur.suffix` what's
  left) and the mutable state. Several `let mut` variables arrive as a tuple **in declaration
  order**: `let mut s := 0; let mut c := 0` gives `⇓⟨cur, s, c⟩`. Swapping them produces a
  confusing `grind` failure, not a type error.
- `mvcgen [f, g]` unfolds `f` and `g` while generating conditions; `@[spec]` lemmas about callees
  let you reason compositionally (`⦃P⦄ callee ⦃⇓ r => Q r⦄` once, then reuse).
- `mleave` turns the remaining `SPred` goals into ordinary propositions for `grind`, `simp` or
  `omega`.
- Early `return` inside the loop needs
  `Invariant.withEarlyReturnNewDo (onReturn := ...) (onContinue := ...)`. Put `exact` on its own
  line under `case inv1 =>`. If it shares the line, the argument lines are indented less than
  `exact` and Lean silently drops them, which shows up as a type mismatch that mentions
  `fun onContinue onReturn => ...`.
- Range loops: `for h : i in [0:a.size] do ... a[i] ...` puts the bound proof in scope so `a[i]`
  needs no `!`.
- Hoare-triple specs look like `⦃⌜True⌝⦄ prog x ⦃⇓ r => ⌜post x r⌝⦄`; start with `mvcgen [prog]`.
- Version note: in Lean 4.35 `mvcgen` works but warns that it's deprecated in favor of `vcgen`,
  which is still experimental and failed on simple loops in testing. Use `mvcgen` and silence the
  warning with `set_option linter.deprecated.syntax false` if it's noisy (the gate allows `linter.*`
  options). On older toolchains you may need `set_option mvcgen.warning false`.

## 6. Arrays, indices and `!`

- `a[i]` needs a proof of `i < a.size` in scope (found automatically by `get_elem_tactic`, or
  given as `a[i]'h`). `a[i]!` returns `default` when out of bounds and needs no proof.
- Specs written with `!` are common in benchmarks. To reason about `a[i]!`, establish the bound and
  rewrite with `getElem!_pos a i h : a[i]! = a[i]`, then use the ordinary lemmas.
- Useful lemma families: `Array.size_map`, `Array.getElem_map`, `Array.size_ofFn`,
  `Array.getElem_ofFn`, `List.length_map`, `List.getElem_map`. `Array.ofFn` is often the easiest
  array implementation to prove things about.
- When an array spec gets painful, convert: `a.toList` has richer lemmas, and `Array.toList_map`
  style lemmas move between the two.

## 7. Reading the common errors

| Error | Usual cause | Try |
|---|---|---|
| `unsolved goals` | The tactic did part of the work | Read the goal; finish with `omega`, `grind`, `simp_all` |
| `simp made no progress` | Wrong normal form, or the lemma doesn't fire | `simp?` to see what fires; `unfold` first; `rw` the exact lemma |
| `failed to synthesize Decidable ...` | `decide` on a non-reducible def | `unfold f; decide`, or `simp [f]` |
| `failed to prove termination` | No obvious decreasing measure | `termination_by <measure>` and `decreasing_by omega` (or `simp_wf; omega`) |
| `motive is not type correct` | Rewriting inside a dependent type | `generalize` the term first, or use `simp` instead of `rw` |
| `deterministic timeout` / `maxHeartbeats` | Search blew up | Split into lemmas; `simp only`; as a last resort `set_option maxHeartbeats 400000 in` (allowed by the gate) |
| `unknown identifier` for a lemma | Renamed between versions | `exact?`, `lean_loogle`, `#check @Name` |
| `grind failed` with a facts dump | Missing lemma or wrong invariant | Read the dump: the unprovable fact names what's missing |

## 8. Trust: axioms and `native_decide`

`#print axioms thm` lists everything `thm` ultimately rests on. A finished vericoding proof should
show only `propext`, `Classical.choice` and `Quot.sound`. The gate runs this for every frozen
declaration.

- `sorryAx` means a `sorry` survived somewhere, possibly in a lemma you called.
- `native_decide` trusts compiled code instead of the kernel. In Lean 4.35 each use adds an axiom
  named like `thm._native.native_decide.ax_1_1`; older toolchains show `Lean.ofReduceBool`. It's
  sometimes acceptable for large finite checks, but it enlarges the trusted base, so the gate
  rejects it unless you pass `--allow-native`, and the report must say so. Prefer `decide` or
  `decide +kernel`.
- Any other name is a custom axiom, which is a bypass.
