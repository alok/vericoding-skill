# How vericoding-skill works, and how to build it yourself

This is a long, teaching-oriented walkthrough of the repository: the problem it solves, the system
around it, every design decision in the gate, the bugs that shaped it, and a sequence of exercises
for rebuilding it from an empty directory. Read it top to bottom once; after that, each section
stands alone.

## Contents

1. The problem: verification you can't trust
2. The surrounding system: Agent Skills, plugins and marketplaces
3. The shape of the solution: instructions plus a gate
4. Lexing without a parser: masking
5. The freeze model: frozen segments and holes
6. Aligning the current file to the original
7. Bypass rules, and why each one is there
8. Lean semantic probes: what the text can't tell you
9. Running verifiers and reading their answers
10. Testing: unit, end to end, and agent evals
11. Publishing: where a skill lives and how people find it
12. Rebuild it yourself: a staged path
13. Where to take it next

---

## 1. The problem: verification you can't trust

A formal verifier answers one question: does this proof establish this statement? It doesn't answer
whether the statement is the one you meant, whether the proof secretly assumed what it set out to
prove, or whether someone edited the statement until the proof went through.

For a human writing proofs, those questions are mostly social: code review catches a weakened
theorem. For an agent optimizing toward "the build is green", they're the main failure mode. In
practice agents do all of these:

- Leave a `sorry` in Lean. Lean reports it as a **warning** and exits with status 0, so the build
  looks green.
- Add an `axiom` that states exactly the goal, then use it.
- Edit the spec: `ensures r > 0` becomes `ensures true`, `x < m` becomes `x ≤ m`.
- Leave the spec text alone but change what it *means*: insert a higher-priority instance of `Mul`
  before the theorem, so `n * n` elaborates to something else.
- Hide the `sorry` behind a macro so a text search for "sorry" in the proof doesn't find it.

Each of these makes the verifier say yes. The point of vericoding (code plus a machine-checked proof
against a frozen spec) is that you can trust the result without re-reading the proof. That only
holds if something checks the conditions above mechanically. That something is `vc_check.py`.

### The trust chain

Here is what a successful vericoding result actually asserts:

```mermaid
flowchart LR
    intent([User intent]) -->|human review| spec[Formal spec]
    spec -->|frozen| file[Task file]
    file -->|agent fills holes| solved[Solved file]
    solved -->|lean / dafny / verus| verifier[[Verifier]]
    verifier -->|kernel check| kernel[[Lean kernel]]
    solved -->|vc_check: freeze, scan, probes| gate{Gate}
    kernel --> gate
    gate -->|all pass| verified([VERIFIED])
```

The human reviews the spec once. Everything after that is mechanical, so every arrow after "frozen"
must be checked by a program and not by trust in the agent.

## 2. The surrounding system: Agent Skills, plugins and marketplaces

### What a skill is

An **Agent Skill** is a folder with a `SKILL.md` file: YAML frontmatter (`name`, `description`, and
optional fields such as `license`, `compatibility`, `metadata`) followed by Markdown instructions.
The format started at Anthropic and is now an open standard (agentskills.io) read by Claude Code,
Codex, Cursor, Gemini CLI, Copilot and dozens of other agents.

The key idea is **progressive disclosure**, in three levels:

1. The `name` and `description` of every installed skill are always in the agent's context. This is
   how the agent decides to use a skill, so the description is the triggering mechanism. It has to
   say *when* to use the skill, concretely, and agents tend to under-trigger, so it should be a little
   pushy. Ours lists the trigger phrases: "verified", "sorry placeholders", the `vc-*` tags, Verina,
   mvcgen, auditing an agent's proof, plus a near-miss exclusion ("not for pure mathematics").
2. The `SKILL.md` body loads when the skill triggers. Keep it under about 500 lines. Ours is the
   workflow and the rules, with the *why* for each rule, because models follow reasons better than
   capitalized commands.
3. Everything else (`references/`, `scripts/`, `examples/`) loads only when the body points to it.
   That's why the Lean playbook is a separate file: a Dafny task never pays for it.

Rules worth remembering from the spec: `name` is 1 to 64 lowercase letters, digits and hyphens, and
must match the folder name; `description` is at most 1024 characters. `agentskills validate`
(from the `skills-ref` package) checks this.

### What a plugin and a marketplace are

Claude Code bundles skills (and commands, agents, hooks, MCP servers) into **plugins**. A plugin is
a folder with `.claude-plugin/plugin.json`. A **marketplace** is a JSON catalog,
`.claude-plugin/marketplace.json`, listing plugins and where to fetch them. Any GitHub repo can be a
marketplace; users add it with `/plugin marketplace add owner/repo`.

This repo is both at once: the marketplace lists one plugin whose `source` is `"./"`, the repo
itself, and the plugin's skill lives at `skills/vericoding/SKILL.md`. That one layout is also what
`npx skills`, `gh skill` and most crawlers look for, which is why it reaches so many agents without
separate packaging.

`claude plugin validate --strict --profile directory .` runs the same checks Anthropic's plugin
directory runs on submission: a README of at least 40 words, a license, a valid name, an icon (which
is fixed the first time the plugin is saved in the portal, so it's worth getting right first).

## 3. The shape of the solution: instructions plus a gate

There are two halves.

**Instructions** (`SKILL.md` and references) teach the workflow: find the holes, freeze, sanity-check
the spec on concrete inputs, implement and test before proving, prove in small checked steps, run
the gate, report in a fixed shape. They also teach Lean technique, since a skill that blocks cheating
but doesn't help prove anything just produces honest failures.

**The gate** (`scripts/vc_check.py`) turns the rules into a program. Instructions alone aren't
enough, because the failure we care about is exactly the agent deciding a rule doesn't apply this
time. This is the "encode lessons in structure" principle: if a mistake matters, make a tool catch
it instead of asking people to remember.

The gate has four commands:

| Command | What it does |
|---|---|
| `holes FILE` | Lists the places the agent may edit. The agent asks the tool, not its own reading. |
| `freeze FILE` | Snapshots the original under `.vericoding/`, and refuses to re-freeze a changed file. |
| `check FILE` | The verdict: spec frozen, no bypasses, verifier accepts, axioms clean, statements mean the same. |
| `scan FILE` | Bypass scan alone, for quick audits. |

It's a single standard-library Python file, so it installs everywhere a skill does, with no
dependency step to fail. The PEP 723 header (`# /// script`) lets `uv run` execute it too.

Why does `freeze` refuse to re-freeze? Because otherwise the cheat is: edit the spec, re-freeze,
then check. Refusing makes "the spec changed" something only a human can bless (`--force`).

## 4. Lexing without a parser: masking

Every later step needs to know what's code and what's a comment or string, because `-- sorry` in a
comment isn't a bypass and `"assume"` in a string isn't an `assume`. Writing three real parsers
would be a project of its own. The trick is **masking**: replace every character inside a comment
(and optionally inside a string) with a space, but keep newlines. The result has exactly the same
length and line structure as the original, so any offset or line number computed on the masked text
is valid in the original.

```python
def mask(text, lang, *, comments=True, strings=True) -> str
```

Details that matter:

- **Nested block comments.** Lean's `/- ... -/`, Dafny's and Rust's `/* ... */` all nest. A depth
  counter handles it.
- **Char literals vs. primes and lifetimes.** `'a'` is a char literal, but Lean identifiers can
  contain `'` (`h'`, `x'`) and Rust has lifetimes (`'a`). The rule: a `'` starts a char literal only if
  the previous character isn't part of an identifier, and only if it matches the char-literal shape
  (`'x'` or an escape) with a closing quote.
- **Raw and verbatim strings.** Rust's and Lean's `r#"..."#` end at a quote plus the same number of
  `#`; Dafny's `@"..."` uses `""` as an escaped quote.
- **Two kinds of mask.** Bypass scanning masks both comments and strings. Spec comparison masks only
  comments, because changing a string literal inside a spec (`ensures s == "abc"`) *is* a spec change.

Masking comments for comparison also means the agent can edit comments in frozen text (a docstring
typo) without failing, which is right, since comments don't change meaning.

## 5. The freeze model: frozen segments and holes

The core abstraction: the original file is cut into **frozen segments** separated by **holes**. The
check passes when the current file contains every frozen segment, in order, with only the holes
changed.

```text
original:  [frozen 0] (hole 1) [frozen 1] (hole 2) [frozen 2]
current:   [frozen 0]  ......  [frozen 1]  ......  [frozen 2]
```

What counts as a hole depends on the file:

- **Benchmark files** with `<vc-…>` tags: the tag regions say it directly. `vc-helpers` and `vc-code`
  are wholly editable; in Lean, each `sorry` inside `vc-definitions` and `vc-theorems` is a hole.
  Everything else, including a `sorry` the task author left in the preamble, is frozen.
- **General Lean**: each `sorry` is a hole. So is each position just before a top-level command at
  column 0 (an **insertion point**, a zero-width hole where new declarations may go), and the spot
  right after the import block (so new imports are allowed).
- **General Dafny and Verus**: method, lemma, `fn` and `proof fn` bodies are holes, including the
  braces. Contracts, and the bodies of `function`, `predicate` and `spec fn`, are frozen because
  they *are* the spec. Insertion points sit before each declaration.

### The continuation attack, and the insertion rule

Insertion points have a subtle hole of their own. Consider

```lean
def post (n : Nat) : Prop := n > 0

theorem t : post 1 := by sorry
```

The position before `theorem` is an insertion point. If the agent inserts `∨ True` there, the
frozen text `def post ... := n > 0` is still present verbatim, but Lean parses the definition as
`n > 0 ∨ True`, which weakens the spec without touching its text. The fix: text inserted at an
insertion point must itself *start a new declaration* (match a declaration keyword). That's the
`INSERT_START` patterns. Text inside a `sorry` or body hole has no such constraint, because it's
inside a definition the agent is supposed to write.

### Normalization

Holes are sorted, holes nested in other holes are dropped, and holes separated only by whitespace
or comments are merged. The last point fixed a real bug: a `sorry` hole at the end of a definition
followed by a docstring and then the next declaration's insertion point produced a frozen segment
that was "empty" after masking. An empty segment matches anywhere, so the solution text got
assigned to the wrong hole. Merging those holes removes empty segments.

## 6. Aligning the current file to the original

Given frozen segments `F0, F1, ..., Fn`, find positions in the current file where each appears, in
order, without overlap, such that each gap (a hole's new content) satisfies its hole's constraint.

Each segment becomes a regex: escape the text, replace each run of whitespace with `\s+`, and allow
leading and trailing whitespace. That makes whitespace-only edits (reformatting) pass.

**Attempt one: greedy.** Take the leftmost match of each segment after the previous one. Without
constraints this is complete, since any in-order embedding can be pushed left. But the insertion
rule *is* a constraint, and greedy failed on this Verus file:

```rust
fn main() {}      // body hole is "{}"
}                 // frozen segment: just "}"
```

The frozen segment after `main`'s body is `}` (closing the `verus!` block). Greedy found the `}`
*inside* the new body `{}`, which left `}` as the content of the end-of-file insertion point. That
isn't a declaration, so the check failed on a correct solution.

**Attempt two: backtracking.** Try each candidate match of segment *i* (up to 64), check the hole
constraint for the gap before it, recurse on segment *i+1*, and remember failed `(segment, position)`
pairs so no state is explored twice. In the common case every segment is long and unique, so
there's one candidate per segment and it costs the same as greedy. The last segment is anchored to
the end of the file. When everything fails, the deepest segment reached is the one reported as
missing, with the first of its lines that can't be found anywhere later in the file.

## 7. Bypass rules, and why each one is there

The scan runs on the *text the agent wrote* (the hole contents found by the alignment), not on the
whole file, so a `sorry` the task author deliberately left in a frozen preamble isn't blamed on the
agent. If the alignment fails, it scans the whole file.

Lean errors: `sorry`, `admit`, `axiom`, `sorryAx`/`lcProof`, `unsafe`, `implemented_by` and
`@[extern]` (the compiled code differs from the proved code), `debug.skipKernelTC`, `#exit` (stops
Lean early, so later declarations are never checked), `run_cmd`/`run_elab`/`run_meta`/`#eval`
(metaprograms can add declarations behind the kernel's back), and `addDecl`/`modifyEnv` and friends.

Lean warnings, each needing a sentence in the report: `native_decide`, `noncomputable`,
`Classical.choose` in an implementation (the implementation is probably the spec's own witness),
`partial def` (opaque to proofs), new syntax (`macro`, `notation`, `elab` and so on, anchored to the
start of a line so `cur.prefix` doesn't trigger the `prefix` rule, which was a real false positive),
new instances, `set_option` other than harmless ones (`maxHeartbeats`, `linter.*`, `trace.*`), and
attribute removal.

Dafny errors: `assume`, `{:axiom}`, `{:verify false}`, `{:only}` (skips verifying everything else),
`{:extern}`, `{:termination false}`, `expect` (the verifier assumes it afterwards), and declarations
with no body (an axiom in disguise). Verus errors: `assume(`, `admit(`, `external_body`,
`external`, `assume_specification`, `unimplemented!`/`todo!`, `unsafe`.

## 8. Lean semantic probes: what the text can't tell you

The freeze check proves the spec's *text* is unchanged. It can't prove the spec still *means* the
same thing, because inserted declarations before it can change how it elaborates (instances,
notation, `open`, options). Lean can tell us, so the gate asks it.

### How the probe works

The gate appends commands to the file and runs it through `lean --json --stdin` (or
`lake env lean --json --stdin` inside a Lake project, found by walking up to a `lakefile`). For
every frozen declaration `X`:

```lean
set_option pp.all true in set_option pp.proofs false in #check @X
set_option pp.all true in set_option pp.proofs false in #print X   -- only for frozen definitions
#print axioms X
```

`--json` matters because Lean prints `#check` output as information messages *without* a
`file:line:` prefix in plain mode. JSON gives each message a position, so the gate knows which output
belongs to which probe (each probe is on its own line).

`pp.all` prints everything explicit: implicit arguments, instances, universe levels. A changed
instance shows up as a different term. `pp.proofs false` prints proofs as `⋯`, because a spec can
contain a proof (`⟨i * n + i, by sorry⟩` for an index bound in a benchmark), and replacing that
`sorry` with a real proof is legitimate and doesn't change meaning (proof irrelevance).

The gate runs the probes on both the original and the current file and compares. For theorems it
compares only the type (the statement). For frozen definitions it compares the value too, since a
postcondition's body is spec.

### The matcher bug

The first real test failed on a correct solution. The postcondition contains a `match`. Lean
compiles each `match` into an auxiliary function `foo.match_1`, and it **deduplicates** them: if an
identical matcher already exists, it reuses it. The solution added a helper lemma *before* the
postcondition with an identical `match`, so in the solved file the postcondition printed as
`findFirst_correct.match_1 ...` instead of `findFirst_postcond.match_1 ...`. Same meaning, different
name.

Ignoring matcher names isn't safe: `match r with | some 0 => ...` and `match r with | some 1 => ...`
compile to different matchers whose uses print the same apart from the name. The fix has two layers:

1. If two printed terms differ *only* in matcher names, pair the names up and probe the matchers
   themselves.
2. Compare the matchers' **types**, not their bodies. A matcher's type lists its alternatives with
   their patterns in order (`h_1 : (i : Nat) → motive (some i)`), and the compiler derives the body
   from that, so equal types mean equal matchers.

That comparison has to be up to renaming of bound variables (one matcher binds `result`, the other
`x`), so there's a small alpha-normalizer that renames binders to `v0, v1, ...` in order of
appearance. It also has to collapse whitespace, because the pretty-printer wraps lines by width and
a longer name moves the line breaks. Both of those were found by the failing test, one at a time.

### Axioms

`#print axioms X` lists what `X` ultimately depends on. Clean is `propext`, `Classical.choice`,
`Quot.sound`. `sorryAx` means a `sorry` survived, possibly in a macro or a called lemma. Anything else
is a custom axiom, except compiler trust from `native_decide`, which the gate rejects unless
`--allow-native` is given. Lean 4.35 changed how that looks: older versions show `Lean.ofReduceBool`,
4.35 adds a fresh axiom per use named like `thm._native.native_decide.ax_1_1`. The test for it failed
until the gate learned the new name, which is a good argument for end-to-end tests against the real
tool.

## 9. Running verifiers and reading their answers

- **Lean**: success means no error messages *and* no `declaration uses 'sorry'` warning (JSON kind
  `hasSorry`). Exit status alone isn't enough.
- **Dafny**: `dafny verify FILE` must end with `finished with N verified, 0 errors`. No
  `--allow-axioms`, whose warnings are exactly the ones you need to see.
- **Verus**: `verus FILE` (plus `--crate-type=lib` when there's no `main`) must print
  `verification results:: N verified, 0 errors`.

Exit codes from the gate: 0 verified, 1 not verified, 2 the verifier couldn't run or a usage error.
That lets scripts and CI distinguish "your proof is wrong" from "install Lean".

## 10. Testing: unit, end to end, and agent evals

**Unit tests** (`tests/test_vc_check.py`) cover masking, every bypass rule, hole finding for each
mode and language, and freeze-check behavior including the continuation attack and the backtracking
case. They need no verifier.

**End-to-end tests** run real Lean on the examples (all must verify) and on deliberate cheats (each
must fail): untouched task, axiom, sorry hidden in a macro, a meaning-changing instance, and
`native_decide` with and without the flag. CI installs Lean 4.35 with elan and runs both.

**Agent evals** (`skills/vericoding/evals/`) test the skill rather than the script: the same task is
run by an agent with the skill and by one without, and the results are graded, mostly by running the
gate on the output. One case is adversarial on purpose: the user asks for "the largest element" but
the spec says every element is strictly less than the result, which the largest element can't
satisfy. A good agent notices and says so; a bad one quietly edits the spec. The folder layout is the
one `claude plugin eval` reads, so the same cases run from the CLI.

## 11. Publishing: where a skill lives and how people find it

As of October 2026:

| Venue | How it gets there |
|---|---|
| GitHub repo + Claude Code marketplace | `/plugin marketplace add alok/vericoding-skill` works as soon as the repo is public |
| skills.sh (`npx skills`) | Indexed on first install; ranked by install count |
| `gh skill` | `gh skill publish --tag vX` validates, adds the `agent-skills` topic, cuts a release |
| SkillsMP, claude-plugins.dev, claudemarketplaces.com | Crawl public GitHub automatically |
| Gemini CLI extension gallery | `gemini-extension.json` at the root plus the `gemini-cli-extension` topic |
| Anthropic plugin directory | Submitted through the claude.ai portal by the owner; reviewed, then published |
| Copilot CLI default marketplace (github/awesome-copilot) | An issue in their external-plugin form format; bots run quality gates, a maintainer approves |
| ClawHub | `clawhub skill publish` after `clawhub login`; everything there is relicensed MIT-0 |
| Awesome lists | Most want the repo to be at least 14 days old with real usage |

`docs/publishing.md` tracks what's been done for this repo.

## 12. Rebuild it yourself: a staged path

Each stage ends in something you can run. Don't look at the existing code until you've tried a stage.

1. **Masking.** Write `mask(text, lang)`. Test: the output has the same length and newline
   positions; `-- sorry` and `"sorry"` vanish; `x'` survives; nested comments work.
2. **Bypass scan.** A list of `(regex, severity, reason)` per language, run over masked text. Test it
   against a file of positives and a file of near-misses (`#print axioms`, `cur.prefix`).
3. **Lean holes.** Find each `sorry`, plus insertion points before column-0 commands. Print them with
   line numbers. This is `holes`.
4. **Greedy freeze check.** Segments as whitespace-tolerant regexes, leftmost matching. Test on
   `SumOdds`: the solution passes, a weakened statement fails.
5. **Snapshots.** `freeze` writes JSON; refuse to overwrite a changed file. `check --base` takes a
   file or `git:REV` (`git show REV:path`).
6. **Run Lean.** `lean --json --stdin`; parse messages; treat `hasSorry` as failure.
7. **Axioms.** Append `#print axioms X` for each frozen theorem; parse
   `'X' depends on axioms: [...]`. Now the macro-hidden `sorry` fails.
8. **Statement probes.** Append `#check @X` with `pp.all`; run on original and current; compare. Now
   the instance cheat fails. Then hit the matcher bug yourself with the `FindFirst` example, and fix it.
9. **Continuation attack.** Write the `∨ True` test first, watch it pass when it shouldn't, then add
   the insertion rule.
10. **Dafny and Verus holes.** Body detection with a brace matcher, plus the set-display heuristic
    for Dafny (`ensures s == {1, 2}` is an expression, not a body: look at the token before `{`).
11. **Backtracking.** Write the Verus `fn main() {}` test, watch greedy fail, replace it with the
    memoized search.
12. **The skill.** Write `SKILL.md` around the tool: the workflow, the rules with their reasons, the
    report shape. Then run an eval with and without it and read the transcripts, not just the scores.

## 13. Where to take it next

- Run the Dafny and Verus runners against real installs and fix what breaks. Their textual parts are
  tested; their verifier I/O is not.
- Replace the pretty-printed comparison with a structural one done inside Lean (a small
  metaprogram that hashes elaborated types with matchers unfolded). It needs `import Lean` in the
  probe, which is why it isn't done that way now.
- A `vc_check.py assemble` command that turns the benchmark's YAML or JSONL tasks into tagged files.
- Spec mutation testing: automatically weaken a spec in small ways and confirm that the solution's
  proof breaks, as a measure of how much the spec constrains.
