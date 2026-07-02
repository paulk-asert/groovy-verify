<!--
  SPDX-License-Identifier: Apache-2.0

  Licensed under the Apache License, Version 2.0 (the "License");
  you may not use this file except in compliance with the License.
  You may obtain a copy of the License at

      https://www.apache.org/licenses/LICENSE-2.0

  Unless required by applicable law or agreed to in writing, software
  distributed under the License is distributed on an "AS IS" BASIS,
  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
  See the License for the specific language governing permissions and
  limitations under the License.
-->

# Tool knobs

Six environment variables tune what the checker *reports* — never what it proves. They're **transient tooling**,
set per run, distinct from the permanent `@TypeChecked(extensions = …)` configuration; unset, every one leaves the
default path byte-identical.

| knob | what it adds |
|------|--------------|
| `VERIFY_REFUTATION=assert\|junit\|spock` | render a refutation's counterexample as a runnable repro test |
| `VERIFY_SUGGEST=contract` | suggest the `@Requires` that would discharge a refuted implicit obligation |
| `VERIFY_EXPLAIN` | on a *verified* obligation, show which authored `@Requires` clauses the proof used |
| `VERIFY_VERBOSE` | print the full OpenJML-style diagnostic + counterexample behind each one-line result |
| `VERIFY_CACHE_STATS` | print the in-process VC-cache hit / miss ratio |
| `VERIFY_DUMP_SMT` | print every solver query as a self-contained SMT-LIB2 benchmark (pipe to cvc5/z3/yices) |

The first three act on one diagnostic, in three directions. Take an unguarded index access:

<!-- doclint:ignore Tool-knobs walkthrough scaffold — illustrative unguarded method shared by the three knob examples -->
```groovy
static int g(int[] a, int i) { a[i] }   // no guard — the bounds obligation refutes
```

It refutes with a concrete counterexample:

```
[Static type checking] - Possible IndexOutOfBoundsException: index may be out of bounds
    obligation: 0 <= i && i < a.size()
    counterexample: a.size() = 0, i = -1
    fails on: g(new int[0], -1)
```

**`VERIFY_REFUTATION` — counterexample → runnable test.** That `fails on:` line is the default repro — a call to
paste and watch throw. Set `VERIFY_REFUTATION=junit` (or `assert` / `spock`) and the *same* counterexample is
rendered as a self-checking test instead:

```
repro (JUnit):
    @Test void gFails() { assertThrows(IndexOutOfBoundsException.class, () -> C.g(new int[0], -1)); }
```

It's a confirmation bridge, not a keeper. The test is green *while the bug is live* — the call really throws — so
run it to prove the compile-time counterexample is a genuine runtime failure (ruling out a verifier
false-positive). Then fix the bug and **flip the test**: once the call no longer throws, invert the assertion into
a regression — *"this input is now handled"* — or delete it. (A verify-only obligation like integer overflow wraps
silently at runtime, so it has no exception to assert and is shown as documentary.)

**`VERIFY_SUGGEST` — refutation → suggested contract.** The complementary move — not *what input breaks it* but
*what precondition would fix it*. Set `VERIFY_SUGGEST=contract` and the same refutation gains one line:

```
    suggested fix: @Requires({ 0 <= i && i < a.size() })
```

Paste that `@Requires` onto `g` and the bounds obligation discharges — the refutation becomes a proof. This is the
Clousot / CodeContracts abduction angle: the guard is the positive form of the violated check, in your own
spelling (`.size()` vs `.length`). It only fires when that guard is a valid precondition — referencing parameters
and fields, never a local or loop variable — so it pastes verbatim. It's a hint, not an auto-fix (a guarded `if`
or a class invariant is often the better home), and overflow is excluded on purpose: its honest guard depends on
operand signs, and the naive range-check would read vacuously under Groovy's wrapping int arithmetic.

**`VERIFY_EXPLAIN` — proof → the clauses it leaned on.** The third direction runs on the obligations that *pass*.
With `g` now guarded — and, say, slightly over-specified — `VERIFY_EXPLAIN` reports, per verified obligation,
which authored `@Requires` clauses the proof actually used, and which it didn't:

```
@Requires({ i >= 0 && i < a.length && i != 7 })
static int g(int[] a, int i) { a[i] }

explain ✓ a[i] in bounds
    load-bearing:     @Requires (i >= 0)
    load-bearing:     @Requires (i < a.length)
    not load-bearing: @Requires (i != 7)
```

That last line is the payoff: `i != 7` carries no weight for the bound, so a hygiene-minded reader can drop it.
The verdict comes from **ablation** — remove one clause, re-prove at full strength, and a clause is load-bearing
exactly when its removal breaks the proof. Because it never uses Z3's weaker unsat-core mode it explains the
*whole* fragment (quantifier and FP proofs included), and because it's a pure downstream read-out in a fresh
solver it can't change a verify / refute. It's the most interactive of the three — O(n) re-proofs per obligation,
so it's for the method you're studying, not a suite-wide sweep — and it currently covers the bounds and divide
obligations. An obligation discharged without an authored `@Requires` (an inline guard, invariant, or path fact)
says so, rather than inventing a clause.

It looks past your `@Requires`, too. A proof often leans on a **structural** fact you didn't write — a class
invariant, or a JVM integer bound — and those surface as `also leaned on`. On the ring buffer, the bounds proof
for `values[head]` names the hidden dependency:

```
explain ✓ values[head] in bounds
    load-bearing:     @Requires (head < tail)
    also leaned on:   @Invariant (0 <= head && head <= tail && tail <= values.length)
```

— so you learn the access is safe *because of* the invariant; weaken it and the proof breaks. Only load-bearing
structural facts show (a JVM bound that wasn't needed stays quiet), so the dependency that matters isn't lost in
noise.

The other three are operational rather than directional — `VERIFY_VERBOSE` prints the full diagnostic behind each
one-line pass/fail, `VERIFY_CACHE_STATS` reports the VC-cache hit/miss ratio, and `VERIFY_DUMP_SMT` prints every
solver query as a self-contained SMT-LIB2 benchmark (declarations, assumptions, the *negated* goal, `(check-sat)`)
so you can pipe an obligation to another solver for a second opinion or read the exact formula to debug the
encoding. All three, with the gradle invocations, are in [BUILD.md](BUILD.md).

## Capability discovery (for agents and tooling)

The knobs above tune one diagnostic at a time; for the *whole surface* — "what can this checker prove, and what
does authoring it look like?" — the answer is generated from the test corpus, the single source of truth:

```sh
./gradlew harvest        # -> build/harvest/{catalog.json, corpus.jsonl}
```

- **`catalog.json`** — one record per capability group: a one-line `description`, verify/refute/skip counts, the
  contract `annotations` the group exercises, and a `canonicalVerify` / `canonicalRefute` case id each — the
  "what can it prove" manifest an agent can load in one read.
- **`corpus.jsonl`** — one record per case (~1450): `{id, group, name, outcome, annotations, diagnostic, source}` —
  full authoring examples with their expected outcome, the few-shot corpus for "write me a contract like X".

It's a pure projection of the declared case specs (which CI proves match reality), so it runs in milliseconds
with no solver. The same corpus is browsable as source: one file per capability group under
[`src/test/groovy/cases/`](src/test/groovy/cases) (`G###_<group>.groovy`), each a self-contained list of
annotated good/bad snippets with teaching comments — and the prose inventory is
[CAPABILITIES.md](CAPABILITIES.md), whose group descriptions are the same text `catalog.json` carries.

---

Back to the [README](README.md).
