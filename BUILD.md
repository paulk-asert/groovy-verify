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

# Building, testing & consuming

How to build the project, run the verification suite, and depend on it from your
own build. For *what* it proves and *why*, see [README.md](README.md).

## Building & testing

Built using JDK 25. It builds against `org.apache.groovy:6.0.0-SNAPSHOT` from the
[ASF snapshot repository](https://repository.apache.org/content/repositories/snapshots) —
it relies on some fixes due for release in the next Groovy 6 pre-release.

```sh
./gradlew verify                          # compact console runner — one line per case, summary at the end
VERIFY_VERBOSE=1 ./gradlew verify         # also print the counterexamples for refuted cases
VERIFY_CACHE_STATS=1 ./gradlew verify     # also print the in-process VC cache hit / miss ratio
VERIFY_REFUTATION=junit ./gradlew verify  # with VERIFY_VERBOSE: emit each refutation as a runnable repro test
VERIFY_SUGGEST=contract ./gradlew verify  # with VERIFY_VERBOSE: also suggest the @Requires that would discharge each refutation
VERIFY_EXPLAIN=1 ./gradlew verify         # on each verified bounds/divide obligation, show which @Requires clauses the proof leaned on
VERIFY_DUMP_SMT=1 ./gradlew verify        # print every solver query as a self-contained SMT-LIB2 benchmark (pipe to cvc5/z3/yices)

./gradlew test                            # the SAME suite as JUnit 6 dynamic tests (per-case IDE/CI reporting)
./gradlew test -Dverify.only='matrix'     # run just the cases whose "group :: name" contains a substring
```

The cases themselves live in **per-group files** under `src/test/groovy/cases/` (`G###_<group>.groovy`, one
`CASES` list per group plus the group's one-line `DESCRIPTION` — the text `catalog.json` carries — with the
shared header/wrappers in `cases/CaseDsl.groovy`); `VerifyHarness` is the runner that concatenates and judges
them. CI (`.github/workflows/ci.yml`) runs `check` — the suite, the runtime rung
(with its coverage canary), and the doc-drift asserts — plus the two TLC models, on every push/PR; the rung-3
bytecode tools (Lincheck / Fray / jcstress) stay local, per `CONCURRENCY.md`.

Verbose mode prints, for each refuted case, the OpenJML-style diagnostic — the failed obligation, a concrete
counterexample, and a runnable repro — that the compact runner collapses to a one-line pass/fail. `VERIFY_REFUTATION`
chooses **how that repro is rendered** (the formats are mutually exclusive, not additive): `message` — the default —
is the bare `fails on: <call>` you paste and watch throw, while `assert` / `junit` / `spock` render the *same* call
as a **self-checking test** (green *while the bug is live*) *in place of* the bare line. It's a confirmation
bridge, not a keeper: run it to prove the compile-time counterexample is a real runtime failure, then fix the bug
and **flip the test** into a regression (assert the input is now handled, not that it throws) — or delete it. It's transient tooling, like `VERIFY_VERBOSE` (with which it pairs); a verify-only obligation such as
integer overflow — which wraps silently and throws nothing at runtime — is shown as documentary (no exception to
assert).

`VERIFY_SUGGEST=contract` adds the **abduction** direction (the Clousot/CodeContracts angle): for each refuted
*implicit* obligation — bounds, divide-by-zero, or null — it prints the `suggested fix: @Requires({ … })` that
would discharge it, the positive form of the violated check echoed in your own spelling (`.size()` vs `.length`).
It only suggests a guard expressible as a precondition (parameters and fields, never a local or loop variable), so
it pastes verbatim; overflow is excluded on purpose — its sound guard depends on operand signs, and the naive
range-check would evaluate vacuously under wrapping Groovy int arithmetic. A human-reviewed hint, not an auto-fix
(a guarded `if` or a class invariant is often the better home) — and like `VERIFY_REFUTATION`, transient tooling
that pairs with `VERIFY_VERBOSE`.

`VERIFY_EXPLAIN` runs on the obligations that *pass*: for each verified bounds / divide obligation it prints which
authored `@Requires` clauses the proof actually leaned on, found by **ablation** — drop one clause, re-prove at
full strength, and a clause is load-bearing exactly when its removal breaks the proof. Unlike the two above it
doesn't ride on the refutation diagnostic — it emits its own `explain ✓ …` lines on *verified* obligations, so it
doesn't need `VERIFY_VERBOSE`. It's for **interactive proof**, where you're studying one method and don't mind the
O(n) re-proofs per obligation. Because it never uses Z3's weaker unsat-core mode it explains the whole fragment
(quantifier / FP proofs included), and because it's a pure downstream read-out in a fresh solver it can't change a
verify / refute. It also attributes **structural** facts the proof leaned on but you didn't write — a class
invariant or a JVM integer bound — printed as `also leaned on` (only when load-bearing, so an unneeded bound stays
quiet); that surfaces hidden dependencies, like a `values[head]` bound that holds *because of* the buffer's
`@Invariant`. An obligation discharged without any attributable fact (an inline guard or path fact carries it)
says so, rather than inventing a clause.

`VERIFY_DUMP_SMT` is the lowest-level knob: it prints **every** solver query as a self-contained SMT-LIB2
benchmark — declarations, the assumptions, the *negated* goal, and `(check-sat)`. Pipe an obligation to any solver
for a second opinion (`cvc5 q.smt2`, `z3 q.smt2`, `yices-smt2 q.smt2`), or read the exact formula to debug the
encoding. Because the goal is asserted negated, `(check-sat)` returns `unsat` when the obligation **holds** and
`sat` (with a counterexample model) when it's **refuted**; a trailing `; verdict:` comment records what Z3
concluded, for easy cross-checking. It emits every query, not just refutations, so it's for focused study — run it
on a small input (or grep for the dump you want), not as a suite-wide sweep.

The self-test ([`src/test/groovy/VerifyHarness.groovy`](src/test/groovy/VerifyHarness.groovy))
compiles annotated snippets on the fly and asserts that good ones verify and
bad ones fail with the expected diagnostic. The cases are a single compact data list (`CASES`); a
`@TestFactory` turns each into an individually-named, individually-runnable JUnit test (`group :: name`),
and `main` runs the same list as the compact console summary — both share one judging path, so the data
lives in exactly one place. A process-wide VC cache (Phase 34) keys
Z3 results on the canonicalised asserted-set so suite-wide duplicates skip the solver
(measured at ~18 % wall-clock saved on a ~20 % hit rate when the cache landed).

### The other half — concurrency rungs

groovy-verify proves the *thread-local* half of the concurrency-lite examples; the structural half (interleavings,
deadlock, memory-model publication) is left to four separate tasks, each its own source set so the JDK-25 z3 suite is
untouched. They are **not** wired into `check` (different toolchains, heavyweight) — run on demand:

```sh
./gradlew tlcCheck         # rung 2: model-check src/tlc/Buffer.tla (every interleaving) with TLA+ TLC
./gradlew lincheckTest     # rung 3a: Lincheck linearizability on a real SpscBuffer (Java 21 toolchain)
./gradlew frayCheck        # rung 3b: Fray controlled-schedule deadlock check (downloads Corretto JDK 25)
./gradlew jcstressCheck    # rung 3c: jcstress empirical JMM-publication stress on the SpscBuffer (JDK 25)
```

The three-rungs story — compile-time proof, exhaustive model, tested bytecode — is written up in
[CONCURRENCY.md](CONCURRENCY.md).

### The runtime rung — a differential soundness oracle

The *sequential* analogue of the concurrency rungs. `groovy.contracts` annotations are also **runtime
assertions**, so every `ok:true` case is recompiled with the VerifyChecker extension stripped but
groovy-contracts live, then run over an input grid — the contract checks itself. It **falsifies, it cannot
certify**, and (since the corroboration step made it deterministic and the verifier soundness gaps it found are
closed) it is **wired into `check`** — a new confirmed proof-vs-runtime divergence fails the build:

```sh
./gradlew runtimeRung      # cross-validate every proved contract against runtime execution of the same annotation
```

Tier A (scalar/array/string inputs) cross-validates **547 of 570 runnable proofs clean** (500 with an
`@Ensures`/`@Invariant`/`assert` postcondition oracle) as of Phase 168; the rest are Tier B (a structured `@Requires` the grid
can't hit) or Tier C (units/concurrency/info-flow — not grid-executable). The grid is also **seeded from the
spec**: rather than only generate-and-discard, the rung parses the precondition and synthesises an in-domain
*witness* for the simple structural shapes (`s.startsWith("foo")`, `a.length > 5`, `n == -7`, `s in 'A'..'Z'`) —
the jqwik-#486 idea scoped to our own contracts — which pulled 25 cases out of Tier B. The **jakarta** constraints
ride the same path: `@Min(k)` / `@Max(k)` / `@Size(min = k)` become synthetic conjuncts fed to the same seeder, so
an *out-of-grid* bound (`@Min(1_000_000)`, `@Size(min = 20)`) is seeded rather than left in Tier B — unifying the
filter (`filterByAnnotations`) and seed paths on one spec-derivation. A seed is only a candidate (a wrong one is
discarded as a `PreconditionViolation`, just like a grid value), so seeding can never manufacture a divergence —
*provided the seed is type-faithful*: an element-type gate stops a `List<String>` being seeded with an Integer
list (a structural `size() > 0` would accept it, then run with the wrong element semantics — caught, once, as a
confirmed divergence before the gate was added).

A first run taught us the runtime is a *noisy* oracle: groovy-contracts' own postcondition evaluation is
imperfect (it reports `result >= a && result >= b` violated for a `max` that returns correct values). So
**Slice 2 corroborates**: on a postcondition violation it gets the raw return value from a contracts-*disabled*
compile and re-evaluates the spec independently — `false` is a **confirmed** divergence, `true` is a
groovy-contracts quirk (verifier correct, *recovered* as validated). A confirmed divergence not in the
`KNOWN_DIVERGENCES` allowlist **fails the run**; the catalogue currently holds three, each a genuine
verifier-vs-runtime difference, not a logic bug: the `a[i] = i++` / `src[++i]` subscript **evaluation order**
(Groovy evaluates the index *after* the increment; the verifier models Java's snapshot-before), and Groovy's
`[].sum()` being **null not 0** at the empty edge (the verifier models the empty sum as 0). A non-empty
`a.max()`/`a.min()` well-definedness gap is still flagged for review.

## Keeping the docs in sync

Three lints hold the documentation to the code. `./gradlew docLint` prints a human-readable report;
`./gradlew check` runs the same checks as JUnit assertions
([`DocLintTest`](src/test/groovy/DocLintTest.groovy)), so any drift fails the build:

1. **group descriptions** — every test group in `CASES` has a one-line capability description in
   `Harvester.GROUP_DESC` (the text behind the [CAPABILITIES.md](CAPABILITIES.md) rows). Add a group → add a line.
2. **snippets-as-tests** — every fenced `groovy` block in the docs is accounted for (see below).
3. **architecture map** — every `src/main/groovy/verification/*.groovy` engine source is named in
   [ARCHITECTURE.md](ARCHITECTURE.md).

### Documenting an example

Every fenced `groovy` block in `README.md` / `FRAGMENT.md` / `CAPABILITIES.md` / `ARCHITECTURE.md` has one of
four dispositions:

- **Linked** — a `<!-- doclint:case <id> -->` comment immediately before the fence pins the block to a specific
  test, where `<id>` is `slug(group)/slug(name)` (lower-cased, non-alphanumerics → `-`). The check fails if the
  block stops being a substring of that test's source. `./gradlew harvest` (re)writes
  `build/harvest/corpus.jsonl`, which lists every id. **Comments are part of the check**: a teaching comment shown
  in the doc must also live in the test's `CASES` source — the test is the single source of truth, so annotate the
  example *there*. (Gotcha: a `//` comment can't trail a continuation operator inside a multi-line contract — it
  breaks Groovy's line-continuation when the snippet is compiled — so park such a note on the closing line.)
- **Exempt** — `<!-- doclint:ignore <reason> -->` marks an illustration with no 1:1 test (a polished README
  variant, a doc-only fragment). The reason is free text; name what it illustrates.
- **Blockquoted** — a `>`-quoted `groovy` block is exposition (desugaring / "generated-code" asides) and is
  auto-exempt; no marker needed.
- **Unmarked** — a weak fallback that only checks the block is a verbatim substring of *some* case. Prefer an
  explicit marker.

So: add an example, then **link it** with `doclint:case` if it mirrors a test, or **exempt it** with
`doclint:ignore <reason>` if it's illustrative — and run `./gradlew docLint` to confirm it's accounted for.

## Using it in your own build

It isn't on Maven Central yet, but you don't need to wait for that — there are three
ways to consume `io.github.paulk-asert:groovy-verify:0.1.0-SNAPSHOT`:

- **Local install.** `./gradlew publishToMavenLocal` drops the jar into your `~/.m2`;
  then add `mavenLocal()` and the dependency to any Gradle/Maven project.
- **Composite build (source dependency).** Clone this repo alongside yours and add
  `includeBuild('../groovy-verify')` to your `settings.gradle` — Gradle substitutes the
  dependency with this project's output, so changes here are picked up without a publish.
  (The companion *groovy6-functional* repo consumes it this way.)
- **JitPack.** Because the build is self-contained (ASF snapshot, no local patch), JitPack
  can build it straight from a GitHub tag/commit — add the JitPack repo and depend on
  `com.github.<owner>:groovy-verify:<tag>`, no publishing step on your side.

Either way the consumer compiles under `@TypeChecked(extensions = 'verification.VerifyChecker')`;
the artifact carries Z3 (via z3-turnkey, native libs bundled) on the compile classpath.
