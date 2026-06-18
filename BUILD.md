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

./gradlew test                            # the SAME suite as JUnit 5 dynamic tests (per-case IDE/CI reporting)
./gradlew test -Dverify.only='matrix'     # run just the cases whose "group :: name" contains a substring
```

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
deadlock) is left to three separate tasks, each its own source set so the JDK-25 z3 suite is untouched. They are
**not** wired into `check` (different toolchains, heavyweight) — run on demand:

```sh
./gradlew tlcCheck         # rung 2: model-check docs/Buffer.tla (every interleaving) with TLA+ TLC
./gradlew concurrentTest   # rung 3a: Lincheck linearizability on a real SpscBuffer (Java 21 toolchain)
./gradlew frayCheck        # rung 3b: Fray controlled-schedule deadlock check (downloads Corretto JDK 25)
```

The three-rungs story — compile-time proof, exhaustive model, tested bytecode — is written up in
[docs/README.md](docs/README.md).

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
