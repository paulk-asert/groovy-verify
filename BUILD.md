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
./gradlew verify                       # compact console runner — one line per case, summary at the end
VERIFY_VERBOSE=1 ./gradlew verify      # also print the counterexamples for refuted cases
VERIFY_CACHE_STATS=1 ./gradlew verify  # also print the in-process VC cache hit / miss ratio

./gradlew test                         # the SAME suite as JUnit 5 dynamic tests (per-case IDE/CI reporting)
./gradlew test -Dverify.only='matrix'  # run just the cases whose "group :: name" contains a substring
```

The self-test ([`src/test/groovy/VerifyHarness.groovy`](src/test/groovy/VerifyHarness.groovy))
compiles annotated snippets on the fly and asserts that good ones verify and
bad ones fail with the expected diagnostic. The cases are a single compact data list (`CASES`); a
`@TestFactory` turns each into an individually-named, individually-runnable JUnit test (`group :: name`),
and `main` runs the same list as the compact console summary — both share one judging path, so the data
lives in exactly one place. A process-wide VC cache (Phase 34) keys
Z3 results on the canonicalised asserted-set so suite-wide duplicates skip the solver
(measured at ~18 % wall-clock saved on a ~20 % hit rate when the cache landed).

Doc-drift lints keep the documentation honest against the suite (`./gradlew docLint` for the
human-readable report; the same checks run as JUnit assertions in `./gradlew check`):
every code block in the docs is either linked to a specific test (`<!-- doclint:case ID -->`,
which fails the build if the block and its test diverge), exempted as an illustration
(`<!-- doclint:ignore … -->`), or a verbatim substring of some case.

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
