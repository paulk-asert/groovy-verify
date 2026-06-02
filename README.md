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

# groovy-verify

An SMT-backed verification extension for Groovy, packaged as a standalone
type-checking extension. Annotate code with stock
[`groovy.contracts`](https://github.com/spockframework/groovy-contracts) contracts,
compile a caller under

```groovy
@TypeChecked(extensions = 'verification.VerifyChecker')
```

and Z3 discharges the proof obligations **at compile time** — before the
runtime contract checks would ever fire. Failed proofs surface as ordinary
compile errors with Dafny-style counterexamples.

This started life as the verification spike in the *groovy6-functional* blog
companion repo. It was split out so it can grow on its own; that repo now
consumes it (via a Gradle composite build) rather than vendoring it.

## What's demonstrated

| Capability | Authoring | Status |
|---|---|---|
| Preconditions discharged at call sites | `@Requires` | ✅ |
| Postconditions vs. method body | `@Ensures` | ✅ |
| Loop invariants & termination | `@Invariant` / `@Decreases` | ✅ |
| **Array/list index in bounds** | *(implicit)* | ✅ Phase 1 |
| **Division / modulo by zero** | *(implicit)* | ✅ Phase 1 |
| **Null dereference** | *(implicit)* | ✅ Phase 1 |
| **`xs.size()` / `xs.length` / `xs.isEmpty()`** in contracts | `@Requires`/`@Ensures` | ✅ Phase 4 |
| **`x == null` / `x != null`** nullity in contracts | `@Requires`/`@Ensures` | ✅ Phase 4 |
| **`x.equals(y)`** (numeric `==`) | `@Requires`/`@Ensures` | ✅ Phase 4 |
| **`xs.contains(y)`** (uninterpreted predicate) | `@Requires`/`@Ensures` | ✅ Phase 4 |
| **Cross-boundary nullity/size at call sites** | `@Requires` | ✅ Phase 4 |
| **Value-flow: safety implied by an assignment** | *(implicit)* | ✅ Phase 5 |
| **Loop-fused bounds (obligation under `@Invariant`)** | *(implicit)* | ✅ Phase 5 |
| **Bounded-universal quantifiers over arrays** | `Forall.range(lo, hi) { … a[it] … }` | ✅ Phase 6 |
| **Array contents: read (`select`) & update (`store`)** | `a[i]` in contracts / `a[i] = v` | ✅ Phase 6 |
| **Array update inside a loop (invariant over contents)** | `a[i] = v` in a `@Invariant`-carrying loop | ✅ Phase 6 |
| **Inter-procedural: assume a callee's `@Ensures`** | `int z = f(args)` | ✅ Phase 7 (slice 1) |
| Lemmas by induction, in-place sort, unbounded quantifiers | — | ⏳ later |

Example diagnostic:

```
[Static type checking] - Cannot prove array index in bounds at this access
    obligation: 0 <= i && i < a.size
    counterexample: a.size = 0, i = -1
```

## Building & testing

Requires JDK 25 and the patched local `org.apache.groovy:6.0.0-SNAPSHOT` in
`mavenLocal()` — it carries static `@Ensures` support and the groovy-contracts
fix that allows a parameterised closure (`{ i -> ... }`) nested inside a contract,
which the Phase 6 quantifier syntax relies on.

```sh
./gradlew verify          # compile a battery of good/bad snippets and assert diagnostics
VERIFY_VERBOSE=1 ./gradlew verify   # also print the counterexamples for refuted cases
```

The self-test ([`src/test/groovy/VerifyHarness.groovy`](src/test/groovy/VerifyHarness.groovy))
compiles annotated snippets on the fly and asserts that good ones verify and
bad ones fail with the expected diagnostic.

## The fragment

Verification is sound *within* a deliberately small fragment and **loudly
unsound outside it**: anything the encoder cannot model emits a "skipped"
warning rather than passing silently. The fragment is integer-linear
arithmetic, comparisons, boolean connectives, the size/nullity oracles above,
array contents under Z3's array theory (`a[i]` reads, `a[i] = v` updates) with
bounded-universal quantifiers (`Forall.range`), and — for bodies — straight-line
code, `if`/`else`, single-assignment locals, and a single annotated `while` loop.
See `Encoder` and the roadmap for the exact boundaries.

## Architecture

| File | Role |
|---|---|
| `VerifyChecker` | the `@TypeChecked` extension; call-site, body, loop & implicit checks |
| `Encoder` | Groovy expression → SMT (the fragment lives here) |
| `BodyEncoder` / `LoopEncoder` | path enumeration & symbolic execution for `@Ensures`/loops |
| `PathFacts` | enclosing-`if` path conditions per expression site |
| `ContractExpansionTransform` | captures verbatim contract text + clean body snapshots at CONVERSION |
| `SmtBackend` / `Z3Backend` | the solver seam and its z3-turnkey implementation |
| `Reporter` | OpenJML-style diagnostics with inline counterexamples |

`Encoder` is written against the `SmtSession` interface; `Z3Backend` is the only
concrete binding, so an alternative solver is a drop-in.

## License

Apache-2.0.
