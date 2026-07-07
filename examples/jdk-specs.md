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

# JDK specs & exceptional contracts

Contracts stop at the edge of your own source — until they don't. This gallery works through the
**external-specification registry**: JML's `.jml`-file idea in the project's own dialect, where a
library class you don't own is specified by an ordinary Groovy *skeleton* — the class re-declared
with the same `groovy.contracts` annotations user code carries, plus `@Pure` and `@ThrowsIf` arms,
and empty bodies. Skeletons live at the classpath resource `META-INF/groovy-verify/specs/<fqn>.groovy`
(a `VERIFY_SPECS` directory overrides, for local iteration), are discovered lazily and parsed
AST-only — never compiled, never executed — and every one is **trusted by definition**: nobody proves
the JDK's bodies. That is why every consumption is recorded in the trusted-spec ledger and why the
runtime rung cross-checks the specs against the live JDK.

## The skeleton, and the total spec

The shipped `java.lang.Math` skeleton opens with the JML community's running example — and adopts the
OpenJML corpus's better idea, a **total** spec: no precondition, the wrap behaviour at the one
unrepresentable point *stated* rather than excluded.

<!-- doclint:ignore spec skeleton (a shipped resource, not a corpus case) -->
```groovy
// META-INF/groovy-verify/specs/java.lang.Math.groovy
package java.lang

class Math {
    @Pure
    @Ensures({ (a >= 0 ==> result == a) &&
               (a < 0 && a != Integer.MIN_VALUE ==> result == -a) &&
               (a == Integer.MIN_VALUE ==> result == Integer.MIN_VALUE) })
    static int abs(int a) {}
    // … negateExact, floorDiv, max, min, floorMod, addExact, and the long overloads
}
```

A caller consumes it like any contracted callee — the spec's `@Ensures` is assumed for the call's
result, and the caller's own guard does the rest:

<!-- doclint:case p215-external-specs/math-abs-total-spec-consumed-ensures-proves-the-caller -->
```groovy
class C {
    @Requires({ a != Integer.MIN_VALUE })
    @Ensures({ result >= 0 })
    static int f(int a) {
        return Math.abs(a)
    }
}
```

Drop the guard and the total spec shows its teeth — the classic abs bug, `abs(x) >= 0`, is simply
**false** at `MIN_VALUE`, and the ensures refutes it with that exact witness:

<!-- doclint:case p215-external-specs/the-abs-wrap-bug-unguarded-result-0-refutes-at-min-value -->
```groovy
class C {
    @Ensures({ result >= 0 })
    static int f(int a) {
        return Math.abs(a)
    }
}
```

```
Cannot prove postcondition of f holds on this return path
    ensured: (result >= 0)
    counterexample: a = -2147483648
```

## The three contract styles, side by side

The skeletons deliberately exhibit the JDK's three exceptional-contract kinds as a triptych. `abs` is
the *total spec* above (every input defined, the edge stated). `absExact` and `negateExact` are the
*exceptional contract* — the edge is a **defined throw**, `@ThrowsIf`'s true iff (`negateExact` throws
`ArithmeticException` at exactly the one unrepresentable point). And `Arrays.binarySearch` carries the
JDK's rarest kind, a **true precondition**: the javadoc's *"the result is undefined"* unless sorted is
what `@Requires` actually means — spelled with the reversal-immune sortedness idiom, it becomes an
obligation at every call site:

<!-- doclint:case p215-external-specs/binarysearch-requires-sorted-unsorted-call-site-refutes -->
```groovy
class C {
    static int find(int[] a, int key) {
        return java.util.Arrays.binarySearch(a, key)
    }
}
```

```
Cannot prove precondition of binarySearch at this call site
    required: (a != null && a.indices.every { it == 0 || a[it - 1] <= a[it] })
```

A caller that *knows* sortedness (its own `@Requires` carrying the same idiom) discharges it.

## Specs compose — clamp from nested max/min

`Math.max` and `Math.min` ship as total specs, and spec calls nest: whichever function the inner call
denotes, the outer spec consumes its result. The classic clamp proves its range property with no body
reasoning beyond the two specs:

<!-- doclint:case p217-jdk-specs/clamp-nested-max-min-spec-composition-proves-the-range -->
```groovy
class C {
    @Requires({ lo <= hi })
    @Ensures({ lo <= result && result <= hi })
    static int clamp(int x, int lo, int hi) {
        return Math.max(lo, Math.min(x, hi))
    }
}
```

## `@Pure` admission — specs as contract vocabulary

A `@Pure`-marked spec method is usable *inside* contract expressions: the call becomes an
uninterpreted function whose defining axiom is the spec's own guarded contract, so your `@Ensures`
can say `Math.abs` instead of hand-expanding it into ternaries:

<!-- doclint:case p218-pure-admission/math-abs-as-contract-vocabulary-ensures-proves -->
```groovy
class C {
    @Requires({ a != Integer.MIN_VALUE })
    @Ensures({ result == Math.abs(a) })
    static int dist(int a) {
        return a >= 0 ? a : -a
    }
}
```

The axiom is real reasoning material, not decoration — here the sign fact `x > 0` is *derived* from
`Integer.signum`'s spec, never stated:

<!-- doclint:case p218-pure-admission/signum-in-requires-sign-fact-derived-from-the-axiom -->
```groovy
class C {
    @Requires({ Integer.signum(x) == 1 })
    @Ensures({ result > 0 })
    static int f(int x) {
        return x
    }
}
```

## Instance methods — range facts on immutable value getters

The registry answers for instance calls too. The v1 rule keeping it sound: a consumed instance
contract must be *receiver-independent* (facts about `result` and the arguments only) — which makes
`java.time`'s value getters the natural population: `getMonthValue()` is 1–12 on *every* receiver.
Two such facts compose arithmetically:

<!-- doclint:case p220-instance-specs/minute-of-day-two-instance-facts-compose-arithmetically -->
```groovy
class C {
    @Requires({ t != null })
    @Ensures({ 0 <= result && result < 1440 })
    static int minuteOfDay(java.time.LocalTime t) {
        int h = t.getHour()
        int m = t.getMinute()
        return h * 60 + m
    }
}
```

(The `t != null` guard is not politeness — the receiver dereference is a proof obligation the nullity
discipline enforces before any range fact flows.)

Receiver-*state* contracts land via substitution: `String#indexOf(int)` ships
`@Ensures({ result >= -1 && result < length() })`, and at each call site `length()` is rewritten onto
the actual receiver. That makes the most idiomatic string bug in the book — indexOf without the
found-check — a compile-time story. With the check, the *native* `charAt` bounds obligation is
discharged by the *registry* fact:

<!-- doclint:case p221-receiver-state-specs/indexof-then-charat-a-native-bounds-obligation-discharged-by-a-registry-fact -->
```groovy
class C {
    @Requires({ s != null && s.length() > 0 })
    static char findOrLast(String s) {
        int i = s.indexOf(120)
        if (i >= 0) {
            return s.charAt(i)
        }
        return s.charAt(s.length() - 1)
    }
}
```

Drop the `if (i >= 0)` and the `-1` sentinel sails into `charAt` — refuted, with the sentinel as
counterexample.

## Survival facts — the call you moved past did not throw

An *executed* call the program moved past didn't throw, so no `@ThrowsIf` arm's condition held — the
contrapositive of must-throw, asserted on the continuation. The JDK's own guard method becomes a
proof device: `checkIndex` survived, therefore the index is in range, therefore the array access is
safe —

<!-- doclint:case p222-signals-arms/checkindex-then-index-the-jdk-guard-method-proves-the-array-access -->
```groovy
class C {
    @Requires({ a != null })
    static int f(int[] a, int i) {
        int j = java.util.Objects.checkIndex(i, a.length)
        return a[j]
    }
}
```

## Catch-entry facts — the handler knows why it was entered

The converse direction: entering a `catch` means some try-block source threw the caught type. When
every source is arm-characterised, the disjunction of matching arm conditions is a fact at catch
entry — the handler *knows the divisor was zero*:

<!-- doclint:case p223-catch-reachability/catch-arithmeticexception-knows-the-divisor-was-zero -->
```groovy
class C {
    @Ensures({ result >= 0 })
    static int f(int a, int b) {
        try {
            int q = Math.floorDiv(a, b)
            return q >= 0 ? q : 0
        } catch (ArithmeticException e) {
            return b == 0 ? 0 : -1
        }
    }
}
```

This consumes the only-when (JML-`signals`) direction of the iff, so it is heavily gated: matching
arms must be fully `exhaustive`, every call in the try must be arm-characterised (the arm *types*
read as the spec's complete throw-type story — the implicit `signals_only` of a skeleton), native
throw sources of the caught type decline, and the conditions must be prefix-independent. Each gate is
pinned by a refuting twin in the corpus.

`@ThrowsIf` itself comes in two strengths: the default is an **iff** (the listed conditions are the
*only* reasons the exception is thrown), while `exhaustive = false` is the one-directional
JML-`signals` form — sufficient but not the whole story — which is what finally admitted
`Integer.parseInt` (`{ s == null }` is a true sufficient condition; the full "malformed or out of
range" is outside the fragment, and a sloppy iff would have been *wrong*, which the rung's grid
inputs would have flagged).

## Collections — factories, and the List twin of binarySearch

The `java.util.Collections` skeleton covers the static factory/query surface. Its `binarySearch` is
the List twin of the `Arrays` true-precondition — and its discharge is machinery, not just a spec:
the caller's own sortedness reaches the formal because element *contents* are tied across the call
boundary, not merely sizes:

<!-- doclint:case p225-collections-specs/binarysearch-obligation-discharged-element-contents-tied-across-the-boundary -->
```groovy
class C {
    @Requires({ xs != null && xs.indices.every { it == 0 || xs[it - 1] <= xs[it] } })
    static int find(List<Integer> xs, int key) {
        return java.util.Collections.binarySearch(xs, key)
    }
}
```

The factories carry the facts callers actually use — non-null results and exact sizes — landing
directly on the assigned local, so downstream dereferences and size claims discharge:

<!-- doclint:case p225-collections-specs/ncopies-guarded-size-fact-object-wildcard-typed-lookup -->
```groovy
class C {
    @Requires({ n >= 0 })
    @Ensures({ result == n })
    static int f(int n) {
        List l = java.util.Collections.nCopies(n, 'x')
        return l.size()
    }
}
```

And `Long.parseLong` joins `Integer.parseInt` as a one-directional arm whose survival contrapositive
does real work — the call returned, so the string wasn't null:

<!-- doclint:case p225-collections-specs/long-parselong-survival-proves-s-non-null-signals-arm -->
```groovy
class C {
    static int f(String s) {
        long v = Long.parseLong(s)
        return s.length()
    }
}
```

## Honest partiality — the specs refuse to over-claim

The `Character` predicates are Unicode-aware, so their specs are **partial by design**: each fact
holds over the ASCII range it names, and everything else stays opaque. Claim more and the spec
refuses — the unguarded "nothing is a digit" refutes with an uncovered code point, because the
skeleton never said anything about `'{'`, let alone Arabic-Indic digits:

<!-- doclint:case p217-jdk-specs/unicode-honesty-unguarded-isdigit-claim-refutes-partial-spec-stays-partial -->
```groovy
class C {
    @Ensures({ !result })
    static boolean f(char c) {
        return Character.isDigit(c)
    }
}
```

That refusal is the registry's one absolute rule made visible: **only provably-true contracts ship**
— partial truths stay partial, wrap behaviour is guarded (`Long.sum`'s ensures holds only in the
non-overflowing range, because the runtime wraps), and anything a spec doesn't state, the verifier
doesn't invent. Trust that is visible is trust that gets reviewed: the harness prints the ledger
beside its perf line, DocLint's trusted inventory lints every shipped skeleton, and the runtime rung
grid-tests the proofs — with its spec-throw category type-checking any runtime throw against the very
arms that predicted it.
