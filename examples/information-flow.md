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

# Information flow — taint tracking, generalized


Compile-time **taint analysis** — Ballerina's `@tainted`/`@untainted`, the OWASP-style trackers — labels data and
refuses to let it reach a sink it shouldn't, at zero runtime cost. The same idea, on this engine, is one
*instance* of a more general construction: a security **lattice** (a proved `enum` of levels) plus a `@Label` on
each source and sink. The verifier discharges the **noninterference** obligation —
`leq( join(ΓE(e), PC), L(sink) )` — over the class's *own* lattice, by the same Z3 backend that proves the
contracts. No new solver theory; the obligation is just a lattice formula. (The Γ/lattice encoding follows Smith,
[*A Dafny-based approach to thread-local information flow analysis*](https://staff.itee.uq.edu.au/smith/recent/dafny.pdf),
§III. The paper's concurrent rely/guarantee story is *reconstructed* on the per-thread rely-step model — see the
rely/guarantee section — but the underlying concurrency/atomicity soundness, that threads truly interleave at the
assumed grain, stays a deliberate non-goal.)

A two-point `Low ⊑ High` is the taint lattice — read `High` as "secret" for confidentiality, or "untrusted" for
integrity; they're duals. **The leak that matters most is into a sink** — a value reaching a parameter classified
below it. This is the injection shape, and it refuses to compile:

<!-- doclint:ignore README illustration: cross-class info-flow leak (Service/Audit) -->
```groovy
class Service {
    enum L { Low, High }
    static boolean leq(L a, L b) { a == L.Low || b == L.High }
    static L join(L a, L b) { leq(a, b) ? b : a }

    static void handle(@Label('High') int secret) {
        Audit.log(secret)                                       // REFUTED — a secret reaches a public sink
    }
}

class Audit {                                                   // the sink, in its own class
    static void log(@Label('Low') int x) { /* … to a public channel … */ }
}
```

```
[Static type checking] - Possible information leak: 'secret' may carry data above the 'Low' classification of parameter 'x' of log
    obligation: leq(level(secret), Low)
```

The sink lives in another class; `Service` carries the lattice and the labelled source. Laundering through a local
doesn't help — `int t = secret; Audit.log(t)` refutes just the same. The label rides the *value*, not the
variable name.

**The part most taint checkers skip: implicit flows.** A secret can leak *without ever being assigned to the
sink* — through control flow. Branching on a secret raises a program-counter label inside both arms, so anything
assigned (or any sink called) there is tainted by *which branch ran*:

<!-- doclint:case pl1-infoflow/1c-implicit-flow-assign-under-secret-branch-refuted -->
```groovy
    @Label('Low')
    static int implicit(@Label('High') boolean secret,
                        @Label('Low') int a, @Label('Low') int b) {
        int t = a
        if (secret) t = a else t = b                             // t now reveals `secret`…
        return t                                                 // REFUTED — though only Low values are ever assigned
    }
```

Neither `a` nor `b` is secret, yet `t`'s value tells you `secret` — and the verifier refuses it. **And it
doesn't cry wolf:** the PC is *scoped* to the branch, so a low value that doesn't depend on the secret is still
fine afterwards:

<!-- doclint:ignore README illustration: PC-scoped info-flow (untouched value) -->
```groovy
    @Label('Low')
    static int scoped(@Label('High') boolean secret, @Label('Low') int pub) {
        int t = pub
        if (secret) { int unused = pub }                         // branch on a secret, but t is untouched
        return t                                                 // VERIFIED — t never depended on it
    }
```

That precision is the whole game: a tool that rejects every branch near a secret is useless. It falls out of a
syntax-directed walk that pushes the PC entering a branch and pops it on exit, threading a `Γ` environment (value
→ level) through assignments, returns, and call arguments alike.

**Beyond taint entirely: a classification that depends on state.** A taint label is fixed — a value is tainted or
it isn't. Here a value's *classification* can be a function of program state, reasoned about path-sensitively.
Declare `data` secret *unless authenticated*:

<!-- doclint:case pl1-infoflow/value-dependent-release-under-the-guard-verifies -->
```groovy
    static L classifyData(boolean authed) { authed ? L.Low : L.High }   // value-dependent classification

    @Label('Low')
    static int get(boolean authed, @Label(by = 'classifyData') int data,
                   @Label('Low') int fallback) {
        if (authed) return data                                  // VERIFIED — under the check, L(data) == Low
        return fallback
    }
```

Releasing `data` *under* the authentication check verifies; releasing it unguarded — `return data` with no
`if (authed)` — refutes, with the unauthenticated state (`authed = false`) as the counterexample, and a guard on
an unrelated condition doesn't help. No taint analysis can express "secret only sometimes"; here it's just a
classification function the SMT backend evaluates under the path conditions.

And the dual bug — changing the *control* variable to make the classification public while the data is still
secret — is caught too:

<!-- doclint:case pl1-infoflow/secure-update-flipping-the-flag-public-refuted -->
```groovy
    static void declassify(boolean authed, @Label(by = 'classifyData') int data) {
        authed = true                                            // REFUTED — L(data) becomes Low, but data may hold High
    }
```

Flipping the flag the other way (`authed = false`, *raising* the classification) verifies. That's the §III-A
secure-update rule: assigning a control variable mustn't strand a value it controls above its new level.

Sometimes a release is *intended* — a password checker must reveal whether the guess was right. That's
**declassification**, and here it's an explicit, greppable act rather than an invisible cast:

<!-- doclint:case pl1-infoflow/declassify-password-check-releases-the-equality-bit-verifies -->
```groovy
    @Label('Low')
    static boolean check(@Label('High') int password, @Label('Low') int guess) {
        return Declassify.to('Low', password == guess)           // release one bit — verified
    }
```

Drop the `Declassify.to` and the same method refutes (`password == guess` carries `High`); release the secret
itself (`Declassify.to('Low', password)`) and a reviewer sees exactly what escaped. Every release point is in the
source, by name.

Where it stops, it says so. Straight-line code, `if`/`else`, and `while`/`for` loops (with an inferred
Γ-invariant), sinks resolved both same-class and cross-class within the compilation unit; an unlabelled source, a
`for`-each over a collection, or a construct outside the fragment skips loudly. The whole *sequential* fragment of
Smith §III is in place; the named next steps are the refinements — sinks in a **precompiled/imported** class,
classification over a field, array element labels, and the predicate-gated (two-state) form of declassification.

