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

# Roadmap

`groovy-verify` proves a point: an SMT-backed type-checking extension can
produce Dafny-shaped verification diagnostics for Groovy today, with no
language change. Explicit contracts (`@Requires`, `@Ensures`, `@Invariant`,
`@Decreases`) and the implicit preconditions every program carries (array
bounds, division, null) are discharged by Z3 at the caller's compile time,
before any runtime check would fire. This document records what is in place and
where it goes next.

Each item slots in as new encoder cases, new verification-condition sites, or
new annotation kinds, without restructuring the engine. The ordering is by
value-to-cost — how much a capability is worth to someone writing real Groovy,
against how much work and solver risk it adds. The increments are not strictly
dependent on each other, but the later ones assume the encoder fragment of the
earlier ones.

Verification is sound *within* a deliberately small fragment and **loudly
unsound outside it**: anything the encoder cannot model emits a "skipped"
diagnostic rather than passing silently. That honesty is a design choice, not a
limitation to be apologised for — see [Non-goals](#non-goals).

---

## Phase 1 — Safety: array bounds, division by zero, null  *(shipped)*

**The "every developer recognises this" win.** No annotation surface; these are
*implicit preconditions* that fire automatically on indexing, division, and
dereference. OpenJML splits them into `UndefinedNegativeIndex`,
`UndefinedTooLargeIndex`, `UndefinedZeroDivision`, `UndefinedNullDeReference`;
the same taxonomy applies here.

**How it works (shipped):**

- `VerifyChecker.verifyImplicitObligations` runs in `afterVisitMethod` for every
  method in the annotated scope. It walks the *clean body snapshot*
  `ContractExpansionTransform` takes at CONVERSION — not `method.getCode()` —
  so groovy-contracts' injected runtime asserts are never mistaken for the
  author's dereferences. (The snapshot is now taken for every method, not just
  `@Ensures`/loop ones.)
- An `ObligationCollector` (a `ClassCodeVisitorSupport`) gathers three site
  kinds: array/list **subscripts** (`a[i]`), **division/modulo** (`a / b`,
  `a % b`), and instance-method **dereferences** on a named parameter/local
  receiver. Static calls, `this`, and calls on non-variable receivers are
  skipped — they are provably non-null or out of reach.
- Each site is discharged by the same machinery as a call-site precondition:
  assume the method's own `@Requires` and the enclosing path facts, assert the
  *negation* of the obligation, and ask Z3 whether that is satisfiable. A model
  is a counterexample.
  - index `a[i]` → `0 <= i && i < a.size`
  - division `a / b` / `a % b` → `b != 0`
  - dereference `r.m(...)` → `r != null`
- A **size oracle** mints an integer constant `<recv>.size >= 0` on demand; a
  **nullity oracle** mints a boolean per reference. The size constant is shared
  with the `.length`/`.size()` contract syntax of [Phase 4](#phase-4--richer-fragment-in-requiresensures-shipped),
  so a contract that bounds a collection's size and an indexing check inside the
  body agree on the same symbol.

**Diagnostic:**

```
Possible IndexOutOfBoundsException: index may be out of bounds
    obligation: 0 <= i && i < a.size()
    counterexample: a.size() = 0, i = -1
```

```groovy
@TypeChecked(extensions = 'verification.VerifyChecker')
class Demo {
    static int at(int[] a, int i) {
        if (i >= 0 && i < a.length) return a[i]   // verified
        return -1
    }
    static int bad(int[] a, int i) {
        a[i]                                       // REFUTED: i may be < 0 or >= a.size
    }
}
```

**Path-sensitivity, and the value-flow that followed.** The implicit checks are
path-sensitive (they honour enclosing `if`s). Originally *value-flow-blind* — local
assignments untracked, loop obligations checked without the `@Invariant` — both gaps
were closed by [Phase 5](#phase-5--value-flow--loop-fused-safety-obligations-shipped).
Counterexamples report integer values; nullity is boolean, so a null-dereference
refutation names the obligation but not a concrete value.

---

## Phase 2 — Postconditions: `@Ensures`  *(shipped)*

**The "now we're verifying methods produce the right answer" win.** The first
capability that requires symbolic execution of the method body, not just the
call site — the checker becomes *per-method*, not only *per-call*.

**How it works:**

- No new annotation. Stock `@groovy.contracts.Ensures({ ...result... })`;
  groovy-contracts generates the runtime postcondition check (including on
  *static* methods) and owns the `result`/`old` names, so the type checker never
  trips over them.
- `ContractExpansionTransform` — a global transform at CONVERSION — reads the
  contract closure while it is still a `ClosureExpression`, captures its verbatim
  text with power-assert's `SourceText`, and stashes it on a RUNTIME
  `@ContractSource`. `VerifyChecker` reads that back and re-parses it — the
  built-in annotation itself retains only a `Class` reference to a generated
  closure, so the source would otherwise be gone by compile time.
- `BodyEncoder` enumerates the body's straight-line execution paths (forking at
  each `if`, threading a per-path step list, so no join-point merge is ever
  needed). For each path it emits the VC
  `path_condition ∧ ¬(postcondition[result ↦ returned_expr])` and discharges it.

**One non-obvious interaction.** groovy-contracts rewrites the method body *in
place* at INSTRUCTION_SELECTION — prepending an `old` map, wrapping in
try/catch, appending the postcondition assert — before the type-checking
extension runs. So the verifier must analyse the **clean CONVERSION snapshot**,
not `method.getCode()`.

```groovy
@Ensures({ result >= a && result >= b })
static int max(int a, int b) { if (a > b) a else b }       // verified

@Ensures({ result >= a && result >= b })
static int maxBuggy(int a, int b) { if (a > b) b else a }  // REFUTED: a=1, b=0
```

The encoder's scope is straight-line + if/else + single return. Symbolic
execution grows tendrils (`break`/`continue`/mid-method `return`, exceptions,
finally blocks), so everything else is a "skipped postcondition" diagnostic.

---

## Phase 3 — Loops: `@Invariant` + `@Decreases`  *(shipped)*

**The classical inductive proof.** Three obligations per loop, plus a fourth for
termination:

1. **Establishment** — invariant holds on first entry.
2. **Preservation** — invariant ∧ guard ∧ one body iteration ⇒ invariant still holds.
3. **Use** — invariant ∧ ¬guard ⇒ whatever VC fires after the loop (e.g. the postcondition).
4. **Progress** (`@Decreases`) — invariant ∧ guard ∧ body ⇒ the measure strictly decreases and stays ≥ 0.

**How it works:**

- No new annotation. groovy-contracts already ships
  `@groovy.contracts.Invariant`/`@groovy.contracts.Decreases` *on loop
  statements*; its transforms inject the runtime checks. We capture their text
  the same way as `@Requires`/`@Ensures` and leave the closures intact.
- `LoopEncoder` does havoc-and-assume symbolic execution: a fresh `Encoder` per
  verification condition gives havoc-by-default (any name a context never binds
  is an unconstrained fresh value), an assignment is a re-bind (so SSA renaming
  falls out for free), and the invariant is assumed, the body executed once, and
  the invariant re-asserted.
- A *deeper* CONVERSION snapshot preserves the loop subtree — guard, clean body,
  and the intact `@Invariant`/`@Decreases` closures — because groovy-contracts
  mutates the loop's *inner* body in place.

```groovy
@Requires({ n >= 0 })
@Ensures({ result == n })
static int countUp(int n) {
    int i = 0
    @Invariant({ 0 <= i && i <= n })
    @Decreases({ n - i })
    while (i < n) { i = i + 1 }
    return i
}
```

All four VCs discharge clean; mutate an increment or the invariant and the
diagnostic names exactly which obligation fails. **Caveat:** the havoc set is
currently *every* in-scope variable rather than the loop's live-modified set —
sound but loose, so non-trivial loops will draw more "could not decide" answers
than a tighter modified-set analysis would. Loop contracts are never read across
a module boundary, so the rebuild discipline below does not apply to them.

---

## Phase 4 — Richer fragment in `@Requires`/`@Ensures`  *(shipped)*

**The extensions that unlock most contracts people actually want to write.**
Each is a small `Encoder` addition; the work was choosing the right encoding.

- **`xs.size()` / `xs.length`** for `List`/`String`/arrays — the size oracle from
  Phase 1, now exposed in contract syntax and sharing its `<recv>.size` constant.
- **`xs.isEmpty()`** as sugar for `xs.size() == 0`.
- **`x == null` / `x != null`** — first-class nullity via the nullity oracle,
  detected at the comparison so `null` need not itself be a fragment value.
- **`x.equals(y)`** for numeric types — the method form of `x == y`.
- **`xs.contains(y)`** — originally an *uninterpreted predicate* `contains$xs : Int -> Bool`
  (sound, `contains(y)` assumed entails `contains(y)` proved, but no membership reasoning).
  **Upgraded in Phase 9** to precise membership `∃ i. 0 <= i < xs.size ∧ xs[i] == y` over the
  modelled contents, once the existential `any` landed — so `contains` now relates to actual
  element values.

The seam grew `SmtBackend.boolVar` (nullity) here; `contains` first rode an
`uninterpretedPred`, since removed when Phase 9 re-modelled it as a precise
existential over the array contents.

**Cross-boundary oracles (shipped).** Inside a unit these all work: a method's
own `@Requires({ s != null })` is assumed when checking its body, and an
`@Ensures` referring to `xs.size()` is checked against the body. At a *call* site
the formal↔actual binding now ties the **size and nullity oracles** as well as
the integer value: when the actual is a named reference and the callee's contract
references its size or nullity, the formal's oracle is asserted equal to the
actual's. Two changes make this land cleanly:

- The oracle is tied **only when the contract actually mints it** on the formal
  (`Encoder.hasSizeOracle`/`hasNullityOracle`), so a purely-nullity precondition
  doesn't fabricate an `xs.size` term in the counterexample.
- A call site now also **assumes the enclosing method's own `@Requires`**, mirror-
  ing what the implicit-obligation checks already did via `assumeContext`. A
  precondition is a given throughout the body, so a method declared
  `@Requires({ s != null }) m(String s) { callee(s) }` can discharge `callee`'s
  `@Requires({ x != null })` from its own contract — not only from an `if`-guard.

So a caller proving a callee's `@Requires({ x != null })` or
`@Requires({ xs.size() > 0 })` across the boundary now verifies, from either a
guard or the caller's own contract. **Residual cosmetic limit:** a refuted
reference-typed call site still lists the formal's meaningless integer shadow
(`s = 0`) alongside the meaningful oracle value — the integer constant minted for
every formal so numeric counterexamples read `x = -1`. Type-aware counterexample
filtering would suppress it; small, not yet wired.

---

## Phase 5 — Value-flow & loop-fused safety obligations  *(shipped)*

**Completing Phase 1 — the everyday wins it used to miss.** The implicit safety
checks (array bounds, division, null) were path-sensitive but *value-flow-blind*:
each obligation was discharged in a fresh `Encoder` assuming only the method's
`@Requires` and the enclosing `if` facts, so every local was havoc-by-default and
the loop invariant was never in scope. Two recognisable patterns therefore failed
even though they are obviously safe:

- **(a) safety from an assignment, not a guard** — `int j = 3; a[j]` under
  `@Requires({ a.length > 5 })` was refuted, because `j = 3` was never threaded.
- **(b) the counted loop** — `while (i < n) { ... a[i] ... }` was refuted, because
  the bounds obligation at `a[i]` was checked without the loop's `@Invariant`.

Both now verify. The work stayed entirely inside the QF_LIA + oracle fragment —
no new theory, no quantifiers — the opposite of
[Phase 6](#phase-6--quantifiers-shipped)'s trigger cliff.

**How it works:**

- **5a — value-flow in straight-line / `if` bodies.** `verifyImplicitObligations`
  first tries a lenient walk of the body (`collectVfObligations`) that snapshots,
  for each obligation, the single-assignment bindings and `if`-guards in effect
  where it is *evaluated* — forking at each `if`, with the condition's own
  obligations evaluated before the branch. Each obligation is then discharged in
  a fresh session under `@Requires` + those reaching assignments (asserted as
  equalities) + those guards. Anything outside the fragment (a loop, a
  re-assignment, an unsupported statement) throws, and the original path-fact-only
  **havoc pass** runs as a sound fallback. *Guarded derived locals already
  verified before* — `if (j >= 0 && j < a.length) a[j]` works because the guard
  and the obligation share the same `j` handle — so 5a's marginal win is the
  *assignment-implied* facts. Collection is also **short-circuit-aware**: in `p && q` the
  right operand's obligations are discharged under `p`, in `p || q` under `not p`, and a
  `c ? t : e` branch under `c`/`not c` — so `if (i > 0 && a[i] < a[i - 1])` proves `a[i - 1]`
  in bounds *from the `i > 0` to its left*, no nested-`if` workaround. And an array-element
  store (`a[i] = v`) no longer bails to the havoc fallback: its contents don't bear on the
  bounds/div/null obligations, so the pass collects the index and rhs obligations and carries
  on (this is what lets a recursive `insert` that swaps stay on the value-flow path).
- **5b — loop-fused bounds.** For a method whose body is an annotated loop, the
  obligations are discharged with the invariant in scope instead of via the havoc
  pass (`verifyLoopObligations`): prefix sites see `@Requires` + the straight-line
  prefix store; the guard and body sites additionally assume the invariant (and,
  in the body, the guard); suffix sites assume the invariant ∧ ¬guard. Each region
  is threaded with `LoopEncoder.symExec` (bind/SSA semantics — correct even when
  the counter is re-assigned). It **only** helps loops carrying an `@Invariant`
  strong enough to bound the index; otherwise it is an honest "could not decide".
- **Lenient `symExec`.** So that a body which *reads* the array (`s = s + a[i]`,
  outside the int fragment) does not abort the whole loop proof, an assignment
  with an unmodelable right-hand side now **havocs** its target (`Encoder.havoc`)
  rather than raising. Sound: havoc only ever makes the invariant/obligation VCs
  harder. This also retires a class of spurious "skipped loop" diagnostics.

```groovy
@Requires({ 0 <= n && n <= a.length })
static int sum(int[] a, int n) {
    int s = 0
    int i = 0
    @Invariant({ 0 <= i && i <= n })
    while (i < n) { s = s + a[i]; i = i + 1 }   // a[i] verified: i < n <= a.length
    return s
}
```

**Known limits.** Value-flow threading is single-assignment only — a
re-assignment throws the body out to the havoc fallback. Inside a loop body 5b
threads straight-line statements but does not fork on a nested `if`, so an
obligation guarded by an *inner* `if` is reasoned from the invariant alone, not
that guard (sound, less precise). And the per-site replay multiplies solver calls
— see the compilation-slowdown cross-cutting risk.

---

## Phase 6 — Quantifiers  *(shipped)*

**The frontier — bounded universals over arrays.** "Every element satisfies P",
sortedness, and the read/write reasoning that array algorithms need. Z3 handles
bounded universals well when the patterns are right; unbounded quantifiers are
where the trigger cliff lives, so the scope is **bounded universals only**
(existentials followed in Phase 9; unbounded quantifiers stay out of scope).

**Syntax for the user:**

```groovy
@Requires({ Forall.range(0, a.length) { a[it] >= 0 } })
```

`Forall.range(lo, hi, predicate)` is a static helper the encoder recognises and
rewrites to a Z3 `mkForall` over an integer constrained `lo <= i < hi`, with the
closure body as the matrix; `a[i]` becomes `(select a i)` under Z3's array theory,
and each such term becomes an instantiation trigger (one pattern per term, so a
matrix with several distinct selects — sortedness uses `a[i]` and `a[i+1]` —
instantiates robustly). The predicate is the trailing closure, naming the index
with `it` or an explicit `{ i -> ... }`; `Forall.range` stays executable, so the
groovy-contracts *runtime* check still works. It composes inside an ordinary
boolean `@Requires`/`@Ensures` (ANDed with normal conditions), reusing
groovy-contracts rather than a parallel annotation.

**Dependency note.** This natural `{ i -> ... }` spelling needs the patched local
`6.0.0-SNAPSHOT`: earlier groovy-contracts builds rejected *any* parameterised
closure (and `it`) nested inside a contract closure, which would have forced an
awkward static-marker workaround. The method-call surface is still the spike form
— [Phase 9](#phase-9--programmer-facing-surface-authoring--diagnostics) owns a
closer-to-idiom spelling.

**Read *and* write: `select` and `store`.** Reading covers proofs like binary
search. The write side models a single array's contents as a value — an immutable
Z3 array threaded through the method, each `a[i] = v` becoming `(store a i v)`
(`BodyEncoder` emits an `ArrayStore` step; a later read of `a[i]` sees the
update) — so a postcondition can describe the array a method *produced*: the
in-place-algorithm proofs (sort, partition, reverse) that are the Dafny-to-Java
showcase. This needs **no general heap or aliasing** (the non-goal below): it
assumes the array parameter is unaliased — the common case in algorithm code —
and reasons with value semantics. The `a.size` oracle and the `a` array value
share the source name, so a bounds obligation `i < a.size` and a `(select a i)`
agree; this retires Phase 1's "array contents not modelled" limit.

**In-loop `store` (shipped).** `store` is threaded through loop bodies too
(`LoopEncoder` rebinds `a := (store a i v)` on `a[i] = v`), so a quantified
`@Invariant` over the array's contents is preserved across the update — a
constant-fill (`a[i] = 0` ⇒ `Forall.range(0, n) { a[i] == 0 }`) verifies, and an
invariant the store breaks is refuted on preservation. Two surface notes the loop
case originally forced: inside `@Invariant` the quantifier had to be written fully-qualified
(`verification.Forall.range(...)`) and with a typed index (`{ int j -> a[j] ... }`)
— the invariant closure was compiled without the file's imports in scope and `a[j]` needs an `int`.
(The FQN half is **fixed in GROOVY-12072**: bare `Forall.range(...)` now resolves; the typed index stays.) And loop invariants are now
captured *as text and re-parsed* (like `@Requires`/`@Ensures`), so the verifier
sees a clean CONVERSION AST rather than the live node later phases resolve to a
static call / `getAt`. **Sort, revisited:** the *sortedness* half lands here — a
recursive insertion sort (`insert` + `sort`) verifies end-to-end via induction (see
Phase 7). The other half, **permutation** (a multiset/`count` model plus `old(a)`), and the
sound framing that lets the two compose in place, followed in Phases 12–14 — where the full
sort verifies *sorted ∧ permutation*. (A *loop*-based sort would also need nested-loop
support; the recursive formulation sidesteps it.)

**Known limits.** Counterexamples for array/quantifier refutations show the
integer skeleton (`a.size`, indices); Phase 9 since added pinning of
solver-constrained array *contents* and a runnable `fails on:` repro, though
unconstrained element values and a full array-model pretty-printer (cross-cutting
risks) stay open. UNKNOWN on a stalled quantifier stays a loud "could not decide"; the
user-supplied trigger/instantiation hint that would rescue it is the lightest
borrow from [Phase 8](#phase-8--beyond-smt-proof-by-computation-and-proof-hints).

---

## Phase 7 — Inter-procedural reasoning, induction & lemmas  *(shipped)*

Filed as an "optional heavy lift", this turned out to be the backbone of the Dafny-style
proofs — and it has landed. All of it reasons *modularly*: a callee's **contract** is used,
never its body.

- **Use a callee's `@Ensures` as a fact.** `int z = f(args)` assumes `f`'s postcondition
  with `result` bound to `z` and formals to actuals (same-class resolution by name + arity).
  A precondition check also assumes the `@Ensures` of the standalone call *immediately* before
  it, so `sort(a, n-1); insert(a, n-1)` composes — immediate-predecessor only, which is sound
  since nothing runs in between (a store between them would invalidate it, and does refute).
- **Induction over recursion.** A method may assume its *own* `@Ensures` at a recursive call —
  the inductive hypothesis — gated on a method-level `@Decreases` measure proved well-founded
  (`0 <= measure[args] < measure[entry]` at each call). It rides the stock `@Decreases`
  (GROOVY-12060), so it stays runtime-meaningful. No measure means the recursive result is
  opaque (honest "skipped"), never silently trusted.
- **Lemmas.** A `void` method proved by induction and *called for its `@Ensures`* — the
  proof-structuring primitive Dafny users lean on most. E.g. sortedness transitivity
  (`a[i] <= a[j]` for `i <= j` from adjacent sortedness, by induction on `j - i`) proved once
  and applied at a call site, quantifier instantiation and all.
- **Payoff — a verified sort.** A recursive insertion sort verifies its *sortedness*
  postcondition end-to-end: `insert` places `a[i]` into the sorted prefix (a store, by
  induction on `i`), `sort` composes on it (by induction on `n`). The recursive shape
  sidesteps nested loops entirely.

**Not done *here* (since shipped in Phases 12–14):** *permutation* for a real sort — the
multiset/`count` model and `old(a)` the sortedness proof above leaves out (it is only the
"zeroing the array would pass" half). Still genuinely open: mutual recursion (only direct
self-recursion gives an inductive-hypothesis point — a cycle needs SCC-aware reasoning over a
combined measure); and cross-module measure *inheritance* (an override of a precompiled super's
`@Decreases`), an upstream groovy-contracts limitation.

**Listed here as "still optional" — both since shipped:** full NIA (Phase 48 — variable products
and `/`/`%` dispatch; hard polynomial/square-root corners may still time out, an honest UNKNOWN) and
opt-in bounded-integer overflow (Phase 44 — `@CheckOverflow`). Bitwise/shift operators are now in too —
see the **bitwise / shift** slice below.

---

## Phase 8 — Beyond SMT: proof by computation and proof hints  *(8a shipped; 8b/8c opt-in)*

**A different axis from Phases 1–6.** Everything above widens the *fragment*
that gets encoded to Z3; the proof *mechanism* stays "collect obligations, hand
them to the solver". But SMT has a ceiling — most visibly Phase 6's trigger
cliff and the NIA opt-out — and the same ceiling exists in mature verifiers.
F\*, for instance, runs SMT by default but offers two escape hatches above it:
*symbolic computation* (prove by running an interpreter, not by equational
reasoning in the solver) and *tactics/metaprogramming* (full user-driven proof).
This phase records which of those are worth borrowing, and which are not — the
ordering is, as ever, by value against cost and fit with the project's
push-button, no-language-change identity.

### 8a — Normalisation: normalise-then-SMT *(the strongest candidate)*

**The escape hatch that fits Groovy's grain.** Many obligations are *closed
computations* that need no solver at all — you just run them. Groovy, unlike a
paper proof language, already ships an interpreter, so this is unusually cheap
to reach. A normalisation pre-pass slots in exactly where `Encoder.translate`
currently returns `null`:

- **Constant folding (closed sub-terms) — shipped.** A closed numeric sub-expression —
  `(2 + 2) * (2 + 2)`, a folded array index `a[(1 + 1) * 2]` — is reduced to a literal via
  `Encoder.tryFoldConstant` before encoding, dissolving the **NIA opt-out** for *constant* products.
  Reuses Groovy's own `ExpressionUtils.transformInlineConstants` (`NumberMath` semantics) so the
  fold matches Groovy's arithmetic.
- **Closed pure-function evaluation — shipped.** A tree-walking interpreter (`PureEvaluator`)
  computes a *same-class, side-effect-free* function applied to *constant* arguments to a literal —
  `pow2(10)` → 1024, `factorial(5)` → 120 — whether the call appears in a contract or a body. It
  evaluates the *clean* CONVERSION body over the evaluable fragment (literals, parameters,
  `+ - * %`, comparisons, boolean connectives, `?:`/`if`/`return`, single-assignment locals,
  same-class recursive/static calls); anything else makes the call un-evaluable and the verifier
  falls back to "skipped" — never guesses. Purity proxy: "body lies entirely in the fragment";
  step budget bounds non-terminating recursion.
- **Bounded symbolic unfolding — shipped.** A pure same-class function applied to *symbolic*
  arguments is inlined to its (single-expression) body with arguments substituted — so `absV(x)`
  becomes an `ite` and a recursive `pow2(n)` reduces one level per call. Recursion bounded by a
  per-VC **fuel** budget (F\*'s `fuel`/`ifuel`); when it runs out — or the body isn't a single
  expression — the unexpanded call is modelled as an *uninterpreted* integer function, a sound
  over-approximation. Fires only for *contract-free* methods (a contracted callee is Phase 7's
  inter-procedural path). **Phase 25 upgrade:** a recursive call now becomes a *shared* symbol
  `f#(args)` carrying its **defining equation**, so two applications are the same term by
  congruence and inductive proofs over a recursive contract function go through.

All three are pure accelerators — a wrong value still refutes on the SMT side (tested for each).
Evaluation computes with `long`, matching the encoder's mathematical-`Int` view, so they add no
new soundness gap beyond the existing bounded-int one.

The clean architecture is **normalise-then-SMT**: evaluate what you can, send the
residual to the solver. One asymmetry to state plainly — normalisation helps only
the *positive* case. It produces no counterexample when a fact is false; it
computes a value or gets stuck. So it is a discharge *accelerator*, not a
replacement for the SMT path, and the project's headline counterexamples stay on
the SMT side.

**Costs that keep this far down, not soon:**

- **It enlarges the trusted base.** F\*'s normaliser is part of its TCB; a Groovy
  evaluator used for proof becomes trusted too, and must agree with the
  *compiled runtime* semantics. Fold `2 * pow2(11)` at arbitrary precision while
  the program runs on 32-bit `int` and the "proof" diverges from reality. This
  couples directly to the **bounded-integer / overflow** item above: evaluation
  and encoding must commit to the *same* integer model or the tool lies.
- **Purity and termination.** Only side-effect-free, terminating methods are safe
  to evaluate — exactly the property `@Decreases` already reasons about, so there
  is real synergy with [Phase 3](#phase-3--loops-invariant--decreases-shipped).

### 8b — Structured proof decomposition *(opt-in, philosophy-compatible)*

When one SMT shot can't reach a fact, let the author break the proof into steps
the solver *can* each discharge — Dafny-style `assert P by { ... }` and `calc`
chains — rather than writing a proof term. No new evaluator, no tactic language;
each intermediate assertion is just another VC. This composes with 8a (an
intermediate `assert` can be discharged by evaluation) and with Phase 6's
instantiation hints. It is the bounded, defensible cousin of tactics: control
when automation fails, without becoming a proof assistant.

### Not in scope here

Full interactive tactics and proof terms (the Coq/Lean/F\* `intro; split; qed`
style) are a **non-goal** — see below. They cut against "no language change,
push-button, diagnostics-not-dialogues", the same reasoning that rules out heap
and concurrency. The line this phase walks: borrow *hints* (8a, 8b, Phase 6
triggers) that keep the tool a compile-time checker; refuse the proof-term
language that would make it a different product.

---

## Phase 9 — Programmer-facing surface (authoring & diagnostics)  *(shipped)*

**Adoption, not capability.** Everything above is about *what* can be proved;
this is about whether a working Groovy developer understands what to write and
what it tells them back, without first learning formal-methods vocabulary. The engine speaks in *obligations*,
*counterexamples*, and an internal *size oracle* (`a.size`); a programmer who just
turned the checker on speaks in `.size()`/`.length`,
`ArrayIndexOutOfBoundsException`, and "what input breaks it?". The goal is to meet
them there — the same instinct that makes the rest of Groovy's static type checker
say "Cannot invoke method size() on null object" rather than naming an internal
AST node. A tool people understand is one they leave switched on.

The distinction that scoped this phase — **two kinds of diagnostic:**

- **Those with a well-known code/runtime equivalent — mirror it.** *(shipped)* Every refuted
  implicit-safety obligation now reads in the developer's vocabulary, not the engine's:
  - the head names the exception they'd actually hit — `Possible IndexOutOfBoundsException`,
    `Possible ArithmeticException: Division by zero`, `Possible NullPointerException: Cannot
    invoke method size() on null object` (the invoked method threaded from the call site;
    `IndexOutOfBoundsException` covers both arrays and lists without inferring which);
  - the obligation and counterexample echo the **accessor the developer wrote** — `a.length`,
    `xs.size()` — harvested by scanning their contracts/body (first spelling wins; a bare
    `a[i]` defaults to `.size()`, valid for arrays too), not the internal `a.size` symbol;
  - a **`fails on:`** line reconstructs a runnable input — `g(new int[0], -1)`, `d(0, 0)`,
    `n(null)`, and even pinned array contents (`diff([21239, 21238] as int[], 0)`) for a
    contents-dependent failure, while contents that don't matter stay size-filled (`new int[3]`).

  All but the array-element pinning are pure `Reporter`/presentation — the engine keeps `a.size`
  internally and the rename is applied once at the solver boundary. The repro additionally reads
  boolean (nullity) and `select(arr, k)` values from the model (a small, contained `Z3Backend`
  touch) and is labelled best-effort: a field-dependent failure may not reproduce from it, and
  String contents / arbitrary objects stay unsynthesised. The **UNKNOWN** ("could not decide")
  head keeps its verification vocabulary — that case has no runtime analogue to borrow.
- **Those with no code equivalent.** Loop-invariant establishment/preservation, termination, and
  the quantifier obligations have no runtime analogue. Forcing a fake one would mislead; the
  right move is *self-explanatory* verification vocabulary — name the obligation and say plainly
  what could not be shown.

**Authoring vocabulary — the input side.** *(shipped)* "Meet the programmer where they are"
applies to how specs are *written* too. The bespoke `Forall.range(...)` helper is now joined by
the native GDK idioms a Groovy developer already reaches for, recognised in contract position and
lowered onto the same bounded `forall`:

```groovy
(0..<a.length).every { a[it] >= 0 }   // bounded range over indices
a.indices.every { a[it] >= 0 }        // the array's own index range
a.every { it >= 0 }                   // element-wise: `it` is the element
```

These need no import and stay runtime-evaluable, so they also work inside `@Invariant` (retiring
the `verification.Forall` FQN + typed-index warts the loop case forced). Recognition is
shape-restricted — any other `every` falls through to a loud "outside fragment" skip, never
silently reinterpreted.

The **existential `any` is now shipped** too — `a.any { it < 0 }`, `(lo..<hi).any { … }`,
`xs.indices.any { … }` — lowered to a bounded `∃ i. lo <= i < hi ∧ body`. It also **upgrades
`xs.contains(y)` from the opaque Phase-4 uninterpreted predicate to precise membership**
(`∃ i. xs[i] == y` over the modelled contents) — so `contains` now relates to actual element
values (e.g. `xs.contains(xs[k])` is provable for a valid `k`). Authoring relies on
GROOVY-12059 (nested closures in contract conditions) in the ASF snapshot. `Forall.range` still
works for back-compat; migrating its remaining internal uses is the open follow-up.

**Why it waited.** Pinning diagnostic/authoring wording before the capability set settled
(Phase 6 especially) would only have churned. With the surface now landed, the payoff is
adoption: the gap between a tool people trust and one they turn off because its errors read like
a proof transcript.

---

## Phase 10 — Instance methods & field state  *(shipped)*

The fragment was static-function-shaped; this opens it to ordinary OO code, in two layers.

**Layer A — instance methods, parameter contracts (already worked).** Nothing in the verifier
gated on `static`, so a non-`static` method with `@Requires`/`@Ensures` over its parameters
verifies exactly like a static one. Confirmed with a test; no code change.

**Layer B — instance field state (shipped).** A method may now read and write its receiver's
*scalar* fields:
- **Reads** — `this.count` (a `PropertyExpression` on `this`) and the bare `count` both resolve to
  the field's state variable, in contracts and bodies.
- **Writes** — `this.count = …` / `count = …` thread the field forward, via **SSA**: each
  assignment binds the name to a fresh version, so a method's `@Requires` sees the *entry* value
  and its `@Ensures` the *exit* value. `count = count + 1` becomes `count#1 == count + 1`, not the
  false `count == count + 1`. This dropped the old single-assignment-locals restriction, so
  re-assigned locals now work too; SSA versions are hidden from the displayed counterexample.

So a mutator is proven to maintain its bound — `@Requires({ count < max }) @Ensures({ count <= max })
void inc() { count = count + 1 }` verifies, and the same without the guard refutes (`count = max`,
the entry/exit distinction made visible). Framing within a single method is trivial (unwritten
fields are unchanged); the receiver's fields are assumed unaliased, the same boundary arrays draw.

**Class-level `@Invariant`** (the natural next layer for OO code) was originally listed as the open
piece here; it **shipped in full — Phase 15a** (instance methods), **15b** (constructors), **45**
(cross-class). *Cross-method* field effects — the `@Modifies`/framing slice — followed in Phase 13. (Array-typed fields work already —
`a[j] = v` on a field threads through `arrayFor` like a param.)

---

## Phase 11 — Pre-state: `old`  *(shipped)*

A postcondition can now relate the *exit* state to the *entry* state via groovy-contracts' `old`
map. `old.field` reads the field's value at method entry; `old.a[i]` reaches into the entry
*contents* of an array field. The verifier captures the snapshot in `checkPath` *before* the body's
writes SSA-rebind state forward, binding `old$field` to the entry value (scalar and array views
both pinned). `@Ensures({ count == old.count + 1 })` verifies for `count = count + 1`, and the
mismatched `count = count + 2` refutes.

This is the keystone the framing/permutation arc needed. The headline is the **element frame**:
a setter that writes only `a[j]` proves every other element is left alone —
`@Ensures({ (0..<a.length).every { it == j || a[it] == old.a[it] } })` — which is exactly the
shape `@Modifies` leans on (Phase 13) so that sound array-havoc-on-call doesn't lose the elements a
callee didn't touch (the gap that would otherwise break the recursive insertion sort).

`old` is instance-only upstream (GROOVY-12052: it snapshots instance state, unsupported in static
methods), so it builds on the Phase 10 field support. It is fully dual-purpose: groovy-contracts
*clones* `Cloneable` fields for the runtime `old` map, and arrays are `Cloneable`, so for `int[]`
the runtime snapshot matches the verifier's entry-snapshot model. **Not yet:** `old` of
method *parameters* (upstream models only fields). (`old` over a multiset/`count` — the permutation
step — followed in Phase 12.)

---

## Phase 12 — Permutation: multiset / `count`  *(building block shipped)*

The half a sort is missing beyond *sortedness* is *permutation* — that the output is a rearrangement
of the input. The tractable encoding, which sidesteps the unbounded `∀v` a multiset usually needs:

- **`count`** — Groovy's GDK `a.count(v)` (occurrences of `v`) modelled as an uninterpreted
  `count(arr, v) : (Array, Int) -> Int` (`SmtBackend.count`). `old.a.count(v)` is the entry snapshot.
- **Per-store update law** — on every `a[i] = val`, `checkPath` asserts
  `count(store(a,i,val), v) = count(a, v) - [a[i]==v] + [val==v]` for the values `v` the postcondition
  counts. This is the sound semantics of `count` under one store; nothing else axiomatises it.
- **Ghost value parameter** — a method takes a value param `v` and proves
  `@Ensures({ a.count(v) == old.a.count(v) })`. Since `v` is an arbitrary free parameter, proving it
  for `v` *is* proving it for all values — permutation, with **no quantifier in the SMT**.

A **swap** is two stores whose count updates cancel, so it preserves every count — verified — while a
plain copy (drops an element) refutes. That building block is sound and shipped.

**Co-dependency found with `@Modifies` (since resolved).** At this point the *recursive* sort's
permutation did not hold soundly: when a caller assumes a callee's `@Ensures` that mentions `old.a`,
the assume path resolved `old.a` to the *caller's* entry snapshot, not the array *at the call* — so
the recursion's count clause became an inconsistent (vacuous) assumption (a broken overwrite-`insert`
wrongly "verified", which is how this was caught). Binding a callee's `old` to a *call-site* snapshot
is precisely the `@Modifies`/havoc machinery, built in Phase 13 — which closed this, so the full
insertion sort verifies *sorted ∧ permutation* in Phase 14. The per-store `count` law built here is
the standalone, sound foundation for that.

---

## Phase 13 — Frame conditions: `@Modifies`  *(shipped)*

A method declares the caller-visible locations it may change via groovy-contracts'
`@Modifies({ this.field })` / `@Modifies({ [this.a, this.b] })` / `@Modifies({ param })`. Captured
like the other contracts (a `modifies` member on `@ContractSource`).

**Frame-check (shipped).** A method carrying `@Modifies` is verified to write *only* the locations
it lists — every `a[i] = v` (array `a`), `this.x = v` / bare field `x = v` is checked against the
declared set; local writes don't count. `@Modifies({ [] })` means pure (any field/array write is a
loud error). This is the callee-side half: a method honours its own frame.

**Caller-side framing (shipped).** At a call to a method with `@Modifies`, the caller now *havocs*
the declared locations (fresh symbols) and reframes them from the callee's `@Ensures` — binding the
callee's `old.X` to the value *at the call*, not the caller's own entry snapshot. That last point was
the bug Phase 12 surfaced (a callee's `old.a` resolving to the caller's entry made the recursion's
`count` clause vacuous; a broken overwrite-`insert` wrongly verified). With it fixed:
- the cross-call **"clobber"** unsoundness is closed — a caller can no longer assume an array a callee
  may modify is unchanged (verified: a caller relying on `a[0]` across a clobbering call now refutes);
- a `@Modifies`-only callee (no `@Ensures`) is modelled as a pure havoc of the declared locations
  (`resolveContractedCallee` widened to accept it);
- the recursive insertion sort is proven a **permutation** for real — `a.count(v) == old.a.count(v)`
  holds across the swaps *and* the recursive calls — and the broken overwrite now refutes.

---

## Phase 14 — The fully verified sort: *sorted ∧ permutation*  *(shipped; precondition hardened in Phase 24)*

> **Hardened by Phase 24** — the `insert` recursive precondition had been passing vacuously
> (name-conflation); restored with a one-line `maxBound` lemma. Now sound at every obligation.

The capstone. A recursive in-place insertion sort proven **both** correctness halves at once —
the result is sorted *and* a permutation of the input — under sound `@Modifies` framing (every call
havocs the array and reframes it from the callee's `@Ensures`; nothing is assumed unchanged for
free). No new engine machinery: it composes bounded quantifiers (Phase 6/9), induction via
`@Decreases` (Phase 7), the per-store `count` law (Phase 12), `old` pre-state (Phase 11), and
caller-side framing (Phase 13) into a single result. See the README's "fully verified sort".

The sortedness-under-havoc problem flagged at the end of Phase 13 — after the recursive call havocs
`a`, proving `a[m-1] <= a[m]` — is solved without a range-multiset: the recursion passes the **pivot
`a[m]` itself** as a fresh, *tight* upper bound `hi`, so the sorted prefix the recursion returns is
bounded by exactly the element it must sit below. A ghost value `v` carries the multiset
(`a.count(v) == old.a.count(v)` for arbitrary `v`), and a suffix-frame clause (`(m+1..<a.length).every
{ a[it] == old.a[it] }`) preserves the untouched tail across the havoc. Soundness is anchored: a
no-op sort cannot claim its result is sorted, and an overwriting insert (Phase 12) cannot claim the
permutation.

---

## Phase 15a — Class `@Invariant`: instance methods  *(shipped)*

The natural OO follow-on to Phase 10's instance fields: a `@groovy.contracts.Invariant({ ... })` on a
class is an **object invariant** — at runtime it holds after every constructor and before/after every
method call. The verifier now treats the class-level form as an extra exit obligation for each
non-static instance method: **assumed at method entry** (an extra fact in scope, alongside `@Requires`)
and **proved at method exit** (conjoined into the goal that `@Ensures` carries, or — for void methods
with no `@Ensures` — standing as the sole exit obligation).

**How it works:**

- **Capture.** A sibling of `ContractExpansionTransform.augment` walks `cn.annotations` at CONVERSION,
  reads each `@Invariant` closure's verbatim text via the same `SourceText` path as
  `@Requires`/`@Ensures`, and attaches a runtime `@ClassInvariantSource` carrier (separate from the
  method-level `@ContractSource` to keep its target narrow). Both the repeatable `@Invariant`
  sequence and the `@Invariants` container shape are handled.
- **Resolve.** `VerifyChecker.classInvariantTexts(ClassNode)` walks the superclass chain super-first
  and returns each captured text re-parsed to an `Expression`. Parent invariants are AND-conjoined
  with the subclass's — matching groovy-contracts' upstream semantics.
- **Pre-filter.** `beforeVisitMethod` pre-translates each invariant in a probe session and drops any
  that don't encode (e.g. `name.length() > 0` on a String field — outside the fragment). One
  `Skipped class invariant` diagnostic per dropped clause per method, not one per discharge site.
- **Wire.** `assumeClassInvariants(s, enc)` is the single helper called from every discharge site:
  - `checkPath` — entry-assume + exit-conjoin (postcondition path).
  - `assumeContext` / `dischargeVfObligation` / `dischargeSeeded` — entry-assume for the
    implicit-obligation discharge (Phase 1/5 paths).
  - `checkEstablishment` / `checkPreservation` / `checkProgress` / `checkUse` — entry-assume for the
    four loop VCs.
- **Diagnostic.** `Reporter.formatClassInvariantViolation` emits the dedicated
  `Cannot prove class invariant of <method> holds at method exit` head when the invariant is the
  sole reason for refutation; `formatClassInvariantSkipped` for outside-fragment clauses.

```groovy
@groovy.contracts.Invariant({ count >= 0 })
class Counter {
    int count
    void inc() { count = count + 1 }                          // verifies: invariant preserved
    void dec() { count = count - 1 }                          // REFUTED: count = 0 → -1
    @Requires({ count > 0 }) void safeDec() { count = count - 1 }   // verifies under the guard
}
```

**Soundness scope.** Sound by construction at *method-entry points* (establishment, postcondition
goal, implicit-obligation seed). For the loop **preservation/progress** VCs the invariant is also
in scope, which is sound iff the loop body doesn't write to a field the invariant references — the
same caveat already in place for the body-internal obligation discharge. A future frame analysis
(per-loop, analogous to `@Modifies` for methods) tightens this; until then, users putting actively-
mutated fields in a class invariant should anticipate the limitation.

**Not yet (15b/15c):**
- **Constructors establishing the invariant.** Shipped in Phase 15b below.
- **Cross-class call-site assumption.** At a call `caller.someOther.m(...)`, the callee's class
  invariant can be assumed to hold both before and after — natural extension of `assumeCalleeEnsures`
  in Phase 13. 15c.
- **Cross-module class-invariant transport.** Same producer-recompile discipline as method
  `@Requires`: a producer compiled without groovy-verify won't carry the class-invariant text in
  bytecode. 15c.

---

## Phase 15b — Class `@Invariant`: constructors establish the invariant  *(shipped)*

**Closes the "instance methods only" qualifier Phase 15a left.** Phase 15a treated `@Invariant` as
an extra entry-assumption + exit-obligation for every non-static method. Constructors got nothing:
the capability table read "instance methods" with that asterisk visible to anyone evaluating the
framework. Now a constructor proves the invariant *at exit* (no entry-assume — the invariant is the
goal, not a precondition), so the class is verified valid by construction.

**Three things made it work:**

- **Constructor capture.** `ContractExpansionTransform` now iterates `cn.declaredConstructors`
  alongside `cn.methods`, attaching the same `ContractSource` annotation + clean-body snapshot.
- **`afterVisitClass` sweep.** Groovy's `StaticTypeCheckingVisitor` doesn't dispatch constructors
  through the `beforeVisitMethod`/`afterVisitMethod` hooks — silent skip. `VerifyChecker` now
  overrides `afterVisitClass(ClassNode)` and manually invokes the same setup + verify pipeline for
  each constructor, with a `currentIsConstructor` flag that makes `assumeClassInvariants` a no-op
  at entry (the invariant is the goal, not a fact).
- **Int-field default-init.** A `Counter()` with an empty body trivially satisfies
  `@Invariant({ count >= 0 })` at runtime (JVM zeroes Int fields before the constructor body),
  but without default-init the field would be unconstrained and refute. `initFieldDefaults`
  asserts `field == 0` at constructor entry for each Int-like instance field. Reference / Set /
  Map / array fields are left unconstrained — the constructor body is expected to initialise them
  when the invariant requires.

```groovy
@groovy.contracts.Invariant({ count >= 0 && count <= max })
class Counter {
    int count, max
    @Requires({ m > 0 })
    Counter(int m) { max = m }                              // verifies — count is default 0, max = m > 0
    @Requires({ count < max })
    void increment() { count = count + 1 }                  // verifies — Phase 15a path
}
```

Drop the `@Requires({ m > 0 })` and the constructor refutes (count >= 0 holds, but max >= count
needs max >= 0 — m could be negative). A `Counter(int n) { count = n }` without
`@Requires({ n >= 0 })` likewise refutes, with `fails on: <init>(-1)` from the model.

**Known limits:**

- **Field initializers.** Groovy compiles `int count = 5` into a synthetic init block prepended to
  every constructor. The clean-body snapshot may or may not contain that injected code; the first
  cut here trusts the constructor body to explicitly assign anything the invariant requires.
  Field initializers as a verified path is a future polish.
- **`<init>` in the diagnostic.** The refute message names the constructor by its JVM-internal
  `<init>` name; a small Reporter tweak could surface the source-level class name (`Counter(-1)`).
- **Cross-class call-site invariant assumption** (when a *consumer* method calls into a class with
  an invariant) remains deferred to 15c. Within a single class, the constructor's exit invariant
  becomes the entry assumption for every other method via Phase 15a's assume-at-entry mechanism;
  cross-class needs the same callee-side invariant lookup applied at the call site.

---

## Phase 16 — Finite sets: membership + cardinality law  *(shipped)*

**The first genuinely new *data structure*, and the foundation under reasoning about reachable-set
algorithms (DFS, worklists, dedup).** Everything before this modelled integers, sequences (arrays /
lists by index), and scalar field state. A `set<T>` is the data structure those proofs are actually
built on — a value that only grows, a membership test, and a cardinality that drives termination —
and it is also everyday Groovy. This lands it for the common, tractable case.

**The encoding — sets as characteristic arrays, the in-grain choice.** A `Set<Integer>` is an
`Array Int -> Int` characteristic function (`1` = member, `0` = absent), so the three core operations
reuse Z3's array theory wholesale rather than introducing a new theory:

- **membership** — `x in s` / `s.contains(x)` → `(select s x) == 1`;
- **add / remove** — `s.add(x)` / `s.remove(x)`, threaded through the body as `s := (store s x 1|0)`
  exactly like an array store, so a later membership read of the post-state resolves through the
  store/select axioms for free (no quantifier);
- **cardinality** — `s.size()` is an uninterpreted `(Array) -> Int` (`setCard`, the direct analogue of
  Phase 12's `count`), whose meaning comes **only** from a per-mutation update law asserted at each
  add/remove: `card(add(s,x)) = card(s) + (x in s ? 0 : 1)`, `card(remove(s,x)) = card(s) - (x in s ? 1 : 0)`.

This is the quantifier-free heart of the recommendation: the same "uninterpreted measure + per-operation
update law" pattern that made permutation provable without `∀v` in Phase 12, now applied to a set's size.
A method that adds an element known *fresh* (`@Requires({ !(x in s) })`) proves `s.size() == old.s.size() + 1`;
drop the freshness premise and the `+ 1` rightly refutes (`x` may already be present). That `size`-grows-by-one
law is precisely what a set-valued `@Decreases` measure (`N - visited.size()`) needs.

**How it works:**

- The encoder is otherwise *shape-based and untyped*, but set and list operations are syntactically
  identical (`contains`, `size`, `in`, `+`). So `VerifyChecker` computes the set-typed parameter/field
  names (`collectSetNames`, `Set`-implementing declared types) and hands them to the `Encoder`
  (`setNames`) — the one place a type hint is needed. A receiver in that set lowers to set semantics;
  anything else stays on the list/array path.
- Body mutation rides the existing path machinery: a standalone `s.add(x)` is captured as a `LemmaCall`
  and intercepted in `checkPath` (`applySetMutation`) ahead of the inter-procedural lemma path, threading
  the store and asserting the cardinality law — no new `BodyEncoder` step kind.
- `old.s` is snapshotted as a set (entry handle) alongside the scalar/array snapshots, so
  `x in old.s` / `old.s.size()` read the entry value. `@Modifies` is honoured on both sides: a set
  mutation is frame-checked as a write to `s` (an undeclared `s.add` under `@Modifies({})` is a loud
  error), and a modified set field is havoced + reframed at a call site like an array.

```groovy
class C {
    Set<Integer> s
    @Requires({ !(x in s) })
    @Modifies({ this.s })
    @Ensures({ x in s && s.size() == old.s.size() + 1 })
    void put(int x) { s.add(x) }                 // verified
}
```

**Known limits (the honest edges).**

- **Element domain is `Int`.** A `Set<Integer>` (node ids, keys) is modelled; `Set<String>` /
  `Set<Object>` would need an element→Int mapping (Route 2 in the design notes), not done.
- **Set *algebra* stays out of fragment.** Union / intersection / subset (`s.containsAll(t)`,
  `s + t`, `s <= t`) need an unbounded `∀x. x∈s ⇒ x∈t` — the explicit quantifier non-goal — so they
  emit a loud "skipped", never a silent pass. *(Since shipped, all via the bounded-domain lowering: subset
  for enum-element sets in Phase 30 and Int-element in Phase 31; the full four-op algebra — union `+`,
  intersection `.intersect`, difference `-`, symmetric difference `^` — as pointwise membership, binop
  `containsAll`, and materialised set locals, enum and Int, in Phase 33/35 + the four-op extension. Only set
  cardinality of a derived set stays out.)*
- **Maps** build directly on this phase (a key-*set* that is itself a set) — shipped in Phase 17 below.

**Wired into recursion termination.** The cardinality law now drives a recursive `@Decreases` measure: the
termination replay (`dischargeTermination`) threads each `s.add(x)` / `s.remove(x)` through the per-mutation
law and translates the *entry* measure before those effects, so a set-valued measure like `n - s.size()`
strictly decreases across a recursive call exactly when a fresh element was added. This is the
DFS-shaped termination argument — a finite recursion over a bounded domain that ends because the visited
set keeps growing — proved with **no quantifier**:

```groovy
class C {
    Set<Integer> s; int n
    @Modifies({ this.s })
    @Decreases({ n - s.size() })
    void fill(int x) {
        if (!(x in s) && s.size() < n) {   // x is fresh, room remains
            s.add(x)                       // |s| grows by one (the cardinality law)
            fill(x + 1)                    // measure n - |s| strictly decreases
        }
    }
}
```

Drop the `!(x in s)` freshness guard and `s.add(x)` may be a no-op, so the measure need not decrease —
termination rightly refutes (`fails on: fill(4)`). The termination half — historically the hard part,
since cyclic graphs make naive DFS loop forever — is done.

---

## Phase 17 — Finite maps: value array + key-set  *(shipped)*

**The DFS adjacency representation — and it cost almost no new machinery, because a map decomposes into
two things this project already has.** A `Map<Integer,Integer>` is modelled as a **value array** (its
contents, `m[k]`) *plus* a **key-set** (its domain) — and the key-set is exactly the Phase-16 set, so
`m.containsKey`, `m.size()`, and the cardinality law come straight from the set machinery.

**The encoding:**

- **value lookup** — `m[k]` / `m.get(k)` → `(select vals k)` over the value array;
- **key membership** — `k in m` / `m.containsKey(k)` → set membership on the key-set;
- **put** — `m.put(k,v)` / `m[k] = v` does *both* sides at once (`doMapPut`): `vals := (store vals k v)`
  **and** the key-set add `keys := (store keys k 1)` with the per-mutation cardinality law. So after a
  put: `m[k] == v` (value read), `m[j] == old.m[j]` for `j != k` (the value frame, via array theory), and
  `m.size()` grew by one **iff** `k` was a new key;
- **size** — `m.size()` → `card(keys)`, reusing the set cardinality and its law unchanged.

**How it works:** the same shape-based-encoder-needs-a-type-hint story as sets — `VerifyChecker` collects
the `Map`-typed names (`collectMapNames`) and hands them to the `Encoder`, which routes a subscript /
`in` / `.get` / `.containsKey` / `.size` on those names to map semantics. Both put spellings ride the
existing path machinery (`m.put` as a `LemmaCall`, `m[k] = v` as the `ArrayStore` step), and a map
subscript is **excluded** from the array-bounds obligation — `m[k]` is a key lookup, not an index. `old.m`
snapshots both dimensions; `@Modifies` frame-checks a `put` and havocs/reframes a modified map across a
call, like an array. And the **key-set cardinality drives a recursive `@Decreases` measure** the same way
sets do — `n - m.size()` strictly decreases when a fresh key is inserted (the map twin of the DFS
termination above).

```groovy
class C {
    Map<Integer,Integer> m
    @Requires({ j != k })
    @Modifies({ this.m })
    @Ensures({ m[k] == v && m.containsKey(k) && m[j] == old.m[j] })
    void put(int k, int v, int j) { m.put(k, v) }     // verified
}
```

**Known limits.** Int keys and Int values only (`Map<Integer,Integer>`). The two pieces a *full* DFS over
`map<Node, set<Node>>` still wants: **(a)** nested values — a map whose values are themselves sets
(`Map<K, Set<V>>`), i.e. a value array of *set* handles (nested arrays, modellable but not yet wired); and
**(b)** the reachability **functional** postcondition (every reachable node ends visited), a bounded-domain
`every` over the adjacency relation. Value-search ops (`containsValue`) and `keySet()`/`values()` as
first-class collections stay a loud skip. With sets, maps, and the cardinality measure all in place, those
two are the remaining gap between here and a fully verified DFS — and both are additive, no engine rework.

---

## Phase 18 — Reachability: the recursive graph traversal  *(shipped)*

**The property a search algorithm exists for — and it composed from the previous phases with no new engine
code.** A depth-first traversal of a functional graph (`next : Map<Node,Node>`, the successor) that marks
nodes in a `Set<Node>`, with a reachability postcondition proved by induction. The notable part is that
sets (Phase 16), maps (Phase 17), induction via `@Decreases` (Phase 7), caller-side set framing (Phase 16),
and bounded quantifiers (Phase 9) *already* compose to discharge it — this phase is the demonstration, not
new machinery.

**What is proved (the two halves the bounded fragment expresses soundly):**

- **Soundness — `visited` only grows.** `(0..<n).every { !(it in old.visited) || (it in visited) }`: a
  bounded universal over the node domain saying every previously-visited node stays visited. The recursive
  call havocs `visited` (sound `@Modifies`) and reframes it from the callee's `@Ensures`; the self-`@Ensures`
  is the inductive hypothesis, and the store relation `visited1 = visited0 ∪ {u}` chains through it.
- **Progress — the node handed in ends visited.** `fuel <= 0 || (u in visited)`: under a fuel budget (a
  plain-int `@Decreases`), the traversed node is covered. On the base case it is already present; on the
  step it is added before the recursion, and monotonicity carries it across the havoc.

Both halves hold under a fuel measure; the soundness half also holds under the **set-cardinality measure**
`@Decreases({ n - visited.size() })` — the DFS-shaped termination from Phase 16 — proving the two
contributions (a cardinality-terminating recursion *and* a reachability postcondition) compose. A traversal
that *removes* a node refutes the monotonic-growth clause; claiming coverage *unconditionally* (dropping the
`fuel <= 0` guard) refutes, because the budget can run out.

```groovy
@Requires({ 0 <= u && u < n && (0..<n).every { 0 <= next[it] && next[it] < n } })
@Modifies({ this.visited })
@Decreases({ fuel })
@Ensures({ (0..<n).every { !(it in old.visited) || (it in visited) } &&
           (fuel <= 0 || (u in visited)) })
void visit(int u, int fuel) {
    if (fuel > 0 && !(u in visited)) { visited.add(u); visit(next[u], fuel - 1) }
}
```

**The honest boundary — what is *not* proved, and why.** Two reachability properties stay out of reach, both
recorded as future work because each needs a genuinely new capability, not just more wiring:

- **Unconditional progress / `start ∈ visited` for an *unbounded* (cardinality-terminating) DFS.** The
  cardinality measure forces the guard `visited.size() < n` (so the recursion is well-founded), which means
  the method legitimately stops when `visited` is "full". To conclude the node is nonetheless covered, you
  need the **domain-cardinality fact**: for `S ⊆ {0..n-1}`, `|S| ≤ n`, and `|S| = n ⇒ S = {0..n-1}`. The
  uninterpreted `card` (Phase 16) knows only its per-mutation deltas, not this relation to the domain. The
  fix is a bounded **cardinality axiom** — e.g. `card(S)` defined as `Σ_{i<n} (i ∈ S ? 1 : 0)`, a bounded
  sum tying cardinality to membership over `0..<n`. *(Since shipped as `bcount`, Phases 19–22.)*
- **Completeness — every reachable node is visited (the closure fixpoint).** This is the deep half of DFS
  correctness. It is *not* a simple inductive set property: the invariant DFS actually maintains is "`visited`
  is closed under successors **except** for nodes on the current recursion stack", so it needs the stack
  modelled (a sequence/ghost), or an explicit inductive `IsPath` predicate plus a least-fixed-point argument
  — beyond the bounded-quantifier fragment. This is the same frontier subtlety that makes DFS a showcase
  proof in Dafny, and is left as an explicit non-trivial target.

Net: the **termination** half of DFS (Phases 16/17) and the **soundness + bounded-progress** reachability
postconditions (this phase) are done and sound; **completeness** and **unconditional coverage** are the two
named, well-understood gaps remaining — the former needing a stack/path model, the latter a cardinality axiom.

---

## Phase 19 — The cardinality axiom: pigeonhole over a bounded domain  *(shipped)*

**The link the uninterpreted cardinality was missing.** `card(s)` (Phase 16) tracks only its per-mutation
deltas — it has no relationship to *which* elements a set holds, so `|s| <= n` for a set drawn from an
`n`-element domain was not derivable. `Sets.boundedBy(s, n)` supplies that relationship — the **pigeonhole** —
as a recognised contract predicate.

**The encoding — a faithful definition, not a trusted axiom.** `Sets.boundedBy(s, n)` means exactly
`s ⊆ [0, n)`, and the encoder lowers it to

```
card(s) <= n  ∧  (card(s) < n  ∨  ∀ i. 0 <= i < n ⟹ i ∈ s)
```

i.e. "bounded by the domain, and *full* (`card == n`) exactly when it covers `[0, n)`". Both pieces — the
cardinality comparison and the bounded membership universal — are already modelled, so this is a boolean
*definition* (sound in both assume and goal positions), not an axiom injected behind the user's back. The
runtime helper `Sets.boundedBy` evaluates the same predicate, so the groovy-contracts runtime check agrees.
`Encoder` recognises the `Sets.boundedBy(s, n)` call shape (like `Forall.range`) and emits the lowering, the
membership `select(s, i)` term serving as the universal's instantiation trigger.

From it the engine **derives** the two facts cardinality-driven search needs, neither previously provable:

- **FULL ⟹ MEMBER** — `Sets.boundedBy(s,n) ∧ s.size() == n ∧ 0 <= u < n ⊢ u ∈ s` (a full bounded set is the
  whole domain).
- **HOLE ⟹ NOT FULL** — `Sets.boundedBy(s,n) ∧ 0 <= u < n ∧ u ∉ s ⊢ s.size() < n` (a missing in-domain node
  means room remains) — exactly the coverage-branch fact a cardinality-terminating DFS needs.

Drop `Sets.boundedBy` and both refute: the uninterpreted size says nothing about membership.

**The honest boundary — why this does not, by itself, close whole-DFS unconditional coverage.**
`Sets.boundedBy` gives the pigeonhole *consequences*, but a recursive DFS must also **preserve** boundedness
across the add that *fills* the set — and proving `Sets.boundedBy(s ∪ {u}, n)` when `|s| = n-1` requires the
*converse* counting: `|s| = n-1 ∧ s ⊆ [0,n) ⟹ s is [0,n) minus exactly one element`, so the fresh in-domain
`u` is precisely that element. The definitional `Sets.boundedBy` does not yield "exact membership from exact
count". Closing it needs a **bounded-sum cardinality** `bcard(s, k) = Σ_{i<k} (i ∈ s ? 1 : 0)` with its
recursive defining axioms, plus the monotonicity/exact-count lemmas proved by induction (Phase 7) — at which
point `card(s)` over a domain *equals* `bcard(s, n)` and the counting closes. *(Since shipped: that
bounded-sum cardinality is `bcount`, Phases 20–22, with the recursive defining axioms landing in Phase 25.)*
`Sets.boundedBy` is the usable pigeonhole layer above the uninterpreted `card` and below it, and stands on
its own (the `HOLE ⟹ NOT FULL` fact is the DFS coverage branch in isolation).

---

## Phase 20 — Bounded-sum cardinality `bcount`: properties earned by induction  *(shipped)*

**The genuine count — and its foundational properties are *proved*, not axiomatised.** The bounded sum
`bcount(s, k) = Σ_{i<k} (i ∈ s ? 1 : 0)` is the real count of `s`'s members in `[0, k)` — the quantity
`Sets.boundedBy` (Phase 19) approximated and the uninterpreted `card` (Phase 16) had no handle on. The notable
part: it is *just an ordinary recursive Groovy method*, and its defining properties fall out of the framework's
own induction (`@Decreases` on `k`, the self-`@Ensures` as the inductive hypothesis, Phase 7) — there is no
built-in `bcount` and no trusted axiom.

```groovy
@Requires({ k >= 0 })
@Ensures({ 0 <= result && result <= k })        // the BOUND, by induction on k
@Decreases({ k })
static int bcount(Set<Integer> s, int k) {
    if (k == 0) return 0
    int rest = bcount(s, k - 1)                  // Assign-form call → the IH applies: 0 <= rest <= k-1
    return rest + ((k - 1) in s ? 1 : 0)         // (k-1) in s is a 0/1 membership ite
}
```

**Two foundational lemmas, both verified:**

- **Bound** — `0 <= bcount(s,k) <= k`. This is precisely the converse-counting *upper bound* the uninterpreted
  `card` could not provide (Phase 18's termination needed it; Phase 19's `Sets.boundedBy` could only *assume* it).
- **Full domain ⟹ count = k** — the same recursion under `@Requires({ (0..<k).every { it in s } })` proves
  `result == k`, tying the count to actual membership. The recursive call's precondition
  (`(0..<k-1).every { it in s }`) follows from the caller's over `[0, k)` by bounded-quantifier instantiation.

The bound is *earned*: a body that over-counts (`rest + 2`) refutes `result <= k`. No machinery was added —
this is the recursive-function induction (Phase 7) over the set membership and bounded quantifiers (Phases
9/16) already present, which is itself the point: the bounded-sum cardinality is *in reach of the existing
fragment*.

**What this unlocks, and what was then open for whole-DFS coverage.** `bcount` supplies the counting facts
`card`/`Sets.boundedBy` lacked. To finish wiring it into a DFS that proves *unconditional* coverage, two steps
remained, both needing **recursive-definition reasoning inside contracts** (so a `bcount(...)` term carries its
defining equation rather than reducing to an uninterpreted symbol) — *both since shipped (per-add law Phase 21,
cross-lemma/defining-equation use Phase 25, full-characterization + unconditional coverage Phase 22)*:

- the **per-add law** — `bcount(s ∪ {u}, k) = bcount(s, k) + (0 <= u < k ∧ u ∉ s ? 1 : 0)` — the `bcount`
  analogue of the per-store `count` law (Phase 12), threading the count across a set mutation; and
- **cross-lemma use** — referencing `bcount` in one method's contract and discharging it from another's
  proved `@Ensures` (today a `bcount(s,k)` term *inside a contract* is modelled as an uninterpreted function,
  so its definition isn't visible across the lemma boundary).

With those, `card(s)` over a domain *equals* `bcount(s, n)`, the "`|s| = n-1` ⟹ exactly one hole" preservation
closes, and the cardinality-terminating DFS proves unconditional coverage. The foundational lemmas here are the
base that development builds on.

---

## Phase 21 — The bcount per-add law: `Sets.boundedCount` as a primitive  *(shipped)*

**Threading the count across a mutation — the first of the two steps Phase 20 flagged.** The recursive
`bcount` (Phase 20) *earns* its bound by induction, but a `bcount(...)` term inside another contract reduces to
an uninterpreted symbol (its definition isn't visible across the lemma boundary) and it cannot take `s ∪ {u}`
as an argument — so it cannot relate the count *before* and *after* a set mutation. `Sets.boundedCount(s, k)` is the
same bounded count exposed as a **primitive**, which can.

**The encoding — bound axiom + per-mutation law, the `count` machinery adapted.** `Sets.boundedCount(s, k)` is an
uninterpreted `(Set, Int) -> Int` (`setCount`, backed by Z3 `bcount$`). On first use of each term the encoder
asserts its **sound bound axiom** — `0 <= bcount`, `k >= 0 ⟹ bcount <= k`, `k <= 0 ⟹ bcount == 0` (all
theorems of "count of members in `[0,k)`", so asserting them keeps the symbol as strong as the count it
models). At every set mutation `s.add(u)` / `s.remove(u)`, for each `k` the postcondition or measure tracks
(harvested by `bcountKArgs`, mirroring `countValueArgs` for the Phase-12 `count` law), the **per-add law** is
asserted:

```
add:    bcount(s', k) = bcount(s, k) + (0 <= u < k ∧ u ∉ s ? 1 : 0)
remove: bcount(s', k) = bcount(s, k) - (0 <= u < k ∧ u ∈ s ? 1 : 0)
```

— the mutation changes the count only at slot `u`, and only when that slot lies in `[0, k)`. It rides the
existing per-store-law plumbing in `applySetMutation` (driven by the `currentBcountKExprs` set per discharge),
so it threads through both the postcondition check and the termination replay.

```groovy
@Requires({ 0 <= u && u < k && !(u in s) })
@Modifies({ this.s })
@Ensures({ Sets.boundedCount(s, k) == Sets.boundedCount(old.s, k) + 1 })   // verified
void put(int u, int k) { s.add(u) }
```

Verified, and sound on each edge: drop the freshness guard and the `+ 1` refutes; add an element *outside*
`[0, k)` and the count is provably unchanged (the law's domain guard); `remove` of a present in-domain element
decrements it; and the bound axiom rides the primitive (`0 <= Sets.boundedCount(s,k) <= k` for `k >= 0`).

**What remains for whole-DFS unconditional coverage.** One Phase-20 step is now done (the per-add law); the
other — **cross-lemma/definitional use** — is subsumed by giving `Sets.boundedCount` its **full-characterization**:
`Sets.boundedCount(s, k) == k ⟺ (0..<k).every { it ∈ s }` (the converse of Phase 20's "full ⟹ count = k", which the
per-add law's bound does not by itself supply). With it, the preservation argument closes — adding the fresh
in-domain `u` to a set whose count is `n-1` raises the count to `n`, which *forces* domain coverage, so
`Sets.boundedBy` is preserved across the filling add and the cardinality-terminating DFS proves unconditional
`start ∈ visited`. *(Since shipped: the full-characterization axiom in Phase 22, the frontier/stack invariant
for completeness in Phase 26.)* The per-add law shipped here is its other half.

---

## Phase 22 — Full-characterization, and the end-to-end DFS unconditional coverage  *(shipped)*

**The capstone of the sets/maps/cardinality arc: a cardinality-terminating DFS proves it reaches the node it
is given — unconditionally.** The last axiom is the converse of Phase 20's *full ⇒ count*:

```
Sets.boundedCount(s, k) == k   ⟺   ∀ i. 0 <= i < k ⟹ i ∈ s        (count is full  ⟺  s covers [0, k))
```

Both directions are theorems of "count of members in `[0, k)`" (`k` members in `k` slots iff every slot is a
member), so the encoder asserts the iff for every `Sets.boundedCount(s, k)` term (in `setCountOf`, alongside the
bound axiom), the membership `select(s, i)` serving as the universal's trigger. The bounded-coverage `forall`
is factored (`domainCoverageForall`) and shared with `Sets.boundedBy`.

**Direct facts (verified):** `Sets.boundedCount(s,k) == k ∧ 0 <= u < k ⊢ u ∈ s` (full count forces every domain node
in); the reverse `(0..<k).every{it∈s} ⊢ Sets.boundedCount(s,k) == k`; and the domain bite — `Sets.boundedCount(s,k) == k`
says nothing about a `u` **outside** `[0, k)` (refuted).

**The end-to-end result.** A DFS over a functional graph (`next : Map<Node,Node>`) marking a `Set<Node>`,
terminated by the **set-cardinality** measure `n - Sets.boundedCount(visited, n)`, proves `u ∈ visited`
**unconditionally** — no fuel budget:

```groovy
@Requires({ 0 <= u && u < n && (0..<n).every { 0 <= next[it] && next[it] < n } })
@Modifies({ this.visited })
@Decreases({ n - Sets.boundedCount(visited, n) })
@Ensures({ (u in visited) && (0..<n).every { !(it in old.visited) || (it in visited) } })
void visit(int u) {
    if (!(u in visited) && Sets.boundedCount(visited, n) < n) { visited.add(u); visit(next[u]) }
}
```

How the obligations close: **termination** — the per-add law (Phase 21) makes `Sets.boundedCount(visited, n)`
strictly increase on the fresh in-domain add, so the measure drops by one and the bound axiom keeps it `>= 0`;
**coverage** — on the guard-false branch the model either has `u ∈ visited` already, or `Sets.boundedCount(visited,n)
>= n`, where the bound forces `== n` and the full-characterization then forces every domain node (`u`
included) into `visited`; on the guard-true branch `u` is added and the inductive hypothesis's monotonicity
carries it across the recursion's havoc. It composes every prior phase — sets, the map graph, induction,
caller-side set framing, bounded quantifiers, the per-add law, the full-characterization — into one result.
*(One wrinkle the build surfaced: `Sets.boundedCount` in a method **body** resolves to a `ClassExpression`
(`verification.Sets.boundedCount`), not the `VariableExpression`/`PropertyExpression` a re-parsed contract carries, so
the encoder's `Sets` recognition was widened to all three.)*

**What remains — completeness.** The proof covers the node *itself*, **not its successors**: `next[u] ∈
visited` refutes (a node visited earlier needn't have had its edge followed). That is *completeness* — every
reachable node is visited, the closure fixpoint — and it needs the DFS **frontier/stack invariant** ("`visited`
is closed under successors except on the recursion stack"), which is not a simple inductive set property: it
needs the stack modelled (a sequence/ghost) or an explicit inductive `IsPath` predicate with a least-fixed-point
argument. That is the one named, well-understood gap between here and a fully verified DFS; everything else —
termination, soundness, and unconditional coverage — is done.

---

## Phase 23 — A run at completeness: closure ⇒ reachable, and the obstacles  *(superseded by 24/25/26)*

**Completeness — *every reachable node is visited* — is the closure fixpoint.** It factors into two halves:
(b) "`visited` closed under `next` ⟹ every reachable node is visited", and (a) "the DFS *establishes* closure".

**What is proved here.** Closure as the bounded universal
`(0..<n).every { !(it in visited) || (next[it] in visited) }` lets the **one-step** consequence of (b) verify:
a closed set covers the successor of any visited node (`closure ∧ u ∈ visited ⊢ next[u] ∈ visited`) — the
inductive *step*, discharged by instantiating the closure universal.

**What was blocked, and where each block closed.** Attempting the full proof surfaced three coupled obstacles,
all since shipped:
- **Recursive definitions in contracts** — the inductive iteration over a `chain(u, d)` needed its defining
  equation visible across the lemma boundary. **Phase 25** lands this (shared symbol + bounded-depth eq); the
  full (b) half — *closure ⇒ EVERY reachable node visited* — now verifies.
- **DFS *establishing* closure** — a plain `mark` breaks closure (the new node's successor isn't visited yet),
  so the invariant is "closed-except-on-stack", needing a recursion-stack ghost. **Phase 26** delivers the
  frontier/stack invariant.
- **Call-site soundness** — the run found that `verifyCallSite` wasn't replaying intervening body mutations
  before discharging a callee's precondition, so a naive closure-threading DFS spuriously passed; recursive-call
  name conflation and missing early-return narrowing were coupled to the fix. **Phase 24** rebuilds the
  call-site path (fresh formals + full-path replay) and re-validates the recursive proofs — including the
  Phase-14 sort, whose recursive precondition had been passing vacuously.

With 24/25/26, every correctness property of DFS — termination, soundness, unconditional coverage, completeness
(both halves) — is machine-checked.

## Phase 24 — Call-site precondition soundness  *(shipped)*

**A soundness fix to the foundation — and the one that revealed a flagship had been resting on a vacuous
check.** The discharge of a callee's `@Requires` at a call site (`verifyCallSite`) was building its context
from the enclosing `@Requires` and the enclosing-`if` path facts only. It missed two things, both unsound:

- **Intervening body mutations weren't threaded.** A precondition over a *mutated* collection's contents was
  checked at the method's *entry* state, not the state at the call. (Surfaced by the Phase-23 closure-DFS:
  `visit(next[u])`'s closure precondition was checked against the *pre-`add`* `visited`, so a naive
  closure-threading DFS passed spuriously.)
- **Recursive-call name conflation.** The callee formal and the caller's same-named variable were the same SMT
  constant, so a self-call's formal binding asserted the garbled `u == next[u]` (or the inconsistent `n == n-1`
  for `sumUp(n-1)`) — checking the precondition in a corrupt/vacuous context. Many recursive call-site
  preconditions were therefore passing *vacuously*.

**The fix (three coupled parts):**

1. **Fresh callee formals.** The formal is a fresh symbol (`name#arg…`, kept out of displayed counterexamples
   by the `#` filter), pinned to the actual — distinct from any caller variable of the same name.
2. **Early-return path narrowing.** An `if (cond) return/throw` that *precedes* the call (not an enclosing
   `if`, so `PathFacts` misses it) contributes `¬cond` — the fact `sumUp(n-1)`/`bcount(s,k-1)` need
   (`n ≠ 0`/`k ≠ 0`) to show `n-1 ≥ 0`.
3. **Precise intervening-mutation replay.** The straight-line prefix (scalar/field assigns, array stores, map
   puts, set add/remove) is replayed into the context, and **the actual arguments are translated *after* the
   replay** — so `insert(m-1, a[m], v)` reads the post-swap `a[m]`. A non-straight-line prefix statement
   (an `if`/loop) soundly *havocs* what it might write.

**Outcome.** The closure-DFS precondition now correctly refutes; a `s.add(k); needs(k)` (where `needs` requires
`k ∈ s`) verifies *because* the add is threaded, and refutes without it; `sumUp`/`bcount` recursive
preconditions now discharge *soundly* (early-return narrowing) rather than vacuously.

**What it revealed — and restored — the Phase-14 sort.** The fix exposed that the capstone sort's recursive
precondition `insert(m-1, a[m], v)` had been passing **vacuously** (the `m == m-1` conflation). The *sound*
obligation needs the *transitive* bound `a[it] <= a[m-1]` (for all `it`) from *adjacent* sortedness — which
Z3 cannot get by e-matching (it times out; the trigger cliff). So the call-site rebuild also generalised the
preceding-call rule: **any** preceding call's `@Ensures` is now assumed in path order (sound *because* the
intervening mutations are threaded), not just the immediate predecessor. With that, a one-line **monotone-bound
lemma** (`maxBound`: every element of an adjacent-sorted prefix `[0,k]` is `<= a[k]`, proved by induction)
called *before* the swap supplies the transitive bound, and its `@Ensures` threads through the swap to the
recursive call — discharging the precondition *soundly*. The sort is fully verified again. This is also the
project's first worked **lemma-as-instantiation-hint** (roadmap Phase 8b): a hard quantifier proof made
tractable by a user lemma, no engine change beyond the call-site threading.

**Still not threaded (sound, documented):** a call nested as an *argument* of another call has no path step to
anchor the replay, so it falls back to the conservative entry-state context.

## Phase 25 — Recursive definitions in contracts: the defining-equation upgrade  *(shipped)*

**The piece that lets an inductive proof reason about a recursive function — and the last addition needed for
the *closure ⇒ every reachable node visited* half of completeness.** Phase 8a's symbolic unfolding *inlined* a
pure function's body at the call site; for a *recursive* function appearing in a contract this produced
different inlined terms at different fuel depths, so two occurrences (a goal `chain(u,d)` and the inductive
hypothesis's `chain(next[u],d-1)`) could not be equated, and the induction refuted.

**The fix — shared symbol + defining equation.** A contract-free same-class call `f(args)` is now translated to
a *shared* uninterpreted symbol `f#(args)` (so two occurrences are the same term by congruence), and its
**defining equation** `f#(args) == body[params↦args]` is asserted (sound by the function's purity). The body's
own recursive calls become `f#(deeper)` terms with their own equations, so the definition unfolds *as
equations* over shared symbols rather than as inlined terms.

**The depth subtlety that made it work.** A naïve shared total unfold budget fails on an inductive function
whose argument *drifts* (`chain(u,d) → chain(next[u],d-1) → chain(next[next[u]],d-2) → …`): the body expansion
drains the whole budget before the goal term is ever defined. So the budget is **per-term depth**, restored
after each top-level call — the goal and the hypothesis each get their equation independently. Depth (6) still
reaches base cases, so the concrete unfolds (`pow2(2) == 4`) keep working.

```groovy
int chain(int u, int d) { d <= 0 ? u : chain(next[u], d - 1) }   // the d-step successor
@Requires({ d >= 0 && 0 <= u && u < n && (u in visited) &&
            (0..<n).every { 0 <= next[it] && next[it] < n } &&
            (0..<n).every { !(it in visited) || (next[it] in visited) } })   // closure
@Ensures({ chain(u, d) in visited })
@Decreases({ d })
void propagate(int u, int d) { if (d > 0) propagate(next[u], d - 1) }       // verified
```

**Payoff.** Two things land: the **completeness (b) half** — closure ∧ `u ∈ visited` ⇒ every node reachable
from `u` is visited, by induction over `chain` (Phase 23's open inductive case) — and **`bcount` cross-lemma
use**: a single-expression `bcount(s,k)` referenced in a *separate* lemma's contract, whose bound
`0 <= bcount <= k` is proved by induction using the defining equation (the cross-lemma use the statement-form
Phase-20 `bcount` couldn't support; a wrong bound still refutes). It is also the bounded, in-grain form of
"recursive-definition reasoning" — no quantified function axioms, just ground defining equations to a fixed
depth, keeping clear of the trigger cliff.

## Phase 26 — The frontier/stack invariant: DFS establishes closure  *(shipped)*

**The last gap, and the capstone of the whole sets→maps→cardinality→completeness arc: a depth-first search
proven to leave its `visited` set *closed under the successor relation* — i.e. it reaches everything reachable.**
This is the deep half of DFS correctness, the one that needs the recursion *frontier* modelled, not just an
inductive set property.

**Why a plain invariant fails.** Mark-then-recurse marks `u` *before* recursing into `next[u]`, so right after
the mark `visited` is closed **except at `u`** (whose successor isn't visited yet); the recursion restores it.
A plain "closed under `next`" invariant therefore provably breaks on a single `mark` (Phase 23's boundary test).
The invariant DFS really maintains is **closed-except-on-stack**.

**The encoding — the stack as a `Set` ghost.** A second set field `onStack` is pushed (`onStack.add(u)`) before
the recursive call and popped (`onStack.remove(u)`) after. The invariant is
`∀ it ∈ [0,n). it ∈ visited ⟹ (it ∈ onStack ∨ next[it] ∈ visited)` — every visited node is on the stack or its
successor is visited. `visit` is proven to **maintain it and restore the stack** (the `@Ensures` includes a
pointwise *stack-restored* clause `(it in onStack) == (it in old.onStack)` and `onStack ⊆ visited`), so a
top-level `dfs` started with both sets empty leaves `onStack` empty — at which point the invariant *is* full
closure `∀ it. it ∈ visited ⟹ next[it] ∈ visited`.

```groovy
@Modifies({ [this.visited, this.onStack] })
@Decreases({ n - Sets.boundedCount(visited, n) })
void visit(int u) {
    if (!(u in visited) && Sets.boundedCount(visited, n) < n) {
        visited.add(u); onStack.add(u); visit(next[u]); onStack.remove(u)   // mark, push, recurse, pop
    }
}
// from empty visited + empty stack, one DFS ⇒ visited is closed under next:
@Ensures({ (0..<n).every { !(it in visited) || (next[it] in visited) } })
void dfs(int start) { visit(start) }
```

**How the obligations close.** The proof composes *everything*: the **pop** after the recursive call is threaded
by Phase 24's call-site/mutation machinery; the recursion **havocs both sets and reframes** them from `visit`'s
`@Ensures` (sound `@Modifies` over two sets); the **stack-restored** clause lets the pop cancel the push
(`u ∉ onStack` follows from `onStack ⊆ visited` and `u ∉ visited`); `u ∈ visited` (needed so the recursion
covers `next[u]` in the invariant's `it == u` case) rides the **`Sets.boundedCount` full-characterization** (Phase 22)
on the "set full" branch; and termination is the **set-cardinality measure** (Phase 16). No new engine
machinery — it is the entire stack of phases 16–25 brought to bear on one proof.

**Cost.** This is the heaviest proof in the suite — several quantifiers over two mutated sets with map-indexed
bodies, plus the defining-equation overhead (Phase 25). It stays within the per-VC timeout (no UNKNOWNs), but
the suite's wall-clock grew noticeably; a tighter unfold depth, VC caching, or per-VC tactic selection (the
cross-cutting compilation-slowdown item) is the natural optimisation now that the capability is proven.

**The arc is complete.** Termination (16/17), soundness + bounded progress (18), the cardinality axiom (19),
bounded-sum cardinality and its laws (20–22), unconditional coverage (22), recursive-defs in contracts (25),
call-site soundness (24), and now closure (26): **a depth-first search over a cyclic graph, every correctness
property machine-checked, by induction, with no loops** — the goal this whole line of work was aimed at.

## Phase 27 — Non-Int element domains: `String` and `Enum` in sets, maps, lists  *(shipped)*

**Real-world Groovy uses string keys and enum-typed fields; the engine was Int-only until now.** Sets,
maps, and lists modelled their elements as `Int` — fine for the DFS over a finite node domain that
Phases 16–22 built up, but `Set<String>`, `Map<String, V>`, `List<Color>` (the everyday shapes) were
out of fragment. This phase lifts the element-sort assumption: any literal of a recognised non-Int
element type lowers to a constant of that type's Z3 uninterpreted sort, and all the existing
operations (`contains`/`add`/`size`/`put`/`get`/subscript read+write) thread through that sort
untouched.

**The encoding — uninterpreted sorts plus pairwise distinct.** Each non-Int element type maps to a Z3
uninterpreted sort (`String!Sort`, `Color!Sort`, …), declared once per name and shared across the
session. A literal (`"admin"`, `Color.RED`) mints a constant of that sort, interned by literal text;
on each new mint, the constant is asserted distinct from every previously-minted literal of the same
sort. So `s.contains("admin")` and `s.contains("guest")` resolve to two different `(select s _)`
queries — `contains("admin")` doesn't entail `contains("guest")` (refutes, with the
counterexample-as-Groovy-literal renderer showing `f("admin")` in `fails on:`). Two enums with the
same source-level simple name in different outer classes collapse into one sort — accepted limit.

**Cross-AST-shape consistency.** A contract closure is re-parsed from text, so `Color.RED` arrives as
`PropertyExpression(VariableExpression("Color"), "RED")`. The method body is post-resolution, so the
same `Color.RED` arrives as `PropertyExpression(ClassExpression(C$Color), "RED")` — the nested-enum
binary name `C$Color` diverges from the source-level `Color`. Two normalisations make them converge:
the enum sort name is the simple name with any `$`-prefix stripped (so `C$Color` → `Color`), and the
literal-key interning uses the property name alone (`"RED"`) — the expected sort already
disambiguates cross-enum (`Suit.RED` vs `Color.RED` reach different sorts).

**`Set<E>` / `Map<K,V>` / `List<E>` routing** — `VerifyChecker` extracts the element/key/value types
from declared generics in `beforeVisitMethod` (`collectSetElementTypes` / `collectMapTypes` /
`collectListElementTypes` / `collectScalarTypes`) and hands them to the `Encoder`. The encoder's
array allocator `arrayFor` now dispatches on `[keySort, valueSort]` — a map value array becomes
`Array KeySort -> ValueSort`, a non-Int list `Array Int -> ElemSort`. The set characteristic array
likewise: `Array ElemSort -> Int`. Per-element-sort `card$T` / `bcount$T` functions are declared
lazily on the backend so cardinality works for `Set<String>` the same way it does for `Set<Integer>`.

**`Sets.boundedBy(s, n)` / `Sets.boundedCount(s, k)` are Int-only here, generalised in Phase 29.** Both
originally depended on the `[0, n)` Int-domain structure (the lowering is a bounded membership
universal over Int indices). For non-Int element sets they returned null and the standard "outside
fragment" skip diagnostic fired. Phase 29 below generalises them to enum-element sets when
`n`/`k` matches the enum's domain size — the bounded-universal coverage becomes a finite
conjunction over the enum's constants. The String case still skips (strings have no finite
domain).

**Counterexample rendering.** A refuting String/Enum parameter's model value is recovered by
checking equality-under-the-model against each interned literal of the same sort (Z3 may assign a
synthetic uninterpreted-sort constant instead of one of our minted ones — string-name matching
alone misses these cases). The repro is rendered as a Groovy literal: `f("admin")` for String,
`f(Color.RED)` for Enum.

```groovy
class C {
    enum Color { RED, BLUE, GREEN }
    Set<Color> palette
    @Requires({ !(Color.RED in palette) })
    @Modifies({ this.palette })
    @Ensures({ palette.size() == old.palette.size() + 1 })
    void useRed() { palette.add(Color.RED) }
}
```

Verifies. Drop the freshness `@Requires` and the `+ 1` refutes with `fails on: useRed()` — a
no-op-add is one model.

**Known limits at the time of this phase** (most since closed). Set algebra (union/intersection/
subset) and `Map<K, Set<V>>` nesting both shipped later — see Phases 30/31/33/35 and Phase 36.
What still skips honestly today: non-Int element domains other than String and Enum (records,
value classes, arbitrary objects) fall through to the default-Int path. The
`Sets.boundedBy`/`Sets.boundedCount` Int-only restriction from this phase was lifted in Phase 29
for the enum case.

## Phase 28 — `EnumClass.values().length` folds to a ground int  *(shipped)*

**A small piece of normalisation that unlocks ground state-coverage proofs.** `Color.values().length`
(and the equivalent `.size()` method form) is a syntactically uniform way to spell an enum's domain
size, but it reached the encoder as a `MethodCallExpression` whose return type isn't modelled — so
contracts like `@Requires({ k < Color.values().length })` skipped as outside fragment. This phase
folds the expression to its literal value at translate time, the same accelerator pattern as
Phase 8a's closed-constant evaluation, scoped narrowly to the one shape.

**How it works.** Both AST shapes are recognised:

- **Post-resolution body**: `PropertyExpression(MethodCallExpression(ClassExpression(Color),
  "values", []), "length")` — the encoder has direct access to the `ClassNode`, counts enum
  constants by walking the type's fields and filtering on the JVM {@code ACC_ENUM} modifier bit
  (`0x4000`), emits an `intLit`.
- **Re-parsed contract**: `PropertyExpression(MethodCallExpression(VariableExpression("Color"),
  "values", []), "length")` — the receiver name has no resolved type, so `VerifyChecker` walks the
  declaring class's module in `beforeVisitMethod`, builds a `Map<String, Integer>` of enum simple
  names → constant counts (both the source-level `Color` key and the inner-class-stripped form for
  nested enums), and hands it to the encoder.

The `ACC_ENUM` filter is the load-bearing detail: Groovy synthesises additional same-typed
`MIN_VALUE` and `MAX_VALUE` fields on every enum, so counting "static fields whose declared type
matches the enum class" would inflate a 3-constant `Color` to 5. The JVM modifier flag is set only
on real enum constants.

```groovy
class C {
    enum Color { RED, BLUE, GREEN }
    @Ensures({ result == 3 })
    static int numColors() { Color.values().length }                          // verifies
    @Requires({ k < Color.values().length })
    @Ensures({ k <= 2 })
    static int safe(int k) { k }                                              // verifies
    @Ensures({ result == 4 })                                                  // refutes
    static int wrong() { Color.values().length }
}
```

**What it unlocks (and what it doesn't).** The folded literal is usable anywhere an `int` literal is
— upper bound of a bounded range (`(0..<Color.values().length).every { … }`), `Sets.boundedBy(s, n)`
over an Int-element set, ground constraint in a postcondition. Phase 29 below additionally uses
the folded count to enable `Sets.boundedBy` / `Sets.boundedCount` over a `Set<Color>` (the FSM
completeness shape). What this phase *doesn't* give on its own: recognition of enums defined in
*other* modules (only the current module's enums are walked). Cross-module enum support would
extend `collectEnumDomainSizes` to consult the compilation unit's classloader; the foundation is
there.

## Phase 29 — `Sets.boundedBy` / `Sets.boundedCount` generalised to enum-element sets  *(shipped)*

**The "FSM proves every state handled" example, with the natural `Set<State>` spelling.** Phase 27
step 8 honestly skipped `Sets.boundedBy` / `Sets.boundedCount` on non-Int element sets — the bounded
universal `∀ i. 0<=i<n ⟹ i ∈ s` is meaningless when `s`'s elements aren't Int. For enums, the
finite domain gives a clean substitute: enumerate the constants, write the coverage as a finite
conjunction. This phase wires that, and lets the natural FSM completeness proof verify directly.

**The encoding.** On first mint of an enum-element set (`setFor` returning a fresh handle), two
facts the finite enum domain gives are asserted unconditionally:

- **Pigeonhole**: `card(s) <= N` where N is the enum's constant count.
- **Full-coverage iff**: `card(s) == N ⟺ c1 ∈ s ∧ … ∧ cN ∈ s` — finite conjunction over the
  enum's constants (the same interned literals Phase 27 already mints).

`Sets.boundedBy(s, n)` and `Sets.boundedCount(s, k)` then dispatch on element sort. For Int: the existing
Phase 19 / 22 machinery (bounded universal). For enum, when `n`/`k` folds to the enum's domain
size (via Phase 28's `EnumClass.values().length` recognition or a literal): `Sets.boundedBy(s, n)`
lowers to `card(s) <= n ∧ (card(s) < n ∨ finite-conjunction)`, and `Sets.boundedCount(s, k)` aliases to
`card(s)` (no partial-domain ordering on an enum, so the only meaningful count is the whole-set
size). Non-matching `n`/`k` skips with the standard "outside fragment" diagnostic — the
restriction is the partial-domain ambiguity, not the element sort.

```groovy
class FSM {
    enum State { IDLE, RUNNING, DONE }
    Set<State> handled
    @Requires({ Sets.boundedCount(handled, State.values().length) == State.values().length })
    @Ensures({ State.IDLE in handled && State.RUNNING in handled && State.DONE in handled })
    boolean allHandled() { true }
}
```

Verifies. `State.values().length` folds to `3` (Phase 28), `Sets.boundedCount(handled, 3)` aliases to
`card(handled)` (Phase 29), the iff axiom `card(handled) == 3 ⟺ IDLE ∈ handled ∧ RUNNING ∈ handled
∧ DONE ∈ handled` was asserted at the set's first use, so `@Requires` ⟹ `@Ensures`. Drop the
`@Requires` and the postcondition rightly refutes — partial coverage can't prove every state.

**Pigeonhole is automatic.** A method whose postcondition is `s.size() <= 3` over a `Set<State>`
verifies *without* requiring `Sets.boundedBy` — the bound was asserted at setFor time. Same for the
implication "this set has at most as many elements as its enum has constants" anywhere it's
needed.

**Known limits at the time of this phase.** Subset, set union/intersection, materialised sets,
and `Map<K, Set<V>>` nesting all shipped in subsequent phases — see Phases 30/31, 33, 35, 36.

## Phase 30 — Subset reasoning: `s.containsAll(t)` over enum-element sets  *(shipped)*

**The canonical authorization predicate, machine-checked.** `granted.containsAll(required)`
expresses subset directly — "every role required is among the granted" — and is the building block
for set equality, ACL checks, FSM coverage transfer, and the membership half of union/intersection
later. This phase adds it for enum-element sets, where the finite domain gives a clean lowering
without any unbounded universal.

**The encoding.** `s.containsAll(t)` lowers to the finite conjunction
`(c1 ∈ t ⟹ c1 ∈ s) ∧ … ∧ (cN ∈ t ⟹ cN ∈ s)` over the enum's constants — the same shape Phase 29
uses for full-coverage, with implication instead of bare membership. Reflexivity, transitivity, and
the "add preserves subset" pattern all fall out of the conjunction structure under Z3's
propositional reasoning; no quantifier needed.

```groovy
class C {
    enum Role { ADMIN, USER, GUEST }
    @Requires({ granted.containsAll(required) && Role.ADMIN in required })
    @Ensures({ Role.ADMIN in granted })                         // verifies — subset entails transfer
    static int check(Set<Role> granted, Set<Role> required) { 0 }
}
```

Drop the `containsAll` precondition and the `@Ensures` refutes — without subset, membership in
`required` says nothing about `granted`.

**Enhancement: empty iff.** The Phase-29 enum-set axioms covered `card(s) == N ⟺ full coverage`
but not the dual at the empty endpoint. Phase 30 adds the third axiom:
{@code card(s) == 0 ⟺ ¬c1 ∈ s ∧ … ∧ ¬cN ∈ s}, asserted at every enum set's first mint
alongside the pigeonhole and full-coverage iff. So `s.size() == 0` now implies every constant is
absent — letting empty-subset claims (`s.containsAll(empty)`) verify by vacuous implication, and
"this method clears the set" postconditions imply non-membership of every constant.

**Known limits at the time of this phase** (since closed). Phase 31 lifts the Int-element
subset restriction by threading a registered `Sets.boundedBy(t, n)` into the subset lowering;
Phase 32 adds `s.equals(t)` as a two-direction composition; Phases 33 and 35 add inline and
materialised set union/intersection.

## Phase 31 — Int-element subset via bounded-domain context  *(shipped)*

**Closes the Int-side of subset.** Phase 30 lowered `s.containsAll(t)` over enum-element sets to a
finite conjunction — the finite domain made it ground. For Int-element sets the user has to
supply the domain via a `Sets.boundedBy(t, n)` clause; once they do, the subset lowering becomes
the natural bounded universal `∀i. 0 <= i < n ⟹ (i ∈ t ⟹ i ∈ s)`. Same shape Phase 19 / 22
already lean on, applied to a new predicate.

**The plumbing — `intSubsetBounds`.** A per-encoder map (set-key → bound handle) is populated as
a side-effect of `translateSetsBounded`'s Int branch: when `Sets.boundedBy(t, n)` translates, it
records `t`'s key with `n`'s Z3 handle. A later `s.containsAll(t)` on Int sets consults this map;
if a bound is registered, it emits the bounded universal with `(select t i)` and `(select s i)`
as triggers. Without a bound (`Sets.boundedBy` not in scope, or `containsAll` translated *before*
the bound clause in L-to-R AST order), the lowering returns null and the standard "outside
fragment" skip diagnostic fires.

```groovy
class C {
    @Requires({ Sets.boundedBy(required, n) && granted.containsAll(required) &&
                0 <= u && u < n && u in required })
    @Ensures({ u in granted })
    static int check(Set<Integer> granted, Set<Integer> required, int n, int u) { 0 }
}
```

Verifies. Reflexivity and transitivity over Int sets (with a shared bound) both go through the
same way enum subset did in Phase 30. The bound *must* be on the subset operand (`t`), not the
superset — the universal needs to range over `t`'s candidate elements.

**Ordering caveat.** Because the bound is populated by side-effect when `Sets.boundedBy(t, n)`
translates, a contract written `@Requires({ a.containsAll(t) && Sets.boundedBy(t, n) })` (subset
first, bound after) skips — at the time `containsAll` is translated, the bound isn't yet
registered. Writing the bound first (`Sets.boundedBy(t, n) && a.containsAll(t)`) works. Not a
soundness issue (skip is honest), but a UX quirk worth knowing.

## Phase 32 — `m.containsValue(v)` for enum-keyed maps + `s.equals(t)` for sets  *(shipped)*

**Two small completions on top of the subset machinery.** `m.containsValue(v)` and `s.equals(t)`
were the next items in the deferred set/map algebra row; both are small enough to ship together,
both compose with what's already there.

**32a — `m.containsValue(v)` for enum-keyed maps.** The existential mirror of Phase 30's finite
conjunction: lower to `(m[c_1] == v) ∨ … ∨ (m[c_N] == v)` over the enum's key constants. The
value is translated in the map's value sort (Int / String / Enum all work). Int-keyed and
String-keyed maps skip honestly — no finite key domain to enumerate.

```groovy
class Registry {
    enum State { IDLE, RUNNING, DONE }
    Map<State, Integer> errorCodes
    @Requires({ errorCodes[State.RUNNING] == 42 })
    @Ensures({ errorCodes.containsValue(42) })
    boolean hasError42() { errorCodes.containsValue(42) }
}
```

Verifies: the key-pinned `[State.RUNNING] == 42` makes the `RUNNING` disjunct true, and the
disjunction holds. Drop the `@Requires` and the postcondition rightly refutes.

**32b — `s.equals(t)` for sets, by subset composition.** Pure composition, no new theory:
`s.equals(t) ≡ s.containsAll(t) ∧ t.containsAll(s)`. Reuses the Phase 30/31 subset lowering in
both directions. Works for any element sort the subset path handles (enum: always; Int: with
mutual `Sets.boundedBy` bounds). Both directions need to translate; if either skips, equals does too.

Reflexivity (`s.equals(s)`) is automatic. The diagnostic-form alternative to writing `s == t`
directly — which would lower to Z3's array-equality predicate (an unbounded universal on the
characteristic functions). The method-form path gives the user a propositionally-decomposed
alternative Z3 reasons about as ground facts.

**Known limits.** Int-keyed map `containsValue` would need a key-set bound (similar to Phase 31's
`intSubsetBounds`) and isn't yet wired. `s.equals(t)` for Int sets without mutual bounds skips.

## Phase 33 — Inline set union / intersection  *(shipped)*

**The last set-algebra slice the deferred row called out, in its tractable form.** A user writing
`(a + b).contains(x)` or `a.intersect(b).containsAll(u)` in a contract gets the natural lowering
without the encoder having to mint a new set handle for the binary operation's result. The result
is treated as a *predicate context* — every method called on it lowers lazily by chaining through
to the operands.

**The encoding — lazy at the use site.** Recognised receiver shapes:
- {@code (s + t)} — Groovy's {@code Set.plus} binary expression (BinaryExpression with PLUS op).
- {@code s.intersect(t)} — Groovy GDK method-form intersection (MethodCallExpression).

Both must be two known set names with matching element sort; otherwise honest skip. Methods on
the result lower:
- {@code .contains(x)}: union → {@code x ∈ s ∨ x ∈ t}; intersection → {@code x ∈ s ∧ x ∈ t}.
- {@code .containsAll(u)} (enum element sort): finite conjunction over the enum's constants —
  {@code (c ∈ u ⟹ c ∈ s ∨ c ∈ t)} for union, {@code (c ∈ u ⟹ c ∈ s ∧ c ∈ t)} for intersection.
- The {@code x in (s + t)} / {@code x !in s.intersect(t)} membership operator forms route through
  the same lowering — mirror of the method-form path.

```groovy
class C {
    enum Role { ADMIN, USER, GUEST }
    @Requires({ a.containsAll(u) })                   // a covers u
    @Ensures({ (a + b).containsAll(u) })              // the union covers u — adding b only helps
    static int f(Set<Role> a, Set<Role> b, Set<Role> u) { 0 }
}
```

Verifies via the finite conjunction. Drop the @Requires and the @Ensures rightly refutes — without
a covering u from either operand, the union claim doesn't hold.

**Known limits.**

- **Materialised set assignment** — `Set<X> u = a + b` as a fresh first-class set — *closed by
  Phase 35*.
- **`.size()` on a union/intersection** — out of scope. Needs inclusion-exclusion
  `|s ∪ t| = |s| + |t| − |s ∩ t|` to be useful; the uninterpreted `card` has no axiom relating
  cards of derived sets. Skip honestly.
- **Int-element `containsAll` on a binop receiver** *(now shipped)* — extends Phase 31's
  `intSubsetBounds` to the binop face: `(a + b).containsAll(u)` and a materialised `Set<Integer> u = a + b`
  lower to a bounded universal over `[0, n)` from a prior `Sets.boundedBy`, the dual of the enum
  finite-conjunction. `u` inherits an operand bound where provable, so subsequent subset chains.

**Update — full four-op algebra (shipped).** `setBinopFor` now also recognises **difference** (`a - b`) and
**symmetric difference** (`a ^ b`, Groovy's `BITWISE_XOR` on sets) beside union (`+`) and intersection
(`.intersect`), plus Groovy's bitwise-operator aliases **`a | b`** (union, `BITWISE_OR`) and **`a & b`**
(intersection, `BITWISE_AND`). All four are one membership combine — `setCombineMembership`: `∨` / `∧` / `a∧¬b` / `xor` —
slotted into every set face: pointwise `x in (a op b)` (any element sort), `(a op b).containsAll(u)`, and a
materialised `Set u = a op b` (Int over a `Sets.boundedBy` bound, enum over the finite domain). Bound
inheritance is per-op: intersection ⊆ either operand, difference `a\b` ⊆ a, union/symdiff ⊆ a∪b (needs both
operands bounded by the same n). Pointwise membership needs no bound (`x∈(a^b) ⟺ x∈a xor x∈b` is per-element).
Locked by the `set algebra` tests. **Still out:** `.size()` of a derived set (inclusion-exclusion, above).

## Phase 34 — VC cache  *(shipped)*

**The first pure-engineering phase.** No new capability, no new contract surface — a *cross-cutting
risk* the project flagged from the start ("compilation slowdown — Z3 calls take 10–100 ms each;
mitigations: cache VCs by `(signature, path-condition hash)`"). The mitigation is now in.

**The encoding.** Two VC checks built from the same set of asserted Z3 expressions — compared
structurally via {@code Expr.toString()}, with the asserted-set sorted to a canonical order, and
prefixed with the solver timeout to keep hard-UNKNOWN results from leaking across configurations
— must produce the same {@code CheckResult}, by Z3's determinism. {@code Z3Backend} now keeps a
process-wide {@code ConcurrentHashMap<String, CheckResult>} consulted at the top of
{@code Z3Session.check()}: hit → return immediately; miss → solve, cache, return.

```groovy
@Override
CheckResult check() {
    String key = vcKey()
    CheckResult cached = Z3Backend.vcCache.get(key)
    if (cached != null) { Z3Backend.recordVCCacheHit(); return cached }
    Z3Backend.recordVCCacheMiss()
    CheckResult result = computeCheck()
    Z3Backend.vcCache.put(key, result)
    return result
}
```

**Soundness.** A cached {@code CheckResult} carries only {@code String} → {@code Long} /
{@code String} maps — no Z3 handles — so the counterexample re-renders correctly in any future
session that declared the same source-level names. Sorts are differentiable inside the assertion
text (an {@code Int} {@code n} and a {@code String} {@code n} would always appear inside
operations that disambiguate them; their {@code toString} differs), so cross-sort name aliasing
can't cause unsound conflation.

**The result.** Test suite drops from **31.5 s to 25.8 s** (–18 %) at 253 cases, with **94 hits
/ 359 misses ≈ 20.8 % hit rate** — the misses are the ~1.4 distinct VCs each test contributes to
the cache for the first time; the hits are the precondition / bounds / null check obligations
that recur across the suite. Set {@code VERIFY_CACHE_STATS=1} to surface the counters.

**Known limits.** Two VCs that are *logically* equivalent but *syntactically* different (e.g.
{@code a + b} vs {@code b + a}, {@code a ∧ b} vs {@code b ∧ a} inside a single conjunct) miss the
cache. A canonicaliser would lift hit rates further at the cost of an extra normalisation pass
per assertion; not pursued today. The cache is also process-wide rather than persisted — each
{@code ./gradlew verify} rebuilds it from scratch. Persistent caching keyed on the project's
class-file digests is a much larger phase (file-system layout, invalidation on dependency
upgrades, cross-machine reproducibility) and the in-memory wins were already worthwhile alone.

## Phase 35 — Materialised set ops  *(shipped)*

**Lifts Phase 33's predicate form to a value form.** Phase 33 lowered {@code (a + b).contains(x)}
and friends *at the use site* — no new set handle minted, the binop stayed a predicate context.
Phase 35 takes the next step: an *assignment* whose RHS is a set union or intersection mints a
fresh set handle for the left-hand side, with the full per-element membership iff relating it to
its operands. Every existing set capability — subset, equals, cardinality update laws on
subsequent mutations, the enum-domain pigeonhole / full-coverage iff / empty iff axioms — picks
up the new local automatically.

**Detection.** The body's {@code DeclarationExpression} already becomes an {@code Assign} step in
{@code BodyEncoder}. The new branch in {@code VerifyChecker}'s {@code Assign} handler runs
{@code Encoder.tryMaterialiseSetBinopAssign(name, rhs)} *before* the int-SSA path. The encoder
reuses Phase 33's {@code setBinopFor} (now also unwrapping an outer {@code CastExpression}, so
{@code Set<Role> u = a.intersect(b) as Set<Role>} — needed because Groovy's GDK
{@code Collection.intersect} returns {@code Collection}) — and on a match commits:

```groovy
setElementTypes.put(name, binop.elemType)   // u becomes a "known set" downstream
Object uH = setFor(name)                     // mint the handle (auto-asserts enum-domain axioms)
for (String c : enumConstantNames(elemType)) {
    Object inU = member(uH, lit(c))
    Object inA = member(setFor(binop.leftKey),  lit(c))
    Object inB = member(setFor(binop.rightKey), lit(c))
    Object rhs = binop.isUnion ? or([inA, inB]) : and([inA, inB])
    session.assertExpr(eq(inU, rhs))         // c ∈ u ⟺ c ∈ a OP c ∈ b
}
```

**Why this composes for free.** Because {@code u} is registered in {@code setElementTypes}, the
encoder's existing {@code setFor(name)} machinery — which auto-asserts pigeonhole
({@code card(u) ≤ N}), full-coverage iff, and empty iff for enum-element sets — fires on the
mint. Everything downstream that already reasons about set parameters and fields
({@code u.containsAll(z)}, {@code u.equals(v)}, {@code Sets.boundedCount(u, k)}) now reasons
about {@code u} the same way; there's no special "materialised set" path elsewhere in the
codebase. The membership iff is the *only* extra fact Phase 35 emits.

```groovy
class C {
    enum Role { ADMIN, USER, GUEST }
    @Requires({ Role.ADMIN in a })
    @Ensures({ result == 1 })
    static int f(Set<Role> a, Set<Role> b) {
        Set<Role> u = a + b
        Role.ADMIN in u ? 1 : 0     // provable: the iff makes ADMIN ∈ u true under @Requires
    }
}
```

Verifies. Drop the @Requires and the else-branch becomes feasible (no constraint forces ADMIN
into either operand), so {@code result == 1} rightly refutes.

**Known limits.**

- **Enum-element domain only.** Int-element and uninterpreted-sort set binops would need an
  unbounded universal with trigger on {@code select(u, x)} — pulls in quantifier reasoning for
  every downstream membership query, deferred (parallels Phase 33's Int-binop {@code containsAll}
  known limit).
- **First assignment only.** A reassignment {@code u = a + c} after the original
  {@code u = a + b} isn't supported — the materialise path is the *declaration* form. Groovy
  rarely reassigns local sets, so this hasn't hurt in practice.
- **Cast handling stops at the outer expression.** A nested cast inside one of the operands —
  e.g. {@code (a as Set) + b} — works because the outer expression is the {@code +} binop, but a
  cast wrapping the whole thing on the *right* hand side is the only cast we unwrap. Reasonable
  given the GDK signature it's there to satisfy.
- **No inclusion-exclusion.** {@code card(u) = card(a) + card(b) − card(a ∩ b)} for a union is
  still out (Phase 33's known limit on {@code .size()} of a binop). The enum-domain pigeonhole
  upper bound + full-coverage iff usually suffice for FSM-shape proofs that care about
  *coverage*, not exact size.

### Phase 35b — set-binop *returns* bind `result`  *(shipped)*

A method that **returns** a set binop — `static Set<Integer> common(a, b) { a & b }` — can now spec its
`result` member-by-member. The materialised form (Phase 35) needs a bound or enum domain for its universal;
this reuses the cheaper *inline* point-wise membership instead. When binding `result` (the same site that
records a list/tuple/map factory return, Phase 78), `tryRecordSetBinopAssign` records `result → (a & b)` in
`setBinopDefs`, and `setBinopFor` resolves a variable through that map — so `x in result` folds exactly like
the inline `x in (a & b)`, at *any* element. Characterise with a symbolic param: `@Ensures({ (p in result)
== (p in a && p in b) })` proves for every `p` (it's an unconstrained parameter). Works for a direct binop
return and a materialised-local return (`Set u = a & b; u`). Co-shipped: `setBinopFor` learned the **method**
spellings of the operators — `a.and(b)`/`a.or(b)`/`a.xor(b)`/`a.minus(b)` join `a & b`/`a.intersect(b)` (a
`Set`-typed result wants these or the operators, since the GDK `intersect` returns a `Collection`). Sound —
a return of `a | b` under an intersection `@Ensures` refutes. Tests: `P35b set return`.

## Phase 36 — Map&lt;K, Set&lt;V&gt;&gt; nesting (read-only)  *(shipped)*

**The final row-2 deferred item: nested element domains.** A {@code Map<K, Set<V>>} reads as one
SMT array whose *value sort is itself an array sort* — the inner set's characteristic function.
Z3's array theory has always supported this: {@code Array<K, Array<V, Int>>} is a perfectly
ordinary sort. What was missing was the Groovy/encoder plumbing: until Phase 36, the value-type
extraction in {@code twoGenericsOrInt} returned {@code Set} (the raw outer-level type), the
encoder defaulted to {@code Int} as the value sort, and any subsequent {@code m[k].contains(x)}
hit "outside fragment" because {@code m[k]} was being typed as a scalar.

**The encoding — value sort lifted to an array.** A new {@code SmtSession.arraySort(key, val)}
returns a Z3 sort *without* minting a constant (the existing {@code arrayVarOfSort} mints; we
need just the sort to compose nested sorts). Two new collect passes:

```groovy
// VerifyChecker
currentNestedSetValueTypes = collectNestedSetValueTypes(node)   // Map<String, ClassNode>: mapName → V
```

drive a small change in {@code Encoder.mapValueSort}:

```groovy
ClassNode nestedElem = nestedSetValueTypes.get(name)
if (nestedElem != null) {
    return session.arraySort(sortFor(nestedElem), session.intSort())
}
// existing: sortFor(pair[1])
```

so the map's value array now mints as {@code Array<K, Array<V, Int>>} — and {@code select(map, k)}
yields a transient inner-set term that the existing {@code member}/{@code select} machinery
already handles.

**The dispatch.** A new {@code nestedSetReceiverFor(Expression)} recognises {@code m[k]} for a
known nested-set map, resolving it to {@code select(mapValsFor(m), translatedKey)} packaged with
the inner element sort and {@link ClassNode}. Both {@link #translateMethodCall} (for
{@code .contains}/{@code .containsAll}) and {@link #translateBinary} (for the {@code in} /
{@code !in} operator) consult it before falling through to the existing receiver shapes:

```groovy
// translateMethodCall
NestedSetReceiver nr = nestedSetReceiverFor(recv)
if (nr != null) {
    if (m == 'contains') return member(nr.innerSet, translateInSort(args.get(0), nr.innerElemSort))
    if (m == 'containsAll') return translateNestedContainsAll(nr, args.get(0))
    return null
}
```

{@code translateNestedContainsAll} is a finite conjunction over V's enum constants — structurally
the same shape as Phase 30's {@link #translateContainsAll}, but operating on a transient inner-set
term instead of a named handle.

```groovy
class C {
    enum Role { ADMIN, USER, GUEST }
    @Requires({ m[Role.ADMIN].containsAll(s) && Role.USER in s })
    @Ensures({ Role.USER in m[Role.ADMIN] })
    static int f(Map<Role, Set<Role>> m, Set<Role> s) { 0 }
}
```

Verifies. The finite conjunction over {@code Role} constants closes the gap between
"{@code m[ADMIN]} covers {@code s}" and "{@code USER} is in {@code m[ADMIN]}" once
{@code USER ∈ s} is in scope.

**Known limits.**

- **Read-only.** {@code m[k] = newSet} (replacing the whole set at a key) and {@code m[k].add(x)}
  (in-place inner-set mutation) are out. The former needs the existing map-put plumbing to thread
  array-valued stores; the latter needs SSA on a *transient* inner handle plus the per-mutation
  cardinality law. Together they're a separate ~3-day phase.
- **No `m[k].size()`.** Cardinality of a transient inner set would need to mint a named handle on
  the fly so {@link SmtSession#setCard} could apply — out of scope; skips honestly.
- **`m[k].containsAll(s)` over Int-element inner sets.** Would need Phase 31's
  {@code intSubsetBounds} applied to a transient receiver — parallels the Phase-33-known-limit
  for Int-binop {@code containsAll}; not yet wired. Enum-V inner sets are the only path today.
- **One layer of nesting.** {@code Map<K1, Map<K2, Set<V>>>} (three-level nesting) isn't
  recognised: {@code collectNestedSetValueTypes} introspects only one level deep. Genuinely
  rare; not pursued.

## Phase 37 — List element nullability  *(shipped)*

**The row-1 nullability slice.** Until Phase 37, {@code xs[i].method()} and
{@code xs.get(i).method()} silently passed — the implicit-NPE pass recognised only *named*
receivers ({@code recv.method()}), so an unguarded dereference into a list element was outside
the obligation set. Phase 37 closes that: every indexed-element dereference is now an
unconditional obligation against a per-element nullity oracle, discharged by a contract guard
or an in-body {@code if} check.

**The encoding.** A new
{@code Encoder.elementNullityFor(name)} returns a lazily-minted {@code Array<Int, Int>} keyed
{@code <name>$nullElem} — the now-familiar 1/0 characteristic-array shape that {@link Sets} and
the map key-set already use. The lowering is symmetric on both faces:

- **Contract face.** {@code xs[i] == null} / {@code null == xs[i]} (and {@code xs.get(i) == null}
  shape) translate to {@code select(xs$nullElem, i) == 1}; the {@code !=} mirrors negate. So a
  {@code @Requires({ xs[i] != null })} pins {@code select(xs$nullElem, i) == 0} in the path
  context.
- **Body face.** The {@code ObligationCollector} now emits a {@code DerefSite} for
  {@code xs[i].method()} / {@code xs.get(i).method()} shapes (recognised by
  {@code Encoder.indexedAccessTarget}, the same helper the contract face uses) carrying the
  index expression alongside. The discharge asserts the negation
  ({@code select(xs$nullElem, i) == 1}) and Z3 returns SAT exactly when the element *can* be
  null on this path — refuted, with the counterexample rendered as e.g. {@code fails on: f([null])}.

```groovy
class C {
    @Requires({ xs.size() > 0 && xs[0] != null })
    static int f(List<String> xs) { xs[0].length() }       // verifies
}
class D {
    @Requires({ xs.size() > 1 && xs[0] != null })
    static int f(List<String> xs) { xs[1].length() }       // refutes — guard was on index 0
}
```

The wrong-index refutation drops out for free: the contract pins
{@code select(xs$nullElem, 0) == 0}, but the body's obligation is about
{@code select(xs$nullElem, 1)}, which Z3 is free to assign 1.

**Annotation plumbing.** {@code collectNonNullElementContainers} reads the standard NullChecker-
shape simple-name set ({@code NonNull}, {@code NotNull}, {@code Nonnull},
{@code MonotonicNonNull}) off the element generic and the array component type, suppressing the
implicit obligation for declared-non-null containers — *if* Groovy's AST preserves the
annotation at the read position. In current Groovy 6.0.0-SNAPSHOT, type-use annotations on
generics ({@code List<@NonNull String>}) aren't reliably present on the GenericsType's inner
ClassNode, so the suppression path is a no-op in practice today; the contract form is the
working interface. The matcher handles inner-class annotation names by stripping the segment
after the last {@code $}, so a {@code C.NonNull} (which Groovy renders as {@code C$NonNull})
matches the same as a top-level {@code NonNull} — should the upstream parser start surfacing
the annotations, this slice picks them up without further changes.

**Known limits.**

- **Annotation surfacing** — see above. The infrastructure is in place; the AST input isn't
  consistently there. Out of our hands until Groovy preserves type-use annotations on generic
  type arguments at the StaticTypeChecking phase.
- **No nullity tracking through writes.** {@code xs[i] = null} / {@code xs[i] = something} does
  not currently update the per-element nullity array — the oracle is read-only in this slice.
  Practical impact: a body that *assigns* into the list and then dereferences would still flag
  the dereference. Adding the write-side is a follow-up paralleling the existing per-store
  {@code count} law.
- **No cross-call propagation.** A method receiving a {@code List<String>} returned by another
  contracted method doesn't know whether that other method's @Ensures said anything about
  element nullity. Element-level @Ensures shapes ({@code @Ensures({ result[0] != null })}) are
  encodable in contracts already; they just aren't currently summarised through inter-procedural
  Phase-7 reasoning the way scalar postconditions are.

## Phase 38 — Immutable container factory recognition  *(shipped)*

**Peephole, not theory.** Immutable factories are the easiest immutability slice to land: their
size is known statically, their elements are known statically, and they can never be mutated —
so every {@code .size()}/{@code .contains}/{@code .get} call on a factory receiver can be folded
to a ground SMT term *without* minting a set/list/map handle. There's no new oracle, no per-store
update law, and no quantifier. Just literal-driven folding.

**Recognised receivers.** {@code factoryContainerFor} matches:

- {@code List.of(args)}, {@code Set.of(args)}, {@code Map.of(k1, v1, …)} — Java-9+ factories.
- Groovy list literals {@code [a, b, c]} (kind {@code list} by default; the outer cast
  {@code [a, b, c] as Set} switches the kind via {@code CastExpression} unwrapping).
- Groovy map literals {@code [k1: v1, k2: v2]} via {@code MapEntryExpression} iteration.

**The folds.** For a recognised {@code FactoryContainer} {@code f}:

| Op | Fold |
|---|---|
| {@code f.size()} | {@code intLit(f.entryCount())} |
| {@code f.isEmpty()} | {@code boolLit(f.entryCount() == 0)} |
| {@code f.contains(x)} | {@code x == a_0 ∨ x == a_1 ∨ …} (list/set kinds) |
| {@code f.containsKey(k)} | same disjunction over {@code f.keys} (map kind) |
| {@code f.containsValue(v)} | same disjunction over {@code f.values} (map kind) |
| {@code x in f} | same as {@code f.contains(x)} for list/set; {@code f.containsKey(x)} for map (matches Groovy semantics) |
| {@code f.get(literal_i)} | {@code translate(f.args[i])} (list); {@code ite}-chain over {@code (k_j, v_j)} entries (map) |
| {@code f[literal_i]} | same fold via {@code translateBinary}'s LEFT_SQUARE_BRACKET path |

```groovy
class C {
    @Ensures({ result == 3 })
    static int f() { List.of(1, 2, 3).size() }

    @Ensures({ result == 1 })
    static int g() { List.of(1, 2, 3).contains(2) ? 1 : 0 }

    @Ensures({ result == 20 })
    static int h() { [10, 20, 30][1] }

    @Ensures({ result == 2 })
    static int i() { Map.of("a", 1, "b", 2).get("b") }
}
```

All four verify. Replace {@code result == 3} with {@code result == 4} and the soundness anchor
kicks in: the literal fold means Z3 sees {@code 3 == 4} on the residual goal, refutes immediately.

**Known limits — all but one closed in Phases 38b/38c** (detailed below): local-variable
propagation of a factory RHS, `Set.of` duplicate enforcement, `Collections.unmodifiableX` /
`.asImmutable()` unwrapping, `.keySet()` / `.values()` forwarding, and symbolic-index `.get(i)`
(an `ite`-chain over the literals). The one residual: **symbolic-arg distinctness** — `Set.of(a, b)`
where Z3 would have to prove `a != b` to know the size — stays out of scope.

### Phase 38b — Factory through assignment  *(shipped)*

The biggest Phase 38 known limit closed. {@code List<Integer> xs = List.of(1, 2, 3); xs.size()}
now folds the same as the inline form: the {@code Assign}-step handler in both {@link
VerifyChecker#checkPath} (body replay) and {@link VerifyChecker#dischargeVfObligation} (implicit
obligation discharge) calls a new {@code Encoder.tryRecordFactoryAssign(name, rhs)} before
falling through to the int-SSA path. The encoder stashes the recognised {@link FactoryContainer}
in a per-session {@code localFactories} map; {@code factoryContainerFor} now resolves a plain
{@code VariableExpression} against that map, so every existing fold path —
{@code translateMethodCall}, {@code translateBinary}'s {@code in} and LEFT_SQUARE_BRACKET branches
— lifts across the variable boundary without further changes.

**Pinning the cross-cutting oracles.** A factory result is non-null and has a known size; both
facts the existing implicit-obligation pass consults independently of the factory fold. So
{@code tryRecordFactoryAssign} also:

```groovy
session.assertExpr(session.not(nullityOf(name)))
if (f.kind == 'list' || f.kind == 'set') {
    session.assertExpr(session.eq(sizeOf(name), session.intLit((long) f.entryCount())))
}
```

— pinning the nullity oracle to false and (for list/set kinds) {@code sizeOf} to the literal entry
count. With that, {@code xs.size()} discharges the {@code xs?null} obligation, {@code xs[1]}
discharges the bounds check via {@code sizeOf(xs) == 3}, and the factory fold delivers the
literal result. Map factories don't need the size pin — {@code m.size()} folds via the factory
fold itself, and the underlying map-vals/key-set handles aren't queried directly.

```groovy
class C {
    @Ensures({ result == 3 })
    static int f() {
        List<Integer> xs = List.of(1, 2, 3)
        xs.size()             // ✓ folds to 3 via the recorded local
    }

    @Ensures({ result == 20 })
    static int g() {
        List<Integer> xs = [10, 20, 30]
        xs[1]                 // ✓ folds to 20; bounds discharged by the sizeOf pin
    }

    @Ensures({ result == 2 })
    static int h() {
        Map<String, Integer> m = Map.of("a", 1, "b", 2)
        m.containsKey("b") ? m.get("b") : 0   // ✓ both folds lift across `m`
    }
}
```

All three verify; the wrong-literal mirrors still refute. The hook fires the same way for both
verification passes, so an implicit-obligation site downstream of a factory assignment sees the
same nullity/size facts the body-replay path does — no divergence between the two oracles.

## Phase 39 — Common list / map method-form idioms  *(shipped)*

**Method-form sugar for the bracket access path.** {@code xs.get(i)}, {@code xs.first()},
{@code xs.head()}, {@code xs.last()} are sibling spellings of {@code xs[i]} and {@code xs[0]} /
{@code xs[size-1]} — Java-style on the get side, Groovy-functional on the first/head/last side.
Until Phase 39 they fell through to honest skip; the verifier didn't recognise them as
indexed reads. The lowering is small (each maps to {@code (select arr i)} with the appropriate
index expression), and one important piece of plumbing makes them sound: the {@link
ObligationCollector} now synthesises an {@code IndexSite} alongside the existing {@code DerefSite}
when it sees these shapes, so the bounds check fires the same way it does for the bracket form
— {@code xs.first()} on a possibly-empty list refutes with {@code obligation: 0 <= 0 && 0 < xs.size()}
and {@code fails on: f([])}, exactly the same diagnostic {@code xs[0]} would produce.

**The dispatch.** In {@code translateMethodCall}'s named-receiver block:

```groovy
if (m == 'get' && args.size() == 1) {
    return session.select(arrayFor(rn), translate(args.get(0)))
}
if ((m == 'first' || m == 'head') && args.isEmpty()) {
    return session.select(arrayFor(rn), session.intLit(0L))
}
if (m == 'last' && args.isEmpty()) {
    return session.select(arrayFor(rn), session.minus(sizeOf(rn), session.intLit(1L)))
}
```

The corresponding {@code IndexSite} synthesis happens in {@link ObligationCollector} for the
{@code get} and {@code first}/{@code head} shapes (index is the arg or {@code ConstantExpression(0)}).
{@code last} skips the synthesis — its index {@code sizeOf-1} is harder to fabricate as an
{@link Expression}, and the @Ensures-driven check already covers correctness when the user
guards with {@code xs.size() > 0}.

**`xs.set(i, v)` as a statement.** The mutating sibling of {@code xs[i] = v} is recognised in
{@link BodyEncoder}'s {@code ExpressionStatement} handling: a non-tail
{@code MethodCallExpression} with {@code methodAsString == 'set'} and two args, on a named
receiver, becomes an {@code ArrayStore(arr, idx, val)} step — the same step the bracket form
emits. Subsequent reads of {@code xs[i]} see the update, the per-store {@code count} law fires,
and {@code @Modifies} framing covers the unchanged indices.

**`m.getOrDefault(k, default)`.** The canonical defensive-read map idiom lowers to
{@code ite(containsKey(k), m[k], default)}, with the default translated in the map's value sort
so types compose. Verifies the value-when-present case via the map-vals/key-set composition
already in for {@code m.containsKey} and {@code m[k]}.

**Factory-fold extensions.** {@code List.of(args).first()} / {@code .head()} / {@code .last()}
fold the same way {@code .get(literal_i)} already did: pick the first/last arg by position;
return null (honest skip) on an empty factory.

```groovy
class C {
    // Bracket and method form discharge identically.
    @Requires({ xs != null && xs.size() > 0 })
    @Ensures({ result == xs[0] })
    static int head(List<Integer> xs) { xs.first() }       // ✓

    // Set-via-method threads through ArrayStore the same as xs[k] = v.
    @Requires({ a != null && 0 <= k && k < a.size() && j != k && 0 <= j && j < a.size() })
    @Modifies({ this.a })
    @Ensures({ a[k] == v && a[j] == old.a[j] })
    void put(int k, int v, int j) { a.set(k, v) }          // ✓

    // Map.getOrDefault picks the value when present, the default otherwise.
    @Requires({ m != null && m.containsKey("k") && m["k"] == 42 })
    @Ensures({ result == 42 })
    static int lookup(Map<String, Integer> m) { m.getOrDefault("k", 0) }   // ✓
}
```

**Known limits.**

- **Sublist-returning idioms** ({@code xs.tail()}, {@code xs.init()}, {@code xs.drop(n)},
  {@code xs.take(n)}) still defer. Each returns a *new* list, which requires minting a fresh
  array handle and threading content-relation axioms ({@code tail[i] == xs[i+1]},
  {@code size(tail) == size(xs) - 1}) — a separate phase paralleling materialised sets.
- **`xs.last()` bounds synthesis.** The bounds check synthesis for {@code .last()} would need
  an {@code Expression} for {@code xs.size() - 1}; not fabricated here. The @Ensures-driven
  check still catches correctness violations, and the user's guard ({@code xs.size() > 0})
  closes the implicit obligation.
- **Set side intentionally minimal.** {@code s.first()} / {@code s.head()} are
  implementation-defined for sets (HashSet's iteration order is hash-dependent), so the
  named-receiver dispatch only fires for lists. Factory sets DO fold {@code .first()} /
  {@code .last()} via the recorded element order — sound for {@code Set.of(...)}-style literals
  where the input order is the source of truth.

## Phase 40 — Size-changing list mutation  *(shipped)*

**The last row-1 capability.** Until Phase 40, {@code xs.add(v)} / {@code xs.clear()} /
{@code xs.removeLast()} on a list were "outside fragment" — the verifier had no model for size
changing across a body step. Phase 40 threads the size oracle ({@link Encoder#sizeOf}) and the
array oracle ({@link Encoder#arrayFor}) together at each mutation, parallel to how Phase 16's
{@code applySetMutation} threads the set's characteristic array and cardinality. No new theory;
just oracle threading.

**The encoding — direct SMT-expression rebinding.** A new {@link Encoder#bindSize} method lets
the size handle for a name be replaced with any SMT expression. Combined with the existing
{@link Encoder#bindArray}, the three list mutations lower to:

```groovy
// xs.add(v)
enc.bindArray(name, s.store(enc.arrayFor(name), enc.sizeOf(name), x))
enc.bindSize(name, s.plus(enc.sizeOf(name), s.intLit(1L)))

// xs.clear()
enc.bindSize(name, s.intLit(0L))     // array left as-is — no in-bounds read survives

// xs.removeLast() / xs.pop()
enc.bindSize(name, s.minus(enc.sizeOf(name), s.intLit(1L)))
```

The rebinding stores **expressions, not named constants** — no SSA versioning needed. Two adds
in a row chain naturally via expression composition: after the second add the size handle is
{@code (+ oldSize0 1 1)} which Z3 simplifies. Subsequent {@code xs[i]} reads see the threaded
array; the per-store {@code count} law fires on the {@code add} store the same way it does for
{@code xs[i] = v}.

**Pop-on-empty diagnostic.** {@code xs.removeLast()} / {@code xs.pop()} require a non-empty list
at runtime — failing throws {@code NoSuchElementException}. The verifier emits this as a
synthesised {@code IndexSite(xs, 0)} in the {@link ObligationCollector}, so the existing implicit-
bounds-check machinery refutes pop-on-empty with the familiar shape:

```
Possible IndexOutOfBoundsException: index may be out of bounds
    obligation: 0 <= 0 && 0 < xs.size()
    counterexample: xs.size() = 0
    fails on: popOne([])
```

The diagnostic mentions {@code IndexOutOfBoundsException} rather than {@code NoSuchElementException}
— a tiny semantic mismatch traded for the soundness of the existing bounds-check infrastructure
firing uniformly on both spellings.

**`old.xs.size()` plumbing.** A postcondition like {@code @Ensures({ xs.size() == old.xs.size() + 1 })}
needs {@code old.xs.size()} to refer to the entry-time size *before* any mutation rebound it.
checkPath's old-snapshot loop now also calls {@code bindSize('old$xs', sizeOf('xs'))} so the
entry handle is pinned before any body step runs. The {@code .size()} dispatch in
{@code translateMethodCall} was widened to recognise the {@code old.fld} PropertyExpression
receiver shape, mapping it to the {@code old$fld} key.

```groovy
class C {
    List<Integer> xs
    @Requires({ xs != null && xs.size() > 0 })
    @Modifies({ this.xs })
    @Ensures({ xs.size() == old.xs.size() - 1 })
    void popOne() { xs.removeLast() }                  // ✓

    @Requires({ xs != null })
    @Modifies({ this.xs })
    @Ensures({ xs.size() == old.xs.size() + 2 })
    void pushTwo(int a, int b) { xs.add(a); xs.add(b) } // ✓ — chained via expression composition

    @Requires({ xs != null })
    @Modifies({ this.xs })
    @Ensures({ xs.size() == old.xs.size() })
    void roundTrip(int v) { xs.add(v); xs.removeLast() } // ✓
}
```

**Known limits.**

- **Shift-based variants** ({@code xs.add(i, v)}, {@code xs.remove(i)}, {@code xs.remove(Object)})
  defer. They require modelling arbitrary element shifts via a quantifier ({@code ∀j. j < i → new[j] == old[j];
  ∀j. j >= i → new[j] == old[j-1]}) and quantifier instantiation depends on Z3 e-matching —
  higher risk of trigger-cliff issues. A separate phase.
- *Since closed (detailed below):* count-tracking across mutations (Phase 41), field-receiver
  bounds synthesis (Phase 43), and implicit obligations downstream of a mutation (Phase 42).

## Phase 41 — Bounded list count, faithful to runtime semantics  *(shipped)*

**The semantic mismatch resolved.** Groovy's GDK {@code list.count(v)} iterates {@code [0, size)};
the verifier's existing {@link SmtSession#count} oracle counts over the unbounded array-index
domain. For arrays ({@code int[]}) the two interpretations agree (size is fixed, no slack); for
lists they diverge whenever size changes without the contents changing — exactly what
{@code removeLast()} / {@code clear()} do. Phase 41 routes list {@code .count(v)} through a new
{@link SmtSession#bcount}({@code arr, v, lo, hi}) oracle and emits per-store + boundary update
laws on every list mutation.

**The encoding.** A new {@code bcount(arr, v, lo, hi)} uninterpreted function returns
{@code #{i : lo ≤ i < hi ∧ arr[i] == v}} (its *meaning* comes from the caller-asserted laws,
mirroring how {@link SmtSession#count} and {@link SmtSession#setCount} work). The encoder
distinguishes List from array via a new {@code currentListNames} set collected from typed
parameters/fields, and the {@code .count(v)} dispatch in {@link translateMethodCall} routes
accordingly:

```groovy
if (m == 'count' && ...) {
    Object arr = arrayHandleFor(recv)
    String rname = receiverArrayName(recv)
    if (rname != null && isListName(rname)) {
        return session.bcount(arr, translate(v), session.intLit(0L), sizeOf(rname))
    }
    return session.count(arr, translate(v))   // unchanged for arrays
}
```

**The laws.** Three per-mutation laws keep {@code bcount} in sync with the body's effect:

- **Per-store** ({@code xs[i] = v} / {@code xs.set(i, v)}): the existing per-store law in the
  {@code ArrayStore} handler now fires on {@code bcount} for List receivers instead of
  {@code count}: {@code bcount(newA, w, 0, size) = bcount(oldA, w, 0, size) - [oldA[i] == w ? 1 : 0]
  + [v == w ? 1 : 0]}. Same shape as the unbounded version, with the bound carried through.
- **Add boundary** ({@code xs.add(v)}): the prefix {@code [0, oldSize)} is unchanged, and the new
  tail slot at {@code oldSize} holds {@code v}: {@code bcount(newA, w, 0, newSize) =
  bcount(oldA, w, 0, oldSize) + [v == w ? 1 : 0]}.
- **RemoveLast boundary** ({@code xs.removeLast()} / {@code xs.pop()}): array unchanged; the
  dropped tail's contribution is the only delta: {@code bcount(arr, w, 0, newSize) =
  bcount(arr, w, 0, oldSize) - [arr[newSize] == w ? 1 : 0]}.
- **Clear**: {@code bcount(arr, w, 0, 0) == 0} for each tracked {@code w} — the empty-range
  zero fact, ad-hoc per call (cheap, avoids needing a quantified empty-range axiom).

```groovy
class C {
    List<Integer> xs
    @Requires({ xs != null })
    @Modifies({ this.xs })
    @Ensures({ xs.count(v) == old.xs.count(v) + 1 })
    void push(int v) { xs.add(v) }                       // ✓ (add boundary law)

    @Requires({ xs != null && xs.size() > 0 && xs[xs.size() - 1] == v })
    @Modifies({ this.xs })
    @Ensures({ xs.count(v) == old.xs.count(v) - 1 })
    void popOne(int v) { xs.removeLast() }              // ✓ (removeLast boundary law)

    @Requires({ xs != null })
    @Modifies({ this.xs })
    @Ensures({ xs.count(v) == old.xs.count(v) })
    void roundTrip(int v) { xs.add(v); xs.removeLast() } // ✓ (laws compose — the headline win)
}
```

The {@code roundTrip} proof is the demo Phase 41 was for: with the pre-Phase-41 unbounded count,
the {@code add} grew the count by one and {@code removeLast} (which doesn't touch the array)
left it grown — the postcondition refuted. With {@code bcount}, the {@code add} grows
{@code bcount(_, _, 0, oldSize+1)} by one and {@code removeLast} drops the size back, so
{@code bcount(_, _, 0, oldSize)} ends equal to what it was at entry.

**User experience.** Pure encoding change — no contract or annotation rewrites. The user writes
the same {@code xs.count(v)} they always did; the verifier now matches what Groovy actually
returns at runtime.

**Arrays untouched.** {@code int[] a; a.count(v)} continues to route through the unbounded
{@link SmtSession#count}, so Phase 12's per-store law and the Phase 14 permutation-sort
showcase are zero-regression.

**Known limits.**

- **Shift-based mutations still defer.** {@code xs.add(i, v)} and {@code xs.remove(i)} would
  need bcount update laws that account for arbitrary shifts — same hard problem as for size
  alone (Phase 40 known limit). Closed together with that work.
- **Cross-call bcount propagation.** A callee's {@code @Ensures} about its own list's
  {@code .count(v)} isn't yet summarised through the inter-procedural Phase-7 reasoning the
  way scalar postconditions are. Same gap as for scalar nullity (Phase 37) and other ensure-driven
  array facts.

## Phase 42 — LemmaCall replay in the implicit-obligation pass  *(shipped)*

**The Phase 40/41 follow-on.** Until Phase 42, the two verification passes ({@code checkPath} for
postconditions and {@code dischargeVfObligation} for implicit obligations like array bounds,
divide-by-zero, NPE) replayed different shapes of body steps. {@code checkPath} walked a Path
whose {@code steps} include Assign / Guard / ArrayStore / LemmaCall in source order — set adds,
map puts, list mutations all threading their oracles. {@code dischargeVfObligation} snapshotted
{@code [guards, assigns]} only, in two separate lists. The result: a body like {@code xs.add(v);
xs[0]} verified its {@code @Ensures} cleanly but over-refuted the bounds check on {@code xs[0]}
(the implicit pass didn't know {@code xs.size()} had grown).

**The refactor.** {@code VfObligation} now carries a single {@code steps: List<Object>} in source
order, populated by {@code collectVfObligations} as it walks the body — Assign, Guard, *and*
LemmaCall steps interleave the same way they do in {@code checkPath}'s Path.

```groovy
@CompileStatic
private static class VfObligation {
    Object site                 // IndexSite | DivideSite | DerefSite
    List<Object> steps          // Assign | Guard | LemmaCall, in source order
}
```

{@code dischargeVfObligation} walks the snapshot in source order, dispatching each step through
the same handlers {@code checkPath} uses ({@code tryMaterialiseSetBinopAssign},
{@code tryRecordFactoryAssign}, {@code applySetMutation}, {@code applyMapPut},
{@code applyListMutation}). The two passes now see the same oracle state at the obligation site —
no divergence, no over-refute.

**Why source order matters.** Assigns / guards are commutative — they assert facts that don't
depend on each other. LemmaCalls rebind the size and array oracles SSA-style, so a guard like
{@code if (xs.size() > 0) …} placed *after* an {@code xs.add(v)} must see the post-mutation
size. Replaying assigns and guards before lemmas (the obvious naïve approach) would assert the
guard against pre-mutation oracles — unsound for the case where the guard depends on the
mutation's effect. The single-ordered-list refactor avoids this by reusing exactly the same
walking discipline {@code checkPath} already had.

**Unrecognised LemmaCalls.** Plain callee calls (a method with no recognised mutation shape) are
silently skipped in the implicit-pass replay, rather than throwing {@code
UnsupportedConstructException} as {@code checkPath} does. The implicit pass is best-effort —
"can't model this mutation" should mean "don't sharpen the downstream check", not "fail the
build".

```groovy
class C {
    @Requires({ xs != null })
    static int firstAfterPush(List<Integer> xs, int v) {
        xs.add(v)
        xs[0]                                          // ✓ bounds discharged via post-add size
    }

    @Requires({ xs != null && xs.size() > 0 })
    static int popThenRead(List<Integer> xs) {
        int n = xs.size()
        xs.removeLast()
        xs[n - 1]                                      // ✗ refutes — size shrunk, n-1 out of bounds
    }
}
```

The {@code firstAfterPush} verify-side is the more visible win; the {@code popThenRead}
refute-side is the soundness anchor (pre-Phase-42 it would have passed because the implicit pass
didn't see the size shrink).

**Known limits.**

- **`countVals` not threaded into the implicit pass.** The bcount boundary law ({@link
  applyListMutation} with non-empty {@code countVals}) is invoked only by {@code checkPath} —
  the implicit pass passes an empty list so the per-mutation bcount facts aren't asserted. Why:
  {@code countVals} are scoped to a postcondition's tracked {@code .count(v)} mentions, which
  aren't relevant to implicit obligations (bounds/null/div). If a future obligation type does
  care about counts, the threading would extend.
- **ArrayStore step still missing.** Bracket assignment {@code xs[i] = v} becomes an
  {@code ArrayStore} step in {@code BodyEncoder} but doesn't get recorded in the implicit-pass
  steps list (the value-flow collector skips ArrayStore by design — its contents aren't tracked
  there). Practical impact: an obligation downstream of an in-bounds bracket store doesn't see
  the contents change. Rarely matters for the bounds/null/div check; could matter if a future
  obligation depends on element values.

## Phase 43 — Field-receiver bounds synthesis  *(shipped)*

**Closes the Phase 40 ergonomic gap.** The IndexSite synthesis for runtime-throwing list shapes
({@code get(i)}, {@code first()}, {@code head()}, {@code removeLast()}, {@code pop()}) was added
in Phase 39/40 inside {@link ObligationCollector#visitMethodCallExpression}, gated by a
{@code realVar} check that accepts only {@link Parameter} and (the loop-bound)
{@link VariableExpression} resolutions. Instance-field references — where
{@code v.accessedVariable} is a {@link FieldNode} — fell through silently, so a pop-on-empty on
{@code this.xs} verified despite the guaranteed runtime exception.

**The fix.** A second branch in the same method handles {@link FieldNode}-resolved
{@code VariableExpression}s. It calls the same {@code synthIndexSiteFor(mce, name)} helper the
parameter branch uses — same diagnostic, same shape, same {@code IndexSite(name, 0)} or
{@code IndexSite(name, idxArg)} — but **does not** add a {@link DerefSite}. The asymmetry is
intentional: existing tests that mutate set/map/list instance fields
({@code s.add(x)}, {@code m.put(k, v)}, {@code xs.add(v)}) don't carry a {@code @Requires({
field != null })}, and adding a scalar nullity check on the receiver would have regressed them.
The bounds check on runtime-throwing reads is what the user actually needs flagged; the field's
scalar nullity is handled by the surrounding class invariants if at all.

```groovy
class C {
    List<Integer> xs
    void popOne() { xs.removeLast() }   // ✗ refutes — pop-on-empty, fails on: popOne()

    @Requires({ xs != null && xs.size() > 0 })
    @Modifies({ this.xs })
    void popSafe() { xs.removeLast() }  // ✓ — bounds discharged via @Requires
}
```

The diagnostic shape is identical to the parameter-receiver version — same
{@code obligation: 0 <= 0 && 0 < xs.size()}, same {@code counterexample: xs.size() = 0}, same
{@code fails on:} repro line (just with no list argument since {@code xs} is a field).

**Known limits.**

- **No scalar field-nullity check.** A {@code field.method()} on an instance field still skips
  the {@code field != null} obligation. Adding it would regress the set/map/list mutation tests;
  the only sound fix is to require those tests to assert non-null in their @Requires (an
  ergonomic change). Class invariants can pin the field's non-null property; this is the
  intended pattern.
- **{@code xs.last()} bounds still skip.** Same as Phase 39's known limit — the {@code size-1}
  index isn't fabricated as an Expression; the @Ensures-driven check still catches correctness
  violations.

## Phase 44 — Opt-in 32-bit integer overflow checks  *(shipped)*

**Closes the major theory gap with Verus.** Until this phase, every {@code int} in groovy-verify
was modelled as Z3's mathematical {@code Int} sort — unbounded, no overflow. This is great for
proof ergonomics (most contracts hold for math integers and machine integers identically) but
unsound vs. the JVM's actual semantics: {@code add(Integer.MAX_VALUE, 1)} returns a wrapped
negative at runtime, and a {@code @Ensures({ result == a + b })} can pass under the math view
while the program computes a non-equal wrapped value.

**The design choice — opt-in, not always-on.** Verus is always-on because Rust's typed-narrow
integers ({@code u32}, {@code i64}, etc.) drive overflow obligations at every arithmetic op.
Groovy has only {@code int}/{@code long}/{@code short}/{@code byte}/{@code char} and no spec/impl
type distinction. Making overflow always-on would refute the permutation-sort showcase
({@code i + 1} loop indices), the Counter example ({@code count + 1} mutations), and ~200 other
existing tests until each gets a fresh layer of bounds annotations. Instead, groovy-verify takes
the path Groovy can support: a {@code @verification.CheckOverflow} marker enables the precise
check method-by-method or class-by-class. Default code keeps the math-int experience; annotated
code gets the Verus-style guarantee.

This positions groovy-verify uniquely in the SMT-verifier landscape: *math by default, machine
precision on demand* — the same engine handles both regimes with one annotation flip.

**The encoding.**

A new {@link OverflowSite} kind in {@link ObligationCollector}, collected only when
{@code currentOverflowChecking} is set:

```groovy
@CompileStatic private static class OverflowSite {
    ASTNode node
    Expression left
    Expression right
    String op       // "+", "-", "*"
    String text     // pretty-printed for the diagnostic
}
```

The {@code ObligationCollector.visitBinaryExpression} adds a site for each {@code +}/{@code -}/
{@code *} on Int-sorted operands, then recurses via {@code super.visitBinaryExpression} so a
nested {@code (a + b) * c} emits two obligations — one for the inner add, one for the outer
mul. The same operator-text gate as the existing {@code /} / {@code %} division check.

The discharge ({@link dischargeOverflow}, called from both the havoc pass and the value-flow
pass via {@link dischargeObligationUnder}) translates the operands as math ints, computes the
result expression with the matching SMT operator, and asserts the negation of
{@code INT_MIN ≤ result ≤ INT_MAX}:

```groovy
Object result = (ov.op == '+') ? s.plus(L, R) :
                (ov.op == '-') ? s.minus(L, R) :
                                 s.times(L, R)
s.assertExpr(s.or([s.lt(result, s.intLit(-2147483648L)),
                   s.gt(result, s.intLit(2147483647L))]))
```

SAT means the math result can lie outside 32-bit range on this path — refute with
{@link Reporter#formatOverflow}, which mirrors the Java exception a developer would actually hit
with {@code Math.addExact} et al.:

```
Possible ArithmeticException: addition overflows 32-bit signed range
    obligation: Integer.MIN_VALUE <= (n + 1) && (n + 1) <= Integer.MAX_VALUE
    counterexample: n = 2147483647
    fails on: incr(2147483647)
```

**Phase 44c — Implicit JVM Int bounds, *always-on*.** Two pieces shipped alongside the opt-in
overflow check, and together they're the *unconditional* slice of the work — they apply whether
or not {@code @CheckOverflow} is set:

1. {@code sizeOf(recv)} now asserts {@code 0 ≤ size ≤ Integer.MAX_VALUE} on every mint
   (was just {@code ≥ 0}). Sound by Java's collection contract.
2. {@code assumeIntJvmBounds(s, enc)} runs at the start of every verification pass
   (body-replay {@code checkPath}, value-flow {@code dischargeVfObligation}, implicit-obligation
   {@code assumeContext}, loop {@code dischargeRegion}) and asserts the integral type's JVM range
   per parameter and declaring-class field: {@code INT_MIN ≤ p ≤ INT_MAX} for {@code int}/{@code Integer},
   {@code LONG_MIN ≤ p ≤ LONG_MAX} for {@code long}/{@code Long} (Phase 44c-width). Without the long
   case a {@code long} param is an unbounded math integer, so the 64-bit overflow check picks a
   counterexample *below* {@code Long.MIN_VALUE} ({@code n + 1 < LONG_MIN}) the runtime can't exhibit.

Locals are transitively bounded via their assignment RHS (an SSA-fresh local is constrained by
{@code local == rhs}, and rhs operates on bounded values). The combined effect: under
{@code @CheckOverflow}, Z3's counterexamples are always values the runtime can actually produce
— a counterexample like {@code n = -2147483650} (below INT_MIN) is no longer possible.

Without {@code @CheckOverflow}, the bounds are still asserted (because they're sound), but
arithmetic isn't checked — so a math-int proof that doesn't depend on the range works
unchanged, and the entire existing test suite verifies as before.

```groovy
class C {
    @CheckOverflow
    @Requires({ a >= 0 && a < 10000 && b >= 0 && b < 10000 })
    static int mul(int a, int b) { a * b }                  // ✓ verifies (50_000_000 < INT_MAX)

    @CheckOverflow
    @Requires({ a >= 0 && a < 100000 && b >= 0 && b < 100000 })
    static int mulLoose(int a, int b) { a * b }             // ✗ refutes (could exceed INT_MAX)

    @CheckOverflow
    @Requires({ a >= 0 && a < 1_000_000 })
    static int sq1(int a) { (a + 1) * (a + 1) }             // ✗ refutes — sub-expression check
}

@CheckOverflow
class D {
    static int incr(int n) { n + 1 }                        // ✗ class-level propagation
}
```

The class-level form covers every method and constructor; method-level overrides for finer
scoping (only on selected methods, regardless of class).

**Known limits.**

- **Width-aware overflow (Phase 44c-width, *shipped*).** The overflow obligation's bound now follows
  Java binary numeric promotion of the *operands*: 64-bit ({@code [LONG_MIN, LONG_MAX]}) when either
  operand is {@code long}/{@code Long}, else 32-bit. So {@code @CheckOverflow long f(long n) { n + 1 }}
  refutes only at the genuine 64-bit boundary ({@code n == Long.MAX_VALUE}) and verifies under a guard
  like {@code n < Long.MAX_VALUE} — no longer a spurious 32-bit refute. {@code BigInteger} operands carry
  no obligation (unbounded, cannot overflow). Two soundness pieces ride along: {@code long}/{@code Long}
  params and fields are bounded to {@code [LONG_MIN, LONG_MAX]} (above), and counterexample extraction
  saturates math-int model values that exceed {@code long} range ({@code clampInt64}) instead of throwing
  — a 64-bit overflow witness can pin an operand past {@code Long.MAX_VALUE}, and the un-caught
  {@code "Numeral is not an int64"} would otherwise drop the whole refute back to a silent clean compile.
- **`short`, `byte`, `char`** still promote to int (32-bit) in arithmetic — correct for the arithmetic
  itself; their narrow widths matter only at a narrowing cast/assignment, a separate slice (below).
- All arithmetic-overflow edge cases now ship: addition, subtraction, multiplication
  ({@code 'neg'} for unary minus on INT_MIN, {@code 'div'} for INT_MIN/-1). {@code %} is
  specifically *not* flagged — Java guarantees {@code Integer.MIN_VALUE % -1 == 0}.
- **JDK boxed-range constants** (`Integer.MAX_VALUE`/`MIN_VALUE`, `Long`/`Short`/`Byte`/`Character`
  variants) fold to their literal values via {@code tryFoldJdkRangeConstant} in the
  {@link PropertyExpression} dispatch, so {@code @Requires({ n < Integer.MAX_VALUE })} works as
  written. Match is by simple class-name on a {@link ClassExpression} (or pre-resolution
  {@link VariableExpression}), so fully qualified and unqualified spellings both fold.
- **Cast/conversion overflow.** {@code (byte) intVal}, {@code (int) longVal} need explicit
  truncation modelling — not in the fragment regardless of {@code @CheckOverflow}.
- **`.intValue()` / `.longValue()` truncation — attempted and rejected at the leaf.** A tempting small slice
  is to model the narrowing wrap at the `.intValue()` call (so `(2 ** 31).intValue() == Integer.MIN_VALUE`,
  which would let `1 << n == 2 ** n` prove through the 32-bit boundary). It does *not* work at the leaf:
  truncating only the `.intValue()` result while the surrounding int arithmetic stays unbounded math-int is
  internally inconsistent. `result == 2 * (2 ** n).intValue()` is runtime-true for all n (the `2 *` overflows
  too, so both sides wrap together), but a leaf-only model wraps the `.intValue()` and *not* the `2 *`, so it
  reads `−2³¹ == +2³¹` at n=30 and the equality breaks. The hybrid matches neither the math-int idealization
  nor the 32-bit runtime, and the inconsistency cuts both ways (false negatives *and* possible false
  positives). Faithful narrowing requires a **fully width-aware arithmetic model** — every int op wraps, not
  just the cast leaf — which is a large, separate slice (and a natural home for a `@CheckOverflow`-scoped
  32-bit mode). Until then `.intValue()`/`.longValue()` stay identity (Phase 93), consistent with the
  documented "unbounded by default" stance — and that identity is *faithful* for `**`, because Groovy's power
  never wraps: `2 ** 31` is the BigInteger `2147483648`, not a truncated int (verified). So the right way to
  surface `**` is at the unbounded/Number level, where the model is exact; the narrowing concern is a
  separate `@CheckOverflow` obligation ("does `2 ** n` fit in int?"), not a wrap to compute here.
  Consequence: `1 << n == 2 ** n` proves genuinely for `n ≤ 30` and is correctly *not* proved for `n ≥ 31` —
  not a gap, but the truth: with `2 ** n` unbounded and `1 << n` the wrapped 32-bit shift, the two genuinely
  differ at `n ≥ 31` (`2**31 = 2147483648 ≠ 1<<31 = −2147483648`), exactly as at runtime.
- **64-bit shifts + width-aware `.intValue()`/`.longValue()` — implemented end-to-end, then reverted as
  computationally non-viable.** To raise the `1 << n == 2 ** n` ceiling from `n ≤ 30` to `n ≤ 62`, the shift
  side needs 64-bit modelling (`1L << n`) and — for soundness — `.intValue()`/`.longValue()` must actually
  *wrap* (a `long` shift compared against an *un*-wrapped `.intValue()` would falsely prove for `n ≥ 31`).
  Both were built: width-parameterised bit-vector ops (32/64) and bit-vector truncation for the narrowing.
  Findings from the full-suite run: (1) the **soundness piece works** — `(1L << n) == (2 ** n).intValue()`
  correctly does *not* prove, and the old unsound `(2 ** n).intValue() >= 1` stops falsely proving; (2) but
  the **truncation is bit-blast-heavy** — proving `truncate(pow(2,n)) == pow(2,n)` needs to *bound*
  `pow(2,n)`, the same symbolic-exponent reasoning that's already hard, so it times out; (3) the **headline
  `n ≤ 62` times out**, and small ranges (`n ≤ 10`) prove; (4) worse, it **regresses** the previously-working
  symbolic facts (`2 ** n >= 1` at `n ≤ 30`, the int-surface doubling) from clean proofs to could-not-decide,
  because the cheap identity model that made them provable is exactly what the (necessary) wrap removes. The
  cheap-but-unsound identity and the sound-but-bit-blast-heavy truncation are in fundamental tension; neither
  raises the ceiling. So 64-bit shifts are *not* a small add-on — they inherit the same width-aware-arithmetic
  prerequisite, and the practical ceiling stays `n ≤ 30`.
- **Always-on mode.** Some safety-critical projects want overflow checked everywhere, no
  annotation needed. A future {@code @TypeChecked(strict = true)} mode could flip the default
  but isn't in scope here — the math-int default is too useful to drop unilaterally.

## Phase 45 — Cross-class `@Invariant` call-site assumption  *(shipped)*

**The last real capability gap closed.** Phase 15a/b verified class invariants *within* a class —
every instance method assumes the invariant on entry, must re-prove on exit; constructors
establish it. What didn't work until Phase 45: when method `f` on class `A` calls `b.method()`
on object `b` of class `B`, the verifier didn't bring B's invariants into scope. A trivial
{@code c.count >= 0} read for a {@code Counter c} parameter — guaranteed by Counter's invariant
— couldn't be proved without restating the bound in `f`'s own @Requires.

**Why this took a refactor and not a slice.** Until Phase 45, every field reference (`count`,
`max`, etc.) resolved to a single SMT entity per source-name, regardless of which class declared
the field or which object holds it. For cross-class reasoning that's unsound: `a.count` and
`b.count` are distinct values at runtime, and you can't ascribe one invariant's facts to the
other's state. The fix is **per-receiver field namespacing**: a class-typed parameter `b`
introduces fresh SMT entities `b$count`, `b$max`, … distinct from anything named `count`
elsewhere. The receiver's contracts (invariants, @Requires, @Ensures) are translated *under a
receiver context* that rewires bare field references to the qualified entities.

**The encoding.** A new field `receiverPrefix` on the Encoder is set during contract translation
for a foreign receiver, and {@code varFor("count")} consults it:

```groovy
Object varFor(String name) {
    if (receiverPrefix != null && receiverFields.contains(name)) {
        return varForRaw(receiverPrefix + '$' + name)
    }
    // existing this-class regime
}
```

A new public method {@code translateUnderReceiver(expr, recvName, fields)} sets the context for
the scope of one translation and unwinds it on return. Used in three places:

1. **Method entry**, via {@code assumeForeignReceiverInvariants}: for each class-typed parameter,
   look up its declared class's invariants and assume each translated under the receiver. So a
   method taking {@code Counter c} starts with {@code c$count >= 0 && c$count <= c$max} in scope.
2. **Call site precondition discharge**, in {@code verifyCallSite}: when the call is
   {@code b.method(...)} and `b` is a known class-typed parameter, translate the callee's
   @Requires under the receiver context. So {@code count < max} in {@code Counter.incr()}'s
   @Requires becomes {@code c$count < c$max} when checked at a call site `c.incr()`.
3. **Cross-class call effects**, via {@code applyCrossClassCall}: havoc the receiver's fields
   (the callee may have mutated any of them) and re-assume the receiver's class invariants
   under the receiver context. The callee preserved them on exit (Phase 15a/b verified that
   when the callee's class was compiled), so re-assuming them in the caller is sound.

**Property expression translation** picks up the same rewrite for explicit `b.field` reads in
contracts and bodies: the PropertyExpression handler now checks if the object expression is a
known class-typed parameter and the property is one of that class's declared fields, routing to
{@code varForRaw(recvName + '$' + prop)} when both hold.

```groovy
@Invariant({ count >= 0 && count <= max })
class Counter {
    int count, max
    @Requires({ count < max })
    void incr() { count = count + 1 }
}

class Client {
    @Requires({ c != null })
    @Ensures({ result >= 0 })
    static int read(Counter c) { c.count }                      // ✓ (invariant assumed at entry)

    @Requires({ c != null && c.count < c.max })
    static int callIt(Counter c) { c.incr(); 0 }                // ✓ (@Requires discharged under c)

    @Requires({ c != null })
    static int unsafe(Counter c) { c.incr(); 0 }                // ✗ refutes — c.count could == c.max
}
```

The refute diagnostic for `unsafe` names the receiver-qualified entities directly:

```
Cannot prove precondition of incr at this call site
    required: (count < max)
    counterexample: c$count = 0, c$max = 0
    fails on: callIt(null)
```

— Z3 picked a Counter at-max state where the precondition can't hold.

**Soundness boundary.** The encoding is sound *under the no-aliasing assumption*: distinct
parameter names denote distinct objects. Heap aliasing is a [Non-goal](#non-goals), so this is
the assumption the rest of the project already lives under. With aliasing, `b$count` and
`c$count` could refer to the same JVM heap cell — the verifier doesn't model that.

**Known limits.**

- **`old.field` in cross-class @Ensures isn't assumed.** A callee that says
  `@Ensures({ count == old.count + 1 })` would need the verifier to snapshot `b$count` before
  the call and pin the callee's `old.count` to that snapshot. The infrastructure is there
  (Phase 13's caller-side framing already does this for same-class calls); not yet wired for
  cross-class. The invariant is what most cross-class contracts actually rely on.
- **Cross-class fields that are collections.** A `Counter` with a `Set<String> roles` field
  has its scalar fields handled, but `c.roles.contains("admin")` would need the set/map/list
  oracles to be receiver-keyed too. The receiver-qualification concept extends; the
  collect/dispatch wiring doesn't yet.
- **Multi-level dereferencing.** `c.next.count` (a Counter with a `next: Counter` field, walked
  one further step) skips. One level only.
- **Same-class `b.method()` calls** (where `b` is also of the declaring class) currently
  *don't* trigger cross-class machinery — they remain in the Phase 7 same-class call path,
  which doesn't apply the receiver-qualified rewrite. Edge case; the typical use is foreign
  receivers, which work.

## Phase 46a — String predicates as uninterpreted functions  *(shipped)*

The string sort was equality-only since Phase 27 — `s == "admin"` worked, but no string
*content* operations (no `startsWith`, no `endsWith`, no `contains`, no `isEmpty`) reached the
encoder. Any HumanEval-style port that filtered a list by predicate hit a wall here.

**The shipped slice.** Four string predicates translate now, modelled as uninterpreted Bool
functions over the existing `String!Sort`:

- `s.startsWith(p)` → `startsWith$(s, p)` — `(String, String) → Bool`.
- `s.endsWith(q)` → `endsWith$(s, q)`.
- `s.contains(sub)` → `strContains$(s, sub)`.
- `s.isEmpty()` → `strIsEmpty$(s)` — unary.

The encoder routes by receiver type: a String-typed parameter (recorded in `scalarTypes`),
a String literal (`ConstantExpression` of String value), or an indexed access on a
`List<String>` (`xs[i]` / `xs.get(i)`). The list-style dispatch ("contains as bounded
existential over array indices", "isEmpty as size == 0") is **explicitly skipped** for String
receivers — the same method name, but the wrong semantics if applied to a String.

Two applications with the same `(s, p)` share the SMT term, so a contract that names
`s.startsWith(p)` connects by syntactic identity to a body that calls `s.startsWith(p)`. The
verifier knows the predicate has *some* Boolean value at each pair — but **not** what relates
it to `length`, to other strings, or to character positions.

**What this unlocks — HumanEval 029 (`filter_by_prefix`):**

```groovy
@Requires({ xs != null && prefix != null &&
            Forall.range(0, xs.size()) { i -> xs[i] != null } })
@Ensures({ result.size() <= xs.size() })
static List<String> filterByPrefix(List<String> xs, String prefix) {
    List<String> result = []
    int i = 0
    @Invariant({ result != null && 0 <= i && i <= xs.size() && result.size() <= i })
    @Decreases({ xs.size() - i })
    while (i < xs.size()) {
        if (xs[i].startsWith(prefix)) {
            result.add(xs[i])
        }
        i = i + 1
    }
    return result
}
```

Same algorithmic shape as `get_positive` (Verus 030), with `startsWith` substituted for the
positivity check. The Verus original is spec-free; we add the size-bound spec.

**Co-shipped: typed-local element types.** `List<String> result = []` previously crashed
during the first `result.add(...)` with a Z3 sort mismatch — the empty factory `[]` minted a
default Int-element array. Now `collectListElementTypes` also scans the method body for
typed `DeclarationExpression`s so a typed-local non-Int list mints with the right element
sort from the start.

**Known limits.**

- **No axioms beyond translation.** `startsWith(s, "")` isn't known to be true; `length(p) >
  length(s) ⟹ ¬startsWith(s, p)` isn't known. Adequate for "every result element satisfies
  the filter predicate" reasoning where the predicate composes opaquely; insufficient for
  length-coupled or character-content claims.
- **No `length`, no `charAt`.** Specs that talk about string length or character positions
  are still out of fragment — would need either a length oracle with literal pinning
  (cheap follow-on) or Z3's native string theory (major phase).
- **`String.reverse()`** now ships at the literal level (Phase 47i, below) — `"abc".reverse() ==
  "cba"`, literal involution and length. *Symbolic* character-content reasoning
  (`s.reverse().reverse() == s` for a variable `s`) remains out, blocked by the same universal-over-
  `Seq→Seq` refute hang as case folding.
- **In-loop `if (xs[i] != null)` doesn't discharge a per-element deref obligation.** The
  loop-encoder's `applyIf` ITE-combines branch bindings but doesn't thread the condition as
  a path fact through obligation discharge. Workaround: a `Forall.range` precondition over
  `xs[i] != null` (as the `filter_by_prefix` port does). Same shape as Verus' `Vec<String>`
  (non-nullable elements), so the precondition is a faithful translation.

## Phase 46b — String length oracle, literal pinning  *(shipped)*

Phase 46a left string predicates uninterpreted: `s.startsWith(p)` had a value, but no tie
to anything else about `s`. Phase 46b adds the length oracle and pins it precisely at
literals, lifting reasoning to "if `s.startsWith("hello")` then `s.length() >= 5`."

**The shipped slice.**

- **`SmtSession.stringLength(s) → Int`** — an uninterpreted `(String!Sort) → Int` declared
  on first use as `strLength$`. Two applications with the same `s` share the term.
- **Literal pinning at the backend's `litOfSort` mint site.** When a String-sorted constant
  is interned (e.g. `"hello"` minted as `String!val_hello`), the backend also asserts
  `strLength$($lit) == 5` — exact JVM `String.length()` count. This is the only fact about a
  literal's content the encoder can name today (charAt is deferred behind Z3 string theory),
  and it composes cleanly with the Phase-46c axioms.
- **Encoder dispatch.** `s.length()` and its GDK alias `s.size()` on String-typed receivers
  route to `stringLength`. `s.isEmpty()` is now lowered to `length(s) == 0` — the
  Phase-46a uninterpreted predicate is retired, so `s.isEmpty()` and `s.length() == 0`
  resolve to the same term and the verifier sees them as syntactically equivalent.

**What this unlocks (in concert with Phase 46c below):**

- `"hello".length() == 5` folds at the mint site — proved by the literal pin.
- `s.length() >= 0` for any String — from the Phase 46c non-negativity axiom.
- The cross-coupling story: length and `startsWith`/`endsWith` now reason about each other.

## Phase 46c — Light string axioms  *(shipped)*

Three universally-quantified facts asserted exactly once per session, gated by a
`stringAxiomsAsserted` flag and lazily on first use of any string op. Each carries a
single-trigger `mkPattern` so Z3 instantiates only on ground terms the user's proof already
mentions — no blind-fire across the Herbrand universe.

- **Axiom 1 — non-negativity:** `∀s. strLength$(s) >= 0`.
  Trigger: `strLength$(s)`.
  Without this, Z3 could (and would) pick a model where some `s.length() == -7` to disprove
  a postcondition.
- **Axiom 2 — startsWith length bound:** `∀s,p. startsWith$(s, p) ⟹ strLength$(p) <= strLength$(s)`.
  Trigger: `startsWith$(s, p)`.
  Load-bearing contrapositive: `length(p) > length(s)` rules out `startsWith(s, p)` — a
  prefix longer than the string can't match. This is the axiom that lets a 4-char string
  *provably never* start with `"hello"`.
- **Axiom 3 — endsWith length bound:** `∀s,p. endsWith$(s, p) ⟹ strLength$(p) <= strLength$(s)`.
  Trigger: `endsWith$(s, p)`.
  Suffix mirror of axiom 2.

**Demo of the composite reasoning shipped with the tests:**

```groovy
// Axiom 2 used positively — proves the *negation* of startsWith outright, not just leaves it open.
@Requires({ s != null && s.length() == 4 })
@Ensures({ !result })
static boolean cannotStartWith(String s) { s.startsWith("hello") }   // verifies ✅
```

**Known limits.**

- **No `contains`/`isEmpty` length axiom.** `s.contains(sub) ⟹ length(sub) <= length(s)`
  is true and would close an obvious gap, but Z3's quantifier instantiation favours a
  smaller axiom set; if a real use surfaces, add it.
- **No reflexivity (`startsWith(s, s) = true`) or empty-prefix (`startsWith(s, "")`) axioms.**
  Both are natural facts but would add another quantifier; not load-bearing for the
  shipped HumanEval-029 port.
- **No relation between predicates.** `s.startsWith(s)` doesn't imply `s.endsWith(s)`,
  and `s.startsWith(p) ∧ s.endsWith(p)` doesn't tell you anything about `length(p)` vs
  `length(s)/2`. Genuinely structural facts about substrings are deferred behind Z3 string
  theory.
- **`charAt` still isn't reachable.** Character-content reasoning needs either a per-position
  `charAt(s, i): Int` oracle with literal pinning (cheap follow-on) or Z3's native string
  theory (a phase of its own).

## Phase 46d — In-loop `if`-condition as a path fact  *(shipped)*

Phase 46a documented a known limit: an in-body `if (xs[i] != null) xs[i].method()` inside
a `while` body didn't discharge the per-element deref obligation. The `filter_by_prefix`
port worked around it with a `Forall.range` precondition. Phase 46d closes that gap directly.

**The fix lives in `dischargeRegion`.** That function discharges every implicit obligation
(bounds / null / divide / overflow / charAt) inside a loop's prefix / guard / body / suffix
region. Pre-46d it walked top-level statements and discharged each statement's obligations
under "invariants + guard" only — an in-region `if` was traversed for its sites but its
condition wasn't asserted before discharging the body's sites.

Two refinements:

- **If-statement recursion.** When `dischargeRegion` sees an `if (cond) { … } else { … }`,
  it discharges the condition's own obligations under the outer facts, then recurses into
  the then-branch with `cond` added to `assumePos`, and into the else-branch with
  `NotExpression(cond)` added. The new `assumePos` list flows into `dischargeSeeded`, which
  already asserts every entry as a precondition for the obligation check.
- **`&&`/`||`/ternary short-circuit awareness.** A new helper `dischargeExpression` walks
  the expression tree, and for each binary `&&` (resp. `||`) operand-pair, discharges the
  left operand first, then the right under `leftExpression` (resp. `!leftExpression`).
  This matches Groovy's runtime short-circuit, so `xs[i] != null && xs[i].method()`
  discharges the inner deref under the null guard the conjunction establishes.

**What this unlocks.** The `filter_by_prefix` port's `Forall.range` workaround is gone:
the natural `if (xs[i] != null && xs[i].startsWith(prefix))` form verifies directly. New
test group `P46d in-loop guards` proves three shapes:
- `if (xs[i] != null) xs[i].length()` discharges in a loop.
- `if (xs[i] != null && xs[i].startsWith(p))` discharges via short-circuit.
- Removing the guard still refutes (the obligation is real; the guard is what dischargest it).

The same machinery applies to ternary `(c ? t : e)` in any region — the branches' obligations
each see their guard, which is just-in-time path-fact threading.

## Phase 46e — `charAt` with per-position literal pinning + bounds  *(shipped)*

The natural follow-on to Phase 46b's length oracle: `charAt(s, i): Int` returning the
codepoint, with two pieces of machinery that make it useful even without Z3 string theory.

**The shipped slice.**

- **`SmtSession.stringCharAt(s, i) → Int`.** Uninterpreted `(String!Sort, Int) → Int` declared
  lazily as `charAt$`. Two applications with the same `(s, i)` share the term.
- **Per-position literal pinning at the backend's `litOfSort` mint site.** For a String
  literal `"hello"`, each position is pinned: `charAt$($lit, 0) == 104`,
  `charAt$($lit, 1) == 101`, …, one assertion per codepoint. Capped at a `CHAR_PIN_CAP`
  of 64 characters — longer literals still get their length pinned but skip per-char pinning
  to keep mint cost bounded. Lazy: `charAt$` is only declared if at least one literal is
  short enough to pin.
- **Bounds obligation via a new `StringCharAtSite`.** `ObligationCollector` emits one for
  every `charAt(i)` call shape; `dischargeObligationUnder` checks `0 <= i < stringLength(s)`
  on the receiver, gated on `currentScalarTypes` recognising the receiver as a String. Same
  shape as `IndexSite` for list reads, but the upper bound comes from `stringLength` rather
  than `sizeOf` (different oracle, same diagnostic — `IndexBounds`).
- **Encoder dispatch.** `s.charAt(i)` on a String-typed receiver translates to
  `stringCharAt(translate(s), translate(i))`. The CastExpression `(int) s.charAt(i)` is
  also handled — Groovy's char-vs-int distinction shows up at return paths where the
  method's declared return type is `int`.

**Demos shipped with the tests:**

- `"hello".charAt(0)` folds to 104 outright (literal pin).
- A wrong-codepoint claim refutes (`"hello".charAt(0) == 65` is provably false).
- An out-of-bounds index refutes with the IndexBounds diagnostic.
- A `charAt(0) == X` precondition flows to the body — symbolic charAt is just an
  uninterpreted function on the receiver, so the user's assumption echoes through.

**Known limits.**

- *Since closed by Phase 47 (Z3 string theory): structural cross-string axioms, substring, concat.*
- **`String.format`-like content reasoning** is out of scope and a `groovy-typecheckers`
  sibling (`FormatStringChecker`) owns that territory.

## Phase 47 — Z3 string theory adoption  *(shipped)*

Phases 46a–c built up string support through *uninterpreted* functions over an
*uninterpreted* `String!Sort`: predicates as `startsWith$ / endsWith$ / strContains$`,
length as `strLength$`, and three hand-stated universally-quantified axioms tying them
together (non-negativity, prefix / suffix length bounds). Phase 46e extended the same
shape to `charAt$` with per-position literal pinning capped at 64 chars.

The whole pyramid is retired in Phase 47. **`declareSort('String')` now returns Z3's
native string sort** — the `Seq Char` type the SMT-LIB string theory operates on. Every
operation routes through Z3's built-in primitives rather than handrolled functions plus
axioms:

| Operation | Pre-47 (uninterpreted) | Post-47 (native) |
|---|---|---|
| `s.startsWith(p)` | `startsWith$(s, p) : Bool`, length-bound axiom | `(str.prefixof p s)` |
| `s.endsWith(q)` | `endsWith$(s, q) : Bool`, length-bound axiom | `(str.suffixof q s)` |
| `s.contains(sub)` | `strContains$(s, sub) : Bool` | `(str.contains s sub)` |
| `s.length()` | `strLength$(s) : Int`, non-negativity axiom, literal pin | `(str.len s)` |
| `s.charAt(i)` | `charAt$(s, i) : Int`, per-position literal pin capped at 64 | `(char.to_int (seq.nth s i))` |
| `"foo" != "bar"` | Pairwise-distinct cascade O(n²) per sort | Theory-distinct |
| `"hello".length() == 5` | Mint-time pin | Theory consequence |
| `s + t` | Out of fragment | `(str.++ s t)` |
| `s.substring(b, e)` / `s.substring(b)` | Out of fragment | `(str.substr s b (e-b))` / `(str.substr s b (len(s)-b))` |

**The headline win — structural cross-string facts that the uninterpreted approach
explicitly couldn't reach.** With native theory, `s.startsWith(t) ∧ i < t.length()`
*structurally implies* `s.charAt(i) == t.charAt(i)`. Phase 46c's known-limits section
called this out as deferred — it now verifies as a free theory consequence:

```groovy
@Requires({ s != null && t != null && s.startsWith(t) && t.length() > 0 })
@Ensures({ result == 1 })
static int f(String s, String t) {
    s.charAt(0) == t.charAt(0) ? 1 : 0   // verifies — theory consequence
}
```

The full conjunction `prefixof(t, s) ⟹ ∀ i. 0 <= i < length(t) ⟹ at(s, i) == at(t, i)`
falls out of Z3's seq theory natively.

**Co-shipped — substring + concat with bounds**.

- `s + t` (operator) and `s.concat(t)` (method) both dispatch to `stringConcat`. The encoder's
  `translateBinary` detects when both PLUS operands are String-typed and routes to
  `mkConcat([...] as SeqExpr[])` — the explicit array picks Z3's varargs-Seq overload over
  the same-named BitVec one (Groovy static dispatch otherwise picks the BitVec form and
  Z3 rejects at runtime).
- `s.substring(begin, end)` and `s.substring(begin)` dispatch to `stringSubstring`. Groovy
  uses `(begin, end)` indices; Z3's `str.substr` uses `(offset, length)`. The encoder
  converts: `length = end - begin` for the two-arg form, `length = stringLength(s) - begin`
  for the single-arg form.
- A new `StringSubstringSite` synthesises `0 <= begin <= end <= length(s)` (or
  `0 <= begin <= length(s)` for single-arg) as one conjunctive bounds obligation — same
  `IndexBounds` diagnostic as charAt and list reads.

**The encoder's `isStringReceiver` helper grew two cases**: it now recognises
`s + t` (`PLUS` BinaryExpression with both operands String-typed) and `s.substring(...)` /
`s.concat(...)` (string-returning methods on a String receiver) as themselves String-typed
expressions. This lets `(s + "x").length()` and `s.substring(1, 4).length()` resolve
correctly — the chained call's receiver is recognised as a String, and the dispatch threads
through.

**Counterexample rendering** for String-sorted variables now uses Z3's native
`Expr.getString()` on the model-evaluated handle, rather than the Phase-27 reverse-lookup
through `sortedLits`. Cleaner and never confused by Z3-synthesised constant names.

**Soundness boundary preserved.** Z3's string theory is **decidable for many fragments
but undecidable in general** — particularly mixing word equations with length constraints
in awkward ways. The verifier inherits this: a query that's theoretically undecidable
returns `UNKNOWN`, which surfaces as "could not decide" — never a silent pass and never an
unsound verify. The shipped tests verify in well under the per-VC timeout; the full suite
runs in ~37s as before.

**Known limits.**

- *Since closed: regex `matches`/`replace` (Phase 47b–c), `indexOf` (47b), `lastIndexOf`
  (47f, uninterpreted + weak axioms).*
- **No `split`.** Returns an array, structurally invasive; deferred.
- **`charAt(i)` returns int (codepoint), not `char`.** The encoder's `CastExpression`
  handler (Phase 46e) bridges `(int) s.charAt(i)`; comparing `s.charAt(0) == 'h'` directly
  works in Groovy because char-to-int promotion happens at the language level.
- **Performance.** Z3's string solver isn't QF_LIA — some queries can hang. Per-VC timeouts
  guard the build; the full self-test suite stays at ~30-45s.

## Phase 47b — `replace` + `indexOf` dispatch  *(shipped)*

Two direct-dispatch additions on top of Phase 47's native theory:

- **`s.replace(old, new)`** → `(str.replace s old new)` via Z3's `mkReplace`. Replaces the
  *first* occurrence; the distinct *replace-all* method (`s.replaceAll`) is a separate operation,
  shipped uninterpreted-with-axioms in Phase 47f. Tests use single-occurrence patterns where the
  two semantics coincide ({@code "hello".replace("l", "P") == "hePlo"}, since only the leftmost 'l' is
  replaced — but the test verifies that exactly).
- **`s.indexOf(sub)` and `s.indexOf(sub, fromIndex)`** → `(str.indexof s sub fromIndex)` via
  `mkIndexOf`. Returns the leftmost position `>= fromIndex`, or `-1` if absent. Single-arg
  form uses `fromIndex = 0`. No bounds obligation — `-1` is a legitimate return.

`isStringReceiver` extended to recognise `s.replace(...)` as String-typed, so a chained
`s.replace("a", "b").length()` resolves correctly.

**Shipped tests** include {@code "hello".replace("l", "P") == "hePlo"} (literal folding),
{@code s.replace("XYZQ", "A") == s} under {@code !s.contains("XYZQ")} (no-op identity),
{@code "hello".indexOf("l") == 2}, {@code "hello".indexOf("l", 3) == 3} (from-index skip),
{@code "hello".indexOf("X") == -1}, and a cross-string bound {@code s.indexOf(t) >= -1}.

## Phase 47c — `matches` with a limited regex parser  *(shipped)*

The big-ticket deferred item from Phase 47. Z3 has a full regex theory (`re.*`); the
problem is that Groovy regex literals are *Java regex strings*, not Z3 regex AST — they
need parsing. Phase 47c ships a small recursive-descent parser inside `Encoder`:

**Grammar supported:**

```
regex  ::= alt
alt    ::= concat ( '|' concat )*
concat ::= quantified*                          -- empty concat = empty-string regex
quantified ::= atom ( '*' | '+' | '?' )?
atom   ::= LITERAL | '.' | '\' ANY-LITERAL | '(' regex ')' | '[' charclass ']'
charclass ::= ( LITERAL | LITERAL '-' LITERAL )+
```

Translation pipeline:

1. The encoder's String-receiver dispatch sees `s.matches(arg)`.
2. If `arg` is a `ConstantExpression` String, the parser walks it bottom-up, calling the
   `SmtSession` regex constructors (`reToRe`, `reUnion`, `reConcat`, `reStar`, `rePlus`,
   `reOption`, `reRange`, `reAllChar`).
3. The result is a Z3 `ReExpr`, fed to `mkInRe(s, re)` to produce a Bool.
4. Any parse error or unsupported feature → null → honest skip with the standard
   "outside fragment" diagnostic.

**What the shipped parser does NOT handle** (each is a graceful skip, not a silent pass):

- Anchors `^` / `$` — but `String.matches` is whole-string-anchored already, so the absence
  is mostly fine.
- Predefined classes `\d` / `\w` / `\s` / `\b` and their negations. Z3 has primitives;
  the parser doesn't yet wire them in.
- Negated character classes `[^…]`.
- Quantified ranges `{n,m}`.
- Backreferences `\1` / `(?P<name>…)`.
- Lookahead / lookbehind `(?=…)` / `(?<!…)`.
- Inline flags `(?i)` / `(?m)`.

**Tie-in with `RegexChecker`.** `RegexChecker` is the sibling `groovy-typecheckers`
extension that validates regex *syntax* at compile time (catching `Pattern.compile("[")`
as broken). Three composition shapes are interesting, in increasing depth:

1. **Orthogonal composition (today).** `RegexChecker` validates the regex literal is
   well-formed; this checker (Phase 47c) translates the well-formed regex into a Z3
   constraint. They ride the same `@TypeChecked(extensions = …)` SPI and stack. A regex
   literal flagged broken by `RegexChecker` would also be rejected by Phase 47c's parser
   (graceful skip); neither tool is load-bearing for the other.
2. **Shared parser (future).** Both tools parse the same regex strings into ASTs. A shared
   parsing module — possibly in a third package both depend on — would dedup the work
   and guarantee feature-coverage parity. Out of scope for this phase; called out as a
   small cleanup for whoever owns the multi-checker tree.
3. **Feature-coverage handoff (future).** If `RegexChecker`'s parser covers `\d` /
   negated classes / etc. and Phase 47c's doesn't yet, the encoder could *defer* to
   `RegexChecker`'s AST when available — a graceful upgrade as the sibling tool grows.
   Again, out of scope here.

For the shipped phase, the two are complementary: `RegexChecker` for "is your regex
syntactically valid" and Phase 47c for "is this `s.matches(pattern)` provable in your
contract." A program that benefits from both stacks both extensions in its
`@TypeChecked(extensions = ['verification.VerifyChecker', 'typecheckers.RegexChecker'])`.

**Known limits.**

- ~~Limited parser grammar~~ — *most common features closed by Phase 47d below.*
- Dynamic regex strings (`s.matches(variableRegex)`) skip — translation requires the regex
  text be statically known. A field with a `final String PATTERN = "…"` could in principle
  be const-folded, but the encoder's pure-fold path doesn't currently reach into static
  field initialisers.

## Phase 47d — Regex feature expansion  *(shipped)*

Extends the Phase 47c recursive-descent parser with the features users actually reach for:

- **Predefined character classes**: `\d` → `[0-9]`, `\w` → `[a-zA-Z0-9_]`, `\s` → ASCII
  whitespace set (space, tab, LF, CR, FF, VT). The capital-letter complements (`\D`, `\W`,
  `\S`) are single-character complements: `mkIntersect(reAllChar, mkComplement(class))`.
- **Negated character classes**: `[^abc]`, `[^a-z]`. Same single-character-complement
  treatment as the predefined complements — parse the inner class as positive, then
  invert.
- **Quantified ranges**: `{n}`, `{n,m}`, `{n,}` via Z3's `mkLoop`. The two-int form
  bounds both sides; the single-int form is open-upper-bound.
- **Anchors `^` and `$`** as silent no-ops. `String.matches` is whole-string anchored, so
  top-level anchors are redundant; mid-position they're tolerated as the empty-string
  regex (matches only "", which composes correctly with concat).

`SmtSession` grew three regex constructors: `reComplement(re)`, `reIntersect(a, b)`,
`reLoop(re, lo, hi)` / `reLoopAtLeast(re, lo)`. All four map to Z3 primitives
(`mkComplement` / `mkIntersect` / `mkLoop` with two overloads).

**Still deferred**: word-boundary anchors (`\b`, `\B`), inline flags (`(?i)` / `(?m)`),
backreferences, lookahead / lookbehind. Each is structurally larger than the recursive
parser handles today; honest-skipped for now.

**Shipped tests**: `\d+` matches digits / rejects letters, `\w+` matches alphanumeric +
underscore, `\s+` matches whitespace, `\D+` rejects digits, `[^0-9]+` matches non-digits,
anchors as no-op (`^abc$` ≡ `abc`), `a{3}` matches exactly three, `a{2,4}` range,
`a{2,}` open-upper.

## Phase 47e — Integer ↔ String conversion  *(shipped)*

Maps `Integer.toString(n)` / `n.toString()` (when statically dispatched) /
`String.valueOf(int)` to Z3's `intToString`; `Integer.parseInt(s)` to Z3's `stringToInt`.
Receiver discrimination handles all three AST shapes the type-checker produces:
`VariableExpression` (unresolved), `PropertyExpression` (FQN), `ClassExpression`
(post-resolution). `isStringReceiver` extended to recognise these as String-producing
expressions, so `Integer.toString(n).length()` resolves correctly.

**Semantic gaps — *closed* in [Phase 54](#phase-54--sign-faithful-integer-tostring--parseint-shipped).**
At this phase the conversions were the raw Z3 primitives, whose SMT-LIB semantics diverge from Java
for negatives: `int.to.str(-5)` is `""` (Java `"-5"`), and `str.to.int` is `-1` for any
non-`[0-9]+` string. That was **silent unsoundness** (the engine *verified* `Integer.toString(n <
0).isEmpty()`). Phase 54 threads the sign explicitly and adds a loud well-formedness obligation; the
round-trip `parseInt(toString(n)) == n` now holds for *all* `n`.

**Shipped tests**: `Integer.toString(5) == "5"`, `String.valueOf(42) == "42"`,
`Integer.parseInt("123") == 123`, `Integer.parseInt("abc") == -1` (Z3 semantics),
wrong-value refute, round-trip `parseInt(toString(n)) == n` under `n >= 0`.

## Phase 47f — `replaceAll` + `lastIndexOf` as uninterpreted  *(shipped)*

Z3 has no native `mkReplaceAll` and no `mkLastIndexOf`. Phase 47f ships both as
*uninterpreted functions with weak universally-quantified axioms* — sound
under-approximations: the verifier knows less than Z3 native would if it had the
primitive, but everything it does know is true.

**`replaceAll(s, old, new)` — axioms asserted on first use:**

1. `¬contains(s, old) ⟹ replaceAll(s, old, new) == s`. When the target isn't present,
   the result is the input. (Cleanest single fact we can carry without a primitive.)
2. `length(old) == length(new) ⟹ length(replaceAll(s, old, new)) == length(s)`. Length
   preservation under same-size swaps — the single-character `s.replaceAll("a", "b")`
   case, common in practice.

**`lastIndexOf(s, sub, fromIndex)` — axioms asserted on first use:**

1. `lastIndexOf(s, sub, from) >= -1`. The return is a valid sentinel-or-position.
2. `¬contains(s, sub) ⟹ lastIndexOf(s, sub, from) == -1`. Absent means -1.

Each axiom has a single-`mkPattern` trigger on the call term, so Z3 instantiates only at
ground call sites that already appear in the proof — no blind-fire over the Herbrand
universe.

**Soundness boundary.** The axioms are deliberately minimal. A specification that needs
finer reasoning ("`replaceAll(s, "a", "b").charAt(i)` is either `s.charAt(i)` or `'b'`")
will skip — there's no axiom that connects post-replace `charAt` to pre-replace `charAt`.
Tests cover the axiomatic facts and a refute for "claiming length-preservation under
unequal-length swap" — explicitly *not* provable.

**Future upgrade path.** When Z3 ships `mkReplaceAll` (and a `lastIndexOf` primitive), the
uninterpreted functions and axioms in `Z3Backend` swap out for native dispatch in one
edit — same shape as Phase 47's swap-out of the Phase 46a–c hand-axiomatized predicates.

**Build cost.** The Phase 47f axioms add modest quantifier load. Axioms are gated so
they're asserted only when a replaceAll / lastIndexOf call appears, keeping methods that
don't use either feature unaffected.

**Shipped tests**: `replaceAll(s, "XYZ", "A") == s` under `!s.contains("XYZ")`,
length-preservation under `replaceAll("a", "b")`, refute under
`replaceAll("a", "bc").length() == s.length()` (unequal-length not provable),
`lastIndexOf(s, t) >= -1`, `lastIndexOf == -1` when absent.

## Phase 47g — ASCII case folding (`toUpperCase` / `toLowerCase` / `equalsIgnoreCase`)  *(shipped)*

Z3's seq theory has no case-folding primitive — there's no `str.upper` or
`str.case-fold`. Phase 47g ships hybrid coverage built on uninterpreted functions plus
exhaustive literal pinning at mint, all done under `Locale.ROOT` (ASCII-faithful — no
Turkish-locale `i`/`İ` surprise).

**The shipped surface:**

- `s.toUpperCase()` → `toUpper$(s)` uninterpreted.
- `s.toLowerCase()` → `toLower$(s)` uninterpreted.
- `s.equalsIgnoreCase(t)` lowers to `toLower$(s) == toLower$(t)` — no separate session
  method; the encoder lowers directly. ASCII-faithful since both sides use the same
  `toLower$` definition.

**Per-literal pinning at the backend's `litOfSort` mint site.** When `"Hello"` is interned
for the first time and case ops are in play, the backend asserts:

- `toUpper$(mkString("Hello")) == mkString("HELLO")`
- `toLower$(mkString("Hello")) == mkString("hello")`

…and recursively pins the derived `"HELLO"` and `"hello"` literals' case forms. The
`stringLiteralKeys` set tracks what's already minted so the recursion is bounded; the case
universe closes after every literal's idempotent and case-swapped forms exist. The pinning
is gated — only fires when `toUpper$` or `toLower$` has been declared (lazy on first
encoder reference).

**Why no universal axioms.** First try was length-preservation
(`∀s. length(toUpper(s)) == length(s)`), idempotence
(`∀s. toUpper(toUpper(s)) == toUpper(s)`), and cascade
(`∀s. toUpper(toLower(s)) == toUpper(s)`). Z3's seq theory + universals over the seq sort
interacted poorly: literal-only refutes like `"Hello".toUpperCase() == "hello"` timed out
at 2s.

A standalone probe (`./gradlew caseAxiomTiming` — kept as forensic evidence) confirmed
this is **not** a slow-laptop issue:

| Scenario | Result |
|---|---|
| Positive equation, no axioms | UNSAT in 1ms |
| Positive equation, 6 universal axioms | UNSAT in 0ms |
| **Negated equation, no axioms** | SAT in 9ms |
| **Negated equation, length axioms (2)** | UNKNOWN at 60000ms |
| **Negated equation, all 6 axioms** | UNKNOWN at 60000ms |

The asymmetry is structural: the *positive* direction (proving `toUpper("Hello") == "HELLO"`)
unifies the conjecture against the literal pin and finishes in microseconds either way. The
*negated* direction (which is how the verifier discharges a refute test, asking SAT for the
negated postcondition) needs Z3 to construct a model for the uninterpreted seq-to-seq
function that satisfies the universal for *all strings*. That construction blocks
indefinitely — any timeout, any axiom set involving the universal, same result. Bumping the
verifier's per-VC timeout doesn't help.

Resolution: ship literal-pin-only. The cost of the structural facts (symbolic length /
idempotence / cascade claims aren't reachable) is real but bounded, and the verifier stays
fast on every other proof shape. A future Z3 release with better seq+UF model construction
(or a `str.upper` / `str.lower` primitive) could close the gap; the uninterpreted form
swaps out cleanly when that happens.

**What this covers (and what it doesn't):**

| Shape | Status |
|---|---|
| `"Hello".toUpperCase() == "HELLO"` | ✅ literal pin |
| `"HELLO".toLowerCase() == "hello"` | ✅ literal pin |
| `"Hello".equalsIgnoreCase("HELLO")` | ✅ both lower to `"hello"`, pin |
| `s.equalsIgnoreCase(s)` (reflexive) | ✅ pointwise term equality |
| `s.toLowerCase() == t.toLowerCase() ⟹ s.equalsIgnoreCase(t)` | ✅ direct lowering |
| `s.toUpperCase().length() == s.length()` for symbolic `s` | ❌ would need universal |
| `s.toUpperCase().toUpperCase() == s.toUpperCase()` for symbolic `s` | ❌ would need universal |
| Non-ASCII case folding (locale-specific) | ❌ ASCII-only via `Locale.ROOT` |
| `s.toUpperCase().charAt(i)` claims | ❌ no per-position axiom |

**Known semantic gap.** `Locale.ROOT` matches what most programs assume but is *not*
necessarily what `s.toUpperCase()` does at runtime if the JVM's default locale is, say,
Turkish (`i` → `İ` rather than `I`). Users running under non-default locales should
either set `Locale.ROOT` explicitly or be aware that the verifier reasons under
ASCII semantics. This is the documented compromise — the user explicitly asked for
"standard ASCII, less worried about charsets like tr_TR".

**Build cost.** The recursive literal pinning expands the literal universe (each new
String literal triggers its upper / lower forms). The expansion is bounded — closes once
no new literals appear in the source.

**Future upgrade paths.** A `toUpperChar$(c)` uninterpreted function with an ASCII case-folding
axiom over `[A-Z]` / `[a-z]` codepoints, paired with a universal that ties
`charAt(toUpper(s), i) == toUpperChar$(charAt(s, i))`, could close the per-position gap.
Alternatively a future Z3 release shipping `str.upper` / `str.lower` would let the
uninterpreted functions retire entirely — same shape as Phase 47's swap-out of
Phase 46a–c hand axioms.

**Shipped tests**: literal toUpperCase / toLowerCase folding (both directions), wrong-case
refute, literal length identity, literal equalsIgnoreCase (matching pairs and distinct
pairs), reflexive equalsIgnoreCase, symbolic equalsIgnoreCase via toLower equality.

## Phase 47h — GString interpolation  *(shipped)*

Groovy's `"hello $name"` parses as a `GStringExpression` (not a `ConstantExpression`) with
two parallel lists: static text fragments and interpolated value expressions. The runtime
value is a `GStringImpl` that implements `CharSequence` and compares equal to a `String`
of the same content. Phase 47h translates the AST shape to chained `str.++` from Phase 47's
seq theory.

**Translation pipeline.**

- The static parts (`gs.strings`) are `ConstantExpression`s of String type — mint via
  `mkString` through the existing `litOfSort` route.
- Each interpolated value (`gs.values[i]`) goes through `translateValueAsString`:
  - If `isStringReceiver(v)` recognises it (String literal, String param, `s + t`,
    `s.substring(...)`, a nested GString, …), translate as a String term.
  - Otherwise default to Int and convert via the `intToString` dispatch — now sign-faithful
    (Phase 54), so a negative interpolated value renders as `"-5"`, matching runtime.
- The parts are folded left into a chain of pairwise `stringConcat`.

**Co-shipped fixes the implementation needed.**

1. **`collectScalarTypes` body-scan.** Typed locals like `String name = "world"` weren't
   tracked — `scalarTypes` only collected method parameters and fields. Without the
   addition, the GString interpolation of `name` would fall into the int path and crash
   Z3 with a sort mismatch. The body-scan uses the *clean pre-contract body snapshot*
   (`ContractExpansionTransform.ORIGINAL_BODY_KEY`) to avoid picking up groovy-contracts'
   injected `final String result = …` declarations, which would otherwise route `result`
   through `sortedEnv` and break dozens of pre-existing tests. Closure bodies are skipped
   as a belt-and-braces measure.
2. **`Encoder.bind` sort-aware storage.** The body-replay path's
   `enc.bind('name', stringTerm)` was putting String-sorted bindings into `env` (Int
   default), while `varForOfSort` reads from `sortedEnv`. The fix: `bind` now also writes
   into `sortedEnv` for any name whose scalar type is non-Int. Symmetric round-trip.
3. **SSA-fresh sort matching.** `checkPath`'s `Assign` step always minted
   `session.intVar('name#1')` for the SSA-fresh handle, then asserted
   `eq(fresh, rhs)` — `eq(int, string)` is a Z3 sort mismatch. The fix: when the
   variable's declared type is non-Int (per `currentScalarTypes`), mint
   `session.varOfSort('name#1', sortFor(declaredType))` instead.
4. **`isStringReceiver` recognises `GStringExpression`.** So a chained
   `"hello $name".length()` or `"$x".startsWith("0")` routes through the string-receiver
   dispatch.
5. **`collectListElementTypes` got the same clean-body + closure-skip treatment** for
   parity (the same hazard would have hit it if a user wrote `@Ensures` referencing a
   contract-injected list).

**What this unlocks.**

```groovy
@Ensures({ result == "hello world" })
static String f() { String name = "world"; "hello $name" }   // verifies via concat-fold

@Ensures({ result == 4 + Integer.toString(n).length() })
static int f(int n) {
    @Requires-decoration n >= 0
    "n = $n".length()
}   // length composes: |"n = "| + |Integer.toString(n)|

@Ensures({ result == "sum=3" })
static String f() { int a = 1; int b = 2; "sum=${a + b}" }   // ${expr} block form
```

**Known limits.**

- Boolean / null / collection interpolation falls into the int default (`null` becomes
  an int term, mismatches sorts). Honest skip — `isStringReceiver` returns false; the
  GString translation returns null overall. A small extension could special-case
  `Boolean` (`"true"`/`"false"`) and `null` (`"null"`); deferred.
- Closure-form `"${->name}"` (lazy evaluation) isn't parsed specially — falls back to
  generic translation, likely null. Rare in practice.
- *(The Phase-47e negative-int gap that once flowed through to GString — `"$x"` rendering empty
  for negative `x` — was closed in Phase 54: `intToString` is now sign-faithful, so `"$x"` for
  `x == -5` is `"-5"` in the verifier's view as well.)*

**Shipped tests**: literal String / int interpolation folding, multi-interpolation
(mixed types), length composition (literal + symbolic), GString-equals-String
literal, refute on wrong interpolation, `${expr}` block-form expression, chained
`.startsWith` through string-receiver dispatch.

## Phase 47i — `String.reverse()` (algebraic, literal pinning)  *(shipped)*

The GDK adds `reverse()` to `String`. Z3's seq theory has no native reverse, so — exactly
like case folding (47g) — `reverse$ : String → String` is an **uninterpreted function with
per-literal pinning**. Every minted literal asserts `reverse(lit) == mkString(rev(key))` at
the `litOfSort` site (Java `StringBuilder.reverse`), and the pinning is **bidirectional** (the
reversed literal is minted and pinned too). That alone gives, as theory consequences:

```groovy
@Ensures({ result == "cba" })       static String f() { "abc".reverse() }            // literal
@Ensures({ result == "racecar" })   static String f() { "racecar".reverse() }        // palindrome
@Ensures({ result == "abc" })       static String f() { "abc".reverse().reverse() }  // literal involution
@Ensures({ result == 5 })           static int    f() { "hello".reverse().length() } // literal length
```

`isStringReceiver` learned that `reverse` returns a String (so chained `.reverse().reverse()`
/ `.reverse().length()` route through the string path).

**Why no universals — confirmed by probe, not just inherited from 47g.** The algebraic
identities a reader wants — symbolic involution `s.reverse().reverse() == s` and length
preservation `s.reverse().length() == s.length()` — need a *universal* over `reverse$`. A
probe added both as **triggered** universals (the same shape `replaceAll`/`lastIndexOf` ship):
they **did** make the symbolic cases prove — **but poisoned the refute direction**, exactly as
47g warned. `"abc".reverse() == "abc"` (false) went from a clean *“cannot prove postcondition”*
to a **solver timeout** (*“could not decide”*): Z3's seq solver stalls building a model that
satisfies a universal over a `Seq→Seq` uninterpreted function. A false spec deserves a crisp
refute, not a confusing stall, so the universals are out. Literal pinning ships; symbolic
algebra is a documented boundary (two `does NOT prove (boundary)` tests pin the behaviour).

**The genuinely valuable cousin** — proving an in-place `char[]`/`int[]` reversal *loop* — is a
different feature riding the (decidable) array-element oracle, not the string layer; its cost is
a two-ended loop invariant (`∀k<i. a[k]==old(a[n-1-k]) ∧ a[n-1-k]==old(a[k])`). Left for later.

**Shipped tests**: literal reverse, palindrome, wrong-reversal refute, literal involution,
literal length-preservation, reflexive `reverse(s)==reverse(s)`, plus two boundary tests
asserting the symbolic identities cleanly *don't* prove.

## Phase 47j — the `==~` match operator  *(shipped)*

Groovy's match operator `s ==~ regex` is a whole-string regex match — semantically identical to
`s.matches(regex)` (Phase 47c). It's a `BinaryExpression` carrying the `MATCH_REGEX` token, so it's routed
*before* the integer-operand path: the left is translated in the String sort, the right is parsed by the
inline regex parser, and both lower to the same `str.in_re`. Everything Phase 47c–d proves about `.matches`
carries over verbatim, and the equivalence `(s ==~ /[a-z]+/) == s.matches("[a-z]+")` proves (both are
`str.in_re` of the same pattern). The *find* operator `=~` (returning a stateful `Matcher`, not a boolean)
stays out.

**Shipped tests**: `result == (s ==~ /…/)` reflects the match; `==~` provably equivalent to `.matches`; a
false `==~` claim refutes.

## Phase 48 — Non-linear integer arithmetic + integer div/mod  *(shipped)*

The Phase 8a pure-NIA opt-out (refusing `a * b` when both sides are non-literal) was
conservative — written before per-VC timeouts were in place and before the suite had
demonstrated how many natural specs are blocked by the cliff. Phase 48 lifts the
restriction and adds the missing `/` / `%` dispatch.

**What changed:**

- `MULTIPLY` translates unconditionally via Z3's NIA solver. Z3's per-VC 2s timeout
  protects against the NIA-hang case — a query that doesn't terminate returns `UNKNOWN`,
  which surfaces as "Could not decide" (honest, never silent). Phase 8a's
  `tryFoldConstant` still folds closed numeric subexpressions before they reach the
  encoder, so `(2 + 2) * (2 + 2) == 16` continues to verify the fast way.
- `DIVIDE` and `MOD` dispatch to new `SmtSession.intDiv` / `intMod`, implemented as Z3's
  `mkDiv` / `mkMod`. Operator-text matching (`be.operation.text == '/'` and `== '%'`)
  rather than `Types.DIVIDE`/`Types.MOD` — Groovy's parser doesn't assign `%` the
  `Types.MOD` token (a caveat the existing `ObligationCollector` already documented).
  > **Corrected in [Phase 50](#phase-50--groovy-faithful-division--modulo-shipped).** This
  > mapping was *Java*-shaped and unsound for Groovy: Groovy's `/` is **BigDecimal** division
  > (`5 / 2 == 2.5G`), not integer division, and `%` is the **sign-of-dividend** remainder
  > (`-5 % 2 == -1`), not Euclidean. Phase 50 re-grounds all of div/mod on Groovy semantics.

**What this unlocks** — natural shapes that previously hit the cliff:

```groovy
// Sign reasoning (Z3 NIA solves quickly).
@Requires({ a > 0 && b > 0 }) @Ensures({ result > 0 })
static int product(int a, int b) { a * b }

// Squaring is non-negative — without bounds.
@Ensures({ result >= 0 })
static int sq(int i) { i * i }

// Bounded squaring stays bounded.
@Requires({ 0 <= i && i <= 10 }) @Ensures({ result <= 100 })
static int sqBound(int i) { i * i }

// Division identity (Euclidean / truncated agree for non-negative).
@Requires({ a >= 0 && b > 0 }) @Ensures({ result == a })
static int divId(int a, int b) { (int)((a / b) * b + a % b) }

// Even-number predicate via modulo.
@Requires({ n >= 0 && n % 2 == 0 }) @Ensures({ result == 1 })
static int isEven(int n) { (n % 2 == 0) ? 1 : 0 }
```

**Known semantic gap — Java vs SMT-LIB div/mod**:

*Superseded by [Phase 50](#phase-50--groovy-faithful-division--modulo-shipped).* The original
Phase 48 mapping (`/` → `mkDiv`, `%` → `mkMod`, both Euclidean) was **Java-shaped and silently
unsound for Groovy** — it modelled `/` as integer division (Groovy gives a `BigDecimal`) and `%` as
the non-negative Euclidean remainder (Groovy is sign-of-dividend). Phase 50 re-grounds the whole
family on Groovy semantics; see it for the corrected encoding.

**Hard NIA cases still skip honestly**:

- Unbounded polynomial identities (`(a + b)² == a² + 2ab + b²` for arbitrary signed `a, b`)
  may timeout — Z3's NIA solver heuristics don't always reach them. UNKNOWN surfaces as
  "Could not decide" — never an unsound pass.
- Square-root / general factoring shapes (`a * a == n`, find `a`) hang predictably.
- Power (`a ** b` / `STAR_STAR`) isn't dispatched yet; Z3 has `mkPower` if wired.

**Co-shipped tests** (11): commutativity, positive product, square non-negativity,
bounded square bound, unbounded-square refute, bounded variable product, division floor,
modulo range, division identity, divide-by-zero refute, even predicate.

**Build cost**: unchanged at 30-45s. The NIA queries that fire are fast for the shapes the
suite exercises; the timeout protection means worst-case is bounded per VC.

## Phase 49 (Slice A) — Early-return in loop prefix  *(shipped)*

Until Phase 49, a method with an annotated loop had to be straight-line around it — any
`return` statement before or after the loop crashed `LoopEncoder.symExec` with
"ReturnStatement in loop region". That blocked the idiomatic guard pattern that opens most
HumanEval shapes (and `is_prime` was the canonical sufferer):

```groovy
if (n <= 1) return false                  // ← early-return guards before the loop
if (n <= 3) return true
if (n % 2 == 0 || n % 3 == 0) return false
int i = 5
@Invariant({ i >= 5 })
while (i * i <= n) { … }
return …
```

**The Slice A shape**: an "early-exit if" is `if (cond) return e;` (or
`if (cond) { return e; }`) with no else-branch. Anything more elaborate stays in the
existing path-fact route inside `LoopEncoder`.

**Verification.** `findLoopSite` now partitions the prefix into early-exit ifs (each
captured as an `EarlyExit { guard, result, priorStmts, priorGuards }`) and the non-exit
statements (kept in `LoopSite.prefix` for the existing `symExec` calls). Then `verifyLoop`
runs:

- `checkEstablishment` and `checkUse` get `¬each-prefix-guard` assumed before sym-exec'ing
  the kept prefix — the loop machinery only fires on the "no early-exit taken" path.
- A new `checkEarlyExit` per exit:
  1. Assume `@Requires` + class invariants.
  2. Assume `¬each-prior-guard` (we got here, not at an earlier exit).
  3. Sym-exec this exit's `priorStmts` (the non-exit statements that ran in source order
     before this guard).
  4. Assume this exit's guard.
  5. Bind `result` to the return expression and check `@Ensures`.

**Suffix exits are still deferred** (Slice B territory). The state-dependent guard
ordering — a `¬suffix-guard` assertion needs to fire AT the suffix point in the walk,
after the prior suffix statements have run, not at the start of `checkUse` — requires
restructuring `LoopEncoder.resultExpr`. The existing "unsupported statement
ReturnStatement after loop" diagnostic is the right honest skip; no soundness risk.

**Co-shipped tests** (5): single prefix early-return, multiple stacked early-returns,
postcondition violation refute, loop invariant using `¬prefix-guard`, prior assignment
running before an exit.

## Phase 49b (Slice B) — Early-return in loop body  *(shipped)*

Slice A handled prefix exits; Slice B handles **early-returns INSIDE the loop body**. This
closes the second half of the original Slice B sizing and lets `is_prime` port verbatim:

```groovy
@Requires({ num >= 0 })
static int isPrime(int num) {
    if (num <= 1) return 0                      // ← Slice A (prefix exits)
    if (num <= 3) return 1
    if (num % 2 == 0 || num % 3 == 0) return 0
    int i = 5
    @Invariant({ i >= 5 })
    while (i * i <= num) {
        if (num % i == 0 || num % (i + 2) == 0) return 0   // ← Slice B (in-body exit)
        i = i + 6
    }
    return 1
}
```

**The shape**: same `if (cond) return e;` (no else, then-block a single return) as
Slice A, recognised at the top level of the loop body.

**The verification has three parts**:

1. **Preservation / progress on the no-exit-fired path.** Rather than calling
   `LoopEncoder.symExec(spec.body, …)` directly, a new `symExecBodyWithExits` walks the
   body's top-level statements: an early-exit `if` asserts `¬guard` (we didn't take this
   exit); everything else defers to the existing `LoopEncoder.symExec` (Phase 45c
   snapshot/restore for non-exit ifs is preserved). At the end of the body walk, the
   invariant is checked / variant decrease is asserted as before. The interleaving keeps
   `¬guard` assertions consistent with the state at the point each guard is evaluated.

2. **Per-exit `@Ensures` check.** `checkEarlyExit` gets a new `region == 'inBody'`
   branch. Critically — and the bug that nearly shipped — the **prefix is NOT
   sym-exec'd** for in-body exits: the loop invariant abstracts the post-prefix state.
   Sym-exec'ing the prefix would over-constrain values (e.g. binding `i = 0` from
   `int i = 0` in the prefix, then asserting `i == 5` in an in-body exit's guard, would
   make the assertion set UNSAT and vacuously verify any postcondition). The correct
   shape: assume invariant ∧ loop-guard, walk body up to this exit interleaving
   `¬each-prior-in-body-guard` with sym-exec of non-exit body statements, then assume
   this exit's guard and bind `result`.

3. **`checkUse` unchanged**. In-body exits exit the *method*, not the loop. The natural
   post-loop path (`invariant ∧ ¬loop-guard ∧ suffix`) doesn't need to know about them.

**The bug worth noting in the design diary**: shipping point 2 incorrectly with the
prefix sym-exec'd caused the soundness-violation test ("in-body return of `-1` against
`@Ensures({ result >= 0 })`") to *pass* (vacuously), not refute. The diagnostic — same
test refuting cleanly after removing the prefix walk — is what surfaced the issue. Worth
remembering whenever a checker adds new path-discovery: vacuous verification is the
quiet failure mode.

**Co-shipped tests** (4): single in-body early-return, postcondition-violation refute,
preservation on the no-exit body path (find-first-negative-index shape), multiple
stacked in-body returns.

**Still deferred**: suffix exits (the original Slice B's other half), and in-body
returns nested inside other if-branches or for-loops. The nested form would need the
partition logic to recurse, which adds complexity for a relatively rare shape.

## Phase 49c (Slice C) — Tail-position nested early-return; binary search verbatim  *(shipped)*

Dafny's flagship tutorial proof, **binary search**, now ports structure-for-structure (`else return mid`
inside the loop, `return -1` after) and verifies — both postcondition directions, the excluded-region
universal preserved across the narrowing, every `a[mid]` bound, and termination. (This is the development
diary behind the README's binary-search example; the README itself keeps only the comparison-relevant
result and the one authoring subtlety.) Getting there took three fixes, and two of the things that
*looked* like blockers weren't:

1. **Sortedness transitivity — the recognised `Sorted` predicate.** The *natural* one-dimensional port of
   `sorted` (adjacent form `(1..<a.length).every { a[it - 1] <= a[it] }`) **times out** in preservation:
   narrowing `low := mid + 1` needs `a[i] ≤ a[mid] < value` for *all* `i ≤ mid`, which is range
   transitivity — induction, not one instantiation (the same wall the insertion-sort proof crosses only
   via the explicit recursive ghost lemma `maxBound`, Phase 14). The fix is a recognised sortedness
   predicate emitting the *two-dimensional* axiom `∀ j,k. 0 ≤ j < k < n ⟹ a[j] ≤ a[k]` with an explicit
   multi-pattern trigger `{a[j], a[k]}`, so the gap fact `a[i] ≤ a[mid]` fires in a single deterministic
   instantiation the moment both selects are ground. Written natively as `a.isSorted()` (Groovy 6 GDK,
   native `int[]`/`long[]` overloads; `a.sorted` property too) or explicitly as `Sorted.ascending(a)` /
   `.descending` / `.strictlyAscending` (`verification.Sorted`, a sibling of `Forall`/`Sets`). Without it,
   preservation refutes on a concrete unsorted counterexample (`[7719, 7718]`).

2. **A precision bug in obligation discharge — the real culprit.** The `a[mid]` bounds obligation inside
   the `else if (value < a[mid])` branch was checked with `mid` **havoced**, producing a spurious
   `IndexOutOfBounds` with the tell-tale `mid = -1`. Cause: when the loop-body obligation walker recursed
   into an `else if`, it restarted its "preceding statements" list empty, dropping the `int mid = …`
   declaration that ran before the `if`. Threading the enclosing prefix through the recursion fixes it —
   and the fix is general (any obligation nested in an `else if` now sees the bindings that precede the
   chain), not binary-search-specific.

3. **The midpoint `intdiv` — a *non*-issue.** An earlier reading fingered integer division in the loop
   region as the blocker; that was wrong. `mid = low + (high - low).intdiv(2)` models fine inside a loop —
   the `mid = -1` counterexample that *looked* like a havoced division was the else-if-discharge bug
   above. Worth recording as a caution: a havoced-variable counterexample points at *where the binding was
   lost*, which isn't always the operation it's attached to.

The real new capability was **lifting the nested `return`.** Phase 49b recognised only a `return` at the
*top* of the loop body (`if (g) return e`); binary search's `else return mid` is the deepest leaf of an
`if`/`else if` chain, which used to skip the whole loop loudly. Phase 49c desugars a tail-position chain by
lifting each returning leaf into the top-level shape — `if (pathCond) return e`, where `pathCond` is the
conjunction of branch guards reaching it (`!(a[mid] < value) && !(value < a[mid])` here) — followed by the
same chain with the return replaced by an empty statement. The existing machinery then checks the lifted
exit's `@Ensures` on its own path and excludes it from preservation, unchanged.

**Caution (design diary):** the lifted node is synthetic, and a diagnostic anchored to a node with no
source position is *silently dropped* — so a wrong exit spec falsely "verified" until the node was stamped
with a real position. The `else return mid` claiming `a[result] != value` now refutes, as it must. A
`return` nested in a *non*-tail position is still out of fragment — it skips loudly, never silently. So
Dafny's verbatim binary search verifies, structure-for-structure.

## Phase 50 — Groovy-faithful division / modulo  *(shipped)*

Phase 48 mapped the `/` and `%` *operators* to integer `mkDiv` / `mkMod` (Euclidean) — a *Java*
model. Groovy's arithmetic is different, and the mismatch was **silently unsound**: the verifier
could return a green "verified" for a program that fails at runtime (e.g. `@Ensures({ result >= 0 })
int rem(int a) { a % 3 }` — `rem(-7) == -1`). Phase 50 re-grounds the whole family on Groovy's actual
semantics (confirmed against `org.codehaus.groovy.runtime.typehandling.IntegerMath`):

| Groovy form | semantics | encoding |
|---|---|---|
| `a / b` (operator) | **`BigDecimal` division** (`5 / 2 == 2.5G`) — `IntegerMath.divideImpl` → `BigDecimalMath` | Z3 exact **Real** sort (Phase 61) — `5 / 2 == 2.5` proves |
| `a % b`, `a.remainder(b)` | remainder, **sign of dividend** (`-5 % 2 == -1`) | `intRem` (truncated) |
| `a.intdiv(b)`, `(int)(a / b)` | integer division, **truncate toward zero** (`(-7).intdiv(2) == -3`) | `intDiv(a − intRem(a,b), b)` (exact ⇒ truncates) |
| `a.mod(b)` | **`BigInteger.mod`**: non-negative, **divisor must be > 0** (else `ArithmeticException`) | `intMod` (Euclidean) + a `b > 0` obligation |

Implementation notes:
- `intRem` is **built from the (non-negative) Euclidean `mkMod`** — `rem = (a >= 0 ∨ mod == 0) ? mod :
  mod − |b|` — because Z3's own `mkRem` does *not* follow the dividend's sign. Correct for all signs.
- The `/` operator returns `null` from the encoder at this phase (BigDecimal unmodelled); its `b != 0`
  safety obligation is still collected. *(Superseded: Phase 61 models `/` via Z3's exact Real sort, and
  Phase 73 models `double`/`float` via Z3's FP theory — neither is a non-goal any more.)* `(int)(a / b)` —
  the idiomatic truncating-int-div — is recognised at the `CastExpression` and routes to `intDiv`.
- `.intdiv` / `.remainder` carry a `b != 0` obligation; `.mod` carries `b > 0`
  (`Reporter.formatModulusNotPositive`), a Groovy-specific bug class. Both are `DivideSite`s, so the
  receiver's (numeric) nullity isn't spuriously checked.
- The "division identity" anchor became `a.intdiv(b) * b + (a % b) == a` (true for all `b != 0`) —
  the BigDecimal form `(a / b) * b + a % b` does **not** equal `a` in Groovy (`(5/2)*2 + 5%2 == 6`),
  so the old anchor was asserting a falsehood that only held under the mis-model.
- Soundness regression guard: `@Ensures({ result >= 0 }) int f(int a) { a % 3 }` now **refutes**
  (it wrongly verified before). A "divergent-semantics audit" lane (P50 group) anchors each form.

This closes the one place the engine could be *confidently wrong* rather than honestly silent —
restoring the "loud unsoundness" promise across all of integer arithmetic.

---

## Phase 51 — Numeric sum aggregation over a list  *(shipped)*

The engine had *occurrence*-count aggregation (`count` / `bcount` / `Sets.boundedCount`) but no
**value-sum** — so the textbook loop-invariant pattern `s == sum(a[0..i))` couldn't even be stated.
That blocked a whole class of HumanEval tasks (3 `below_zero`, 8 `sum_product`, 60 `sum_to_n`) and
everyday totals/averages/running-balances. Phase 51 adds it, mirroring the `bcount` machinery.

**Surface (Groovy-idiomatic):**
- `xs[lo..<hi].sum()` — the bounded / prefix sum, the natural spelling inside a loop `@Invariant`.
- `xs.sum()` — the whole-list sum (≡ `xs[0..<xs.size()].sum()`), used in `@Ensures`.

**Encoding:** an uninterpreted `sumArr$ : (Array, Int, Int) → Int`, with two defining axioms asserted
mint-once per array handle, quantified over all ranges (triggered on the `sum$` application):
- base — `∀ l,h. h <= l ⟹ sum(arr,l,h) == 0`
- step — `∀ l,h. l < h ⟹ sum(arr,l,h) == sum(arr,l,h-1) + arr[h-1]`

The step axiom is what makes `s == sum(arr,0,i)` survive `s = s + a[i]; i = i+1`: at `i+1` it
e-matches to `sum(arr,0,i+1) == sum(arr,0,i) + a[i]`, exactly the body's update. The headline proof —
a running total provably equals the whole-list sum — verifies; so does a literal-bounded range sum
unfolding to its elements (`xs[0..<2].sum() == xs[0] + xs[1]`).

**Honest limitations:**
- **`sum()` is duck-typed — Int *and* String are modelled.** Groovy's `sum()` folds with `plus`, so
  `[1,2,3].sum() == 6` is numeric sum while `['a','b','c'].sum() == 'abc'` is *String concatenation*.
  The dispatch branches on the element type (`listElementTypes`): an Int list lowers to `sum$`, a
  String list to **`strConcat$`** — the same base/step shape over the String monoid (base `""`, step
  `concat(l,h-1) ++ arr[h-1]` via the Phase-47 `str.++`), so a running concatenation provably equals
  the whole-list `sum()` exactly like the numeric running total. Any *other* element domain (enum,
  etc.) has no aggregation monoid here and honestly **skips** rather than hitting a Z3 sort mismatch.
- **Groovy `[].sum()` is `null`, not `0`.** The no-arg `sum()` models the empty range as `0` (so a
  spec evaluating it on a possibly-empty range needs a non-empty guard for *runtime* fidelity). The
  **`sum(initial)` form is also recognised** (`xs[lo..<hi].sum(0)` → `0 + sum$(arr,lo,hi)`): since
  `[].sum(0) == 0` at runtime, it's the runtime-safe spelling for specs that genuinely range over the
  empty prefix (e.g. `below_zero`'s balance-before-any-operation).
- **GDK `sum()` is typed `Object`.** So `xs.sum() == …` works (Groovy `==` is lenient) but a
  *comparison* `xs.sum() < 0` doesn't type-check — it needs an explicit `(int)` cast. A Groovy
  type-system reality, not a verifier limit; the cast is transparent to the encoder.

**Capstone — HumanEval 3 (`below_zero`).** The sum primitive composes with bounded `∀`/`∃` and the
early-return-in-loop (Phase 49) to verify the *full biconditional* `result ⟺ ∃ prefix. sum < 0`: the
early `return true` witnesses the `any`, and a "no prefix negative yet" `every`-invariant carries the
converse to the `return false` path. Verifies end-to-end (the tight biconditional self-anchors — a
wrong body wouldn't satisfy it), using the runtime-safe `sum(0)` + the `(int)` cast above.
- **`xs.sum()` as a method *body* returning `int` doesn't type-check** under `@TypeChecked` (the GDK
  `sum()` is typed `Object`); it's usable in *contracts*, which is where the aggregation spec lives.
- **Refuting a *false* sum claim returns UNKNOWN.** Z3 can't construct a model satisfying the ∀
  base/step axioms (MBQI), so a wrong sum postcondition surfaces as an honest "could not decide,"
  never an unsound pass. Soundness rests on the axioms being theorems of the real sum; non-vacuousness
  on the positive proofs (the running-total loop, the unfold, the step law). This is the same
  weak-refutation caveat the other quantified features carry.

This is the loop-invariant aggregation pattern that was conspicuously missing — and the foundation for
the `below_zero` / `sum_product` HumanEval shapes.

---

## Phase 52 — Product aggregation and the `inject` fold  *(shipped)*

The multiplicative sibling of Phase 51's sum, and the surface that comes with it. Groovy has no GDK
`product()`, so the idiom for a fold is `xs.inject(1) { a, x -> a * x }` — which the encoder now
recognises as a **product** (and `inject(0) { a, x -> a + x }` as a **sum**, an alternative spelling).

- **`prod$ : (Array, Int, Int) → Int`** uninterpreted primitive, with base/step axioms mirroring
  `sum$`: base `∀ l,h. h <= l ⟹ prod == 1` (the empty product), step
  `∀ l,h. l < h ⟹ prod(arr,l,h) == prod(arr,l,h-1) * arr[h-1]`. A running product invariant
  `p == xs[0..<i].inject(1){…}` is preserved by `p = p * xs[i]` — the step at `i+1` instantiates to
  `prod(0,i+1) == prod(0,i) * xs[i]`, which closes by *congruence* (`p == prod(0,i)`), not NIA solving,
  so it's as robust as the sum loop.
- **`inject` recognition** matches a two-parameter closure `{ a, x -> a OP x }` whose operands are
  exactly the two parameters (either order), with `OP ∈ {*, +}`; the initial value lifts in as
  `init * prod$` / `init + sum$`. Any other fold shape (different operator, non-parameter operands)
  falls through to an honest skip. Gated to Int-element lists, like sum.

**Capstone — HumanEval 8 (`sum_product`).** Sum and product accumulate in one loop, each proven
against its aggregate (`s == xs[0..<i].sum()` ∧ `p == xs[0..<i].inject(1){…}`). groovy-verify doesn't
model tuple/array *returns*, so the showcase returns `s + p` to expose both in one int — the point is
the two aggregations composing in a single method. The `(int)` casts are the same GDK-`Object`-typing
accommodation as `below_zero` (an `Object + Object` in the postcondition won't type-check otherwise).

---

## Phase 54 — Sign-faithful `Integer.toString` / `parseInt`  *(shipped)*

Phase 47e mapped the conversions to Z3's raw `int.to.str` / `str.to.int`, whose SMT-LIB semantics are
correct only for *non-negative* integers — a **silent-unsoundness** hole (the engine *verified*
`Integer.toString(n).isEmpty()` for `n < 0`, false in Groovy). Like the Phase 50 div/mod fix, Phase 54
threads the sign explicitly rather than reasoning over Z3's convention, and makes the malformed-input
case *loud*.

- **`Integer.toString`** — `ite(n >= 0, intToString(n), "-" ++ intToString(-n))`. Java-faithful for
  all `n` (`toString(-7) == "-" + toString(7)`, and Z3 is correct for the non-negative magnitude).
- **`Integer.parseInt`** — `ite(prefixof("-", s), -stringToInt(substring(s, 1)), stringToInt(s))`,
  stripping a leading sign. The round-trip `parseInt(toString(n)) == n` now holds for **every** `n`
  (the Phase-47e test's `n >= 0` guard is no longer needed).
- **Loud obligation (`NumberFormatException`)** — a new `ParseSite` discharged at each
  `Integer.parseInt(s)` call: the sign-stripped magnitude must be a valid digit sequence
  (`stringToInt(magnitude) >= 0`). An arbitrary `String` argument can't prove it, so it **refutes**
  (`Reporter.formatNumberFormat`) — the engine no longer silently models `parseInt("abc")` as `-1`.
  `parseInt(Integer.toString(n))` discharges cleanly (`toString` produces valid numerals).
  *Residual:* integer overflow on a too-long numeral (Java throws, Z3's `str.to.int` is unbounded) is
  not yet checked — a `@CheckOverflow`-style follow-on.

---

## Phase 55 — Fibonacci generation: the `Fib.of(i)` helper (HumanEval 055 `fib`)  *(shipped)*

This **is** HumanEval task **055** (`fib`, the n-th Fibonacci number) with the functional spec the Verus
corpus omits — our `Fib.of` indexing matches HumanEval's (`Fib.of(10) == 55`, `Fib.of(8) == 21`). (It was
originally filed here under its motivation — task 039's `prime_fib`, below — but the standalone
`result == Fib.of(n)` proof is task 055 in its own right; the Phase-number/task-number match is a
coincidence.) The two-term-recurrence sibling of the Phase-51/52 `sum`/`prod` aggregations: a `Fib.of(i)`
spec helper (runtime-executable, like `Sets.boundedCount` / `Forall.range`) recognised and lowered to an
uninterpreted `fib$ : Int → Int` with mint-once defining axioms:

- base `fib(0) == 0`, `fib(1) == 1`
- step `∀k. k >= 2 ⟹ fib(k) == fib(k-1) + fib(k-2)` (triggered on `fib(k)`)

The headline is the **textbook iterative-equals-recursive proof**: an iterative Fibonacci provably
equals `Fib.of(n)`, the invariant carrying the recurrence `a == fib(i) ∧ b == fib(i+1)`, re-established
across `b = a + b` by the step axiom at `i+2` (a congruence). `Fib.of(5) == 5` unfolds through the
axioms; the step law verifies as a positive anchor (refuting a *false* fib claim is the usual
quantified-axiom weak direction — honest UNKNOWN). Inside an `@Invariant` the helper used to need the FQN
`verification.Fib.of(i)` (the loop-invariant closure was compiled without the file's imports in scope — the
same wart `Forall` carried); **GROOVY-12072 fixed that**, so bare `Fib.of(i)` now resolves.

**The outer `prime_fib` is a deliberate non-target.** Returning the n-th number that is both prime
*and* Fibonacci is an *unbounded search* (`while true`) with no termination measure — and whether
there are infinitely many Fibonacci primes is an **open problem in number theory**, so no `@Decreases`
can exist for symbolic `n` (even Verus' HumanEval port leaves task 039 a `TODO`). The Fibonacci
generation it rests on verifies; the search does not, and saying so cleanly is the honest boundary.

---

## Phase 63 — Tribonacci generation: the `Trib.of(i)` helper (HumanEval 063 `fibfib`)  *(shipped)*

The three-term sibling of Phase 55, and HumanEval task **063** (`fibfib`): the recurrence
`fibfib(n) = fibfib(n-1) + fibfib(n-2) + fibfib(n-3)` with base `0, 0, 1`. It shows the recurrence
machinery extends mechanically — a `Trib.of(i)` helper (runtime-executable; `Trib.of(5) == 4`,
`Trib.of(8) == 24`, matching HumanEval) lowered to an uninterpreted `trib$ : Int → Int` with mint-once
axioms, mirroring `fib$`:

- base `trib(0) == 0`, `trib(1) == 0`, `trib(2) == 1`
- step `∀k. k >= 3 ⟹ trib(k) == trib(k-1) + trib(k-2) + trib(k-3)` (triggered on `trib(k)`)

The iterative-equals-recursive proof (`result == Trib.of(n)`) carries a **three-wide** recurrence window
in its invariant — `a == trib(i) ∧ b == trib(i+1) ∧ c == trib(i+2)` — re-established across the body's
`c = a + b + c` by the step axiom e-matching `trib(i+3) == trib(i+2) + trib(i+1) + trib(i)` (a congruence,
not a fresh nonlinearity). New backend primitive `trib(k)` + encoder `tribOf` + the `verification.Trib`
helper; recognised from the `Trib.of(i)` shape exactly as `Fib.of(i)`. Same honest boundary as Phase 55:
refuting a *false* `trib` claim is the quantified-axiom weak direction (UNKNOWN, not a counterexample).

---

## Phase 57 — Logical implication: `==>` and `.implies()`  *(shipped)*

The backend already had an `implies` primitive (used internally for quantifier ranges); this exposes
it at the surface. Both Groovy spellings of logical implication are now recognised in contracts:

- **`a ==> b`** — Groovy 5's implication operator, which the parser produces as a `BinaryExpression`
  with the `IMPLIES` (`==>`) token; `translateBinary` lowers it (by operator text) to `implies(L, R)`.
- **`a.implies(b)`** — the DGM `Boolean.implies` method (`!a || b`); `translateMethodCall` lowers it
  the same way.

Both are `!a ∨ b`. This is *ergonomics, not capability* — `a ==> b` was always expressible as
`!a || b` / `a ? b : true` — but it reads far better for the shapes that recur here: the array-element
**frame** `every { it != j ==> a[it] == old.a[it] }` (every index other than `j` is unchanged), modus
ponens, and the DFS "closed-except-on-stack" invariant `(it in visited) ==> (it in onStack ∨ next[it]
in visited)`. *Residual:* like the DGM method, the operator is **eager**, and the implicit-obligation
short-circuit scan doesn't yet treat a *body-level* `a ==> b` as guarding `b`'s accesses by `a` (use
an `if` to guard an access in a body); in contract position — the overwhelming use — the value
translation is all that's needed.

---

## Phase 58 — Spaceship operator `<=>`  *(shipped)*

Groovy's `a <=> b` (compareTo) is a `BinaryExpression` with the `COMPARE_TO` token. For Int operands it
lowers to the three-way sign `ite(a < b, -1, ite(a == b, 0, 1))` — exactly `Integer.compareTo`'s
`-1/0/1` — so a three-way comparator's contract verifies (`(result < 0) == (a < b) ∧ …`, and `a < b ⟹
result == -1`). Int-oriented like the other comparison operators; a `String <=>` (lexicographic,
arbitrary-valued) would need Z3's string ordering, so it skips honestly rather than mis-applying int
comparison. **Modest** — the three-way result is rarely the *subject* of a spec (direct `<`/`==`
comparisons read clearer, and don't need it), but it rounds out comparison-operator coverage and lets
a `compareTo`/`compare` method be verified directly.

---

## Phase 59 — Classic `for` loops  *(shipped)*

The verifiable-loop story was `while`-only; the most common Groovy loop is the C-style
`for (init; cond; update)`. groovy-contracts already injects `@Invariant`/`@Decreases` on a
`ForStatement` (its `LoopContractSupport` visits `for`/`while`/`do-while` uniformly via
`LoopingStatement.getLoopBlock()`), so this is purely a verifier-side desugar — no upstream change.

In `ContractExpansionTransform.buildLoopSpec`, a `ForStatement` whose collection is the classic
`ClosureListExpression` `[init, cond, update]` is lowered to while-shape: **`cond`** becomes the guard,
**`init`** is captured into a new `LoopSpec.init` and threaded into the loop prefix by `findLoopSite`,
and **`update`** is normalised to a plain assignment (`i++`/`++i` → `i = i + 1`, `i += k` → `i = i + (k)`,
a bare `i = …` kept) and *appended to the loop body*. Every downstream path — the four loop VCs
(`LoopEncoder`) and the value-flow loop-fused obligation pass — then sees an ordinary while-shaped loop,
so a `for`-loop array-bounds obligation discharges from the invariant exactly as a `while` does. A
`for`-in loop (no index to bind the invariant to) and an unsupported update shape return null → loud skip.

---

## Phase 60 — `xs.max()` / `xs.min()` as the witnessed extremum  *(shipped)*

`a.max()` is what a Groovy developer writes; the explicit witnessed-extremum spell (a `.every` bound
plus a `.any` witness, as in the HumanEval `maxElement` port) is what the proof needs. This recognises
`xs.max()` / `xs.min()` over an Int list/array and lowers each to a fresh constant `r` (`Encoder.maxMinOf`,
mint-once per receiver) carrying the two defining facts over the modelled contents: a **bound**
(`∀i. lo<=i<hi ⟹ a[i] <= r`, or `>=` for min, triggered on `a[i]`) and an **achieved** witness
(`∃j. lo<=j<hi ∧ a[j] == r`). The achieved-fact is guarded by non-emptiness (`lo < hi ⟹ …`) so an empty
range — Groovy's `[].max()` is undefined — can't make the context vacuously unsatisfiable. `result == a.max()`
then proves against the same max-finding loop the explicit spec did (Z3 closes `result == r` by
antisymmetry: each bounds the other's witness). Non-Int element domains skip.

---

## Phase 61 — BigDecimal division as exact reals  *(shipped)*

The headline Groovy arithmetic surprise — `/` on integers is **`BigDecimal` division** (`5 / 2 == 2.5`,
not `2`) — was previously skipped loudly. It is now modelled with Z3's exact **Real** sort, retiring that
caveat. The backend gains four Real primitives (`realLit`/`realVar`/`realDiv`/`intToReal`); the existing
`plus`/`minus`/`times`/`eq`/`lt`/… are sort-polymorphic (Z3 arithmetic accepts Real), so no other backend
op changed. In `Encoder.translateBinary`, a binary fires the Real path when an operand is decimal (a
`BigDecimal`/`Double`/`Float` literal or a decimal-typed name) or the operator is `/` (always BigDecimal
in Groovy); `asReal` translates the subtree, coercing Int operands via int→real, and a comparison with a
decimal operand emits a Real comparison. Decimal-typed names (params, fields, the implicit `result`,
typed locals) come from `VerifyChecker.collectDecimalNames`, threaded into the encoder as `decimalNames`.

**Soundness containment.** A decimal value can only reach an Int slot via Groovy's implicit
BigDecimal→int narrowing — and Groovy's own static type checker rejects the body/local forms
(`int x = a / b` is a compile error), leaving only the `int f() { a / b }` return narrowing, which the
result-binding guard skips loudly (its old behaviour) rather than binding a Real where Int is expected.
A full crash audit of the suite confirms no Z3 sort-mismatch. **Out of fragment:** true IEEE-754
`double`/`float` (modelled as exact reals, not bit-exact), and decimal `%`.

---

## Phase 62 — Bounded property-based refutation on UNKNOWN  *(shipped)*

The weak direction is *refutation* of a quantified/recurrence contract: Z3's MBQI can't build a model
violating the aggregation/`Fib` axioms, so a false `@Ensures({ result == Fib.of(n) })` surfaces as an
honest UNKNOWN (timeout), not a counterexample. Because the contracts are executable Groovy, the natural
fallback is to *run the spec the solver couldn't prove*. `ContractTester` (a self-contained concrete
interpreter, kept separate from `PureEvaluator` so the Phase-8a folding path is untouched) is invoked
from `checkPath` only on a postcondition UNKNOWN: it searches a small symmetric integer grid, checks the
`@Requires`, executes the body to a `result`, and evaluates the `@Ensures`, reporting the first failing
input as a runnable `fails on:` repro via `Reporter.formatPostconditionRefutedByTesting`.

It is a **witness, not a proof of falsity** — a bug needing inputs outside the grid escapes, so the
diagnostic says "counterexample found by bounded testing". The evaluable fragment mirrors `PureEvaluator`
(Int arithmetic, comparisons, boolean connectives, `?:`, `if`/`return`, single-assignment locals,
same-class contract-free calls) over `Long`, plus the `Fib.of` helper. Outside it — notably array /
quantified contracts (`result == xs.sum()`), the Long-only limit — the search bails to the honest "could
not decide", never fabricating a false refutation. Extending the concrete domain to arrays/lists (so
quantified UNKNOWNs also get repros) is the natural follow-on.

---

## Phase 63 — `for (x in xs)` loops  *(shipped)*

The for-in (for-each) loop is the most idiomatic Groovy iteration; Phase 59 left it skipping. Both
spellings — `for (x in xs)` and the Java-style `for (T x : xs)` — parse to the same `ForStatement`
shape and are handled identically. It now desugars to an **indexed** while over the collection — the one wrinkle being that for-in exposes no
index for the user to write an invariant against. The resolution (the brief asked for it explicitly):
**synthesize a hidden index, but retain the loop variable's name for reporting.**

In `ContractExpansionTransform.buildLoopSpec`, a `ForStatement` whose `collectionExpression` is a plain
`VariableExpression` `xs` (a named list/array — a literal or method-call collection skips) is lowered:
a synthetic index `__gvForInIdx` initialised in the prefix (`int idx = 0`), guard `idx < xs.size()`,
and an update `idx = idx + 1` appended to the body. The loop **variable keeps its source name**, bound
to `xs[idx]` as the first body statement (`x = xs[idx]`), so the body, contracts, and counterexamples
all read in terms of `x`, never the index. Because the index isn't user-nameable, two clauses are
**auto-injected**: an index-bounds invariant `0 <= idx && idx <= xs.size()` (added after the user's, so
preservation of a user invariant has the bound in scope, and the synthetic `xs[idx]` read is provably
in-bounds) and a `xs.size() - idx` variant (so for-in loops are proved terminating for free, unless the
user supplied a `@Decreases`).

The synthetic index is suppressed everywhere user-facing: filtered from the displayed counterexample
(`VerifyChecker.shown`, alongside the SSA/array-element keys) and from the invariant text in a loop
diagnostic (`invText`). So a broken `@Invariant({ s == 0 })` over `for (x in xs) { s = s + x }` reports
`invariant: (s == 0)` / `counterexample: s = 0, xs.size() = 1` / `fails on: sumIn([-1])` — the loop
variable and a runnable repro, no `__gvForInIdx` in sight.

**Known limits.** Int-element collections are the modelled case; a non-Int element doesn't translate
and skips. *(Phase 64 lifts the earlier "preservation can't assume `@Requires`" limit for loop-stable
conjuncts; Phase 65 lifts the "an invariant can't reference the loop variable" limit — such clauses are
now verified as per-element checks.)*

---

## Phase 64 — Loop-stable `@Requires` in preservation/progress  *(shipped)*

Preservation and progress deliberately omit `@Requires`: a precondition over mutable state goes stale
once the loop runs (`@Requires({ i < n })` is false after the body increments `i`). But a conjunct that
references only state the loop body *doesn't* modify stays true on every iteration and is sound to
assume — which is exactly what for-in element reasoning needs (`xs.every { it >= 0 }` instantiated at
the current element, where the loop only *reads* `xs`).

The discrimination is a **sound write-set over-approximation** of the loop's prefix + body
(`loopWriteSet`): assignment / declaration / `++` / compound-assign targets, `a[i] =` array names,
`this.field` writes, and the receivers of a fixed set of known collection mutators (`add`/`remove`/
`put`/…). Anything whose effects can't be bounded — an unrecognised method call, a shift operator that
might be a `<<` append, an unusual statement — makes `loopWriteSet` return null, and **all** conjuncts
are dropped (the prior, always-sound behaviour). A `@Requires` is split into top-level `&&` conjuncts;
a conjunct is assumed in preservation/progress iff its free names (over-collected via a visitor —
closure params like `it` included, which only makes the test stricter) are disjoint from the write-set.

Over-approximation is the safe direction: surplus write-set names, or surplus free names, only cause
*more* conjuncts to be conservatively dropped — never a stale fact assumed. The soundness anchor: a loop
that decrements `cap` puts `cap` in the write-set, so `@Requires({ cap >= 1000 })` is dropped and
`@Invariant({ cap >= 0 })` correctly refutes at `cap = 0` (assuming the stale bound would wrongly verify
it). The mechanism is loop-shape-agnostic — while, classic-for, and for-in all benefit; establishment
and use already saw the full `@Requires`.

---

## Phase 65 — For-in invariants over the loop variable (per-element checks)  *(shipped)*

groovy-contracts checks a loop invariant at **body-entry** — inside the loop, with the loop variable
bound to the current element (`@Invariant({ x < 5 })` over `for (x in xs)` fires at runtime when `x`
reaches an element `>= 5`). The Phase 63 desugar checked the invariant at the **loop head** instead,
where the synthetic `x = xs[idx]` binding hasn't run, so `x` was havoced — and the spurious counterexample
was always the *empty* collection (`xs.size() = 0`), the one case the runtime never reaches. A true
per-element invariant like `x >= 0` was wrongly refuted; a false one failed for the wrong reason.

The fix splits a for-in's invariants (after breaking each into top-level conjuncts) into the clauses
that reference the loop variable and those that don't. The **x-free** clauses (`s >= 0`, the auto index
bound) stay inductive loop-head invariants — establishment + preservation as before. The **per-element**
clauses are discharged by one extra VC (`checkForInElement`): at an arbitrary valid iteration — x-free
invariants ∧ guard (so `0 <= idx < size`) ∧ loop-stable preconditions ∧ `x = xs[idx]` — each clause must
hold. This matches the runtime exactly and is naturally **vacuous on an empty collection** (the guard
makes the antecedent unsatisfiable, so no spurious failure). Combined with Phase 64, `@Requires({ xs.every
{ it >= 0 } })` now discharges `@Invariant({ x >= 0 })` by instantiating the precondition at the element;
the refutation counterexample names the offending element and a *non-empty* collection.

---

## Phase 66 — Repeated `@Requires` / `@Ensures` / `@Modifies`  *(shipped)*

`@Requires`, `@Ensures`, and `@Modifies` are all `@Repeatable`, and groovy-contracts enforces *each* at
runtime. The capture in `ContractExpansionTransform` kept only the *last* (a plain overwrite), silently
dropping the rest — unsound in several directions, not merely incomplete:

- a dropped `@Ensures` let a method violate a postcondition it declared and still "verify" (the body only
  had to satisfy the last one);
- a dropped `@Requires` under-constrained a *caller* (the call-site precondition check required less than
  the callee actually demanded);
- a dropped `@Modifies` location both raised a spurious frame violation (a write to the dropped-but-declared
  location looked undeclared) and, at a call site, was *not* havoced — so a caller wrongly assumed it
  unchanged across the call.

The fix collects *all* closure texts of each kind — whether the parser left a sequence of annotations or
collapsed them into a `@RequiresConditions`/`@EnsuresConditions`/`@ModifiesConditions` repeatable
container. The two **predicate** kinds (`@Requires`/`@Ensures`) are ANDed (each parenthesised) — so
`@Requires({ a >= 0 }) @Requires({ b >= 0 })` behaves exactly like `@Requires({ a >= 0 && b >= 0 })`, and
a body meeting only the last of two `@Ensures` is correctly refuted. `@Modifies` is a **frame** (a *union*
of locations, not a predicate), so its texts are merged into one `[ … ]` list — the consumer's
`addModifiedLocation` recursively flattens, so an already-list frame nests harmlessly. A lone annotation of
any kind passes through unchanged. The earlier "combine your premises into one `@Requires`" workaround (it
predated repeatable capture) is no longer needed — the modus-ponens example now reads as two separate
`@Requires`. (`@Decreases` is genuinely single — one termination measure — so it stays last-wins.)

---

## Phase 67 — Decimal negation, and a clean boundary for unmodelled decimal ops  *(shipped)*

Phase 61 modelled BigDecimal `+`/`-`/`*`/`/` and comparisons in Z3's Real sort, but two everyday cases
slipped through the binary-operator path: **unary minus** (`-a`, a `UnaryMinusExpression`) and a
**negative decimal literal** (`-2.5`). Both fell to the integer path — `-a` negated `a`'s meaningless int
shadow (refuting a true postcondition), and `-2.5` left the decimal constant unmodelled (a loud "outside
fragment" skip). Now `isDecimalExpr`/`asReal` handle `UnaryMinusExpression`, `translate` routes a decimal
negation to the Real path, and a decimal-valued *return* is bound through `asReal` (so a bare decimal
literal/variable result is Real, not an int shadow). So `BigDecimal f(BigDecimal a) { -a }` proving
`result == -a`, and `-2.5` as a return, now verify. Scalar decimal arithmetic is complete: `+ - * /`,
unary minus, negative literals, and comparisons.

A second fix closes a confusing edge: a decimal operand on an operator the Real path *doesn't* model —
notably `%` (BigDecimal remainder, which Z3's real theory has no clean primitive for) — used to fall
through to the integer path and translate the decimals as int shadows (a spurious divide-by-zero /
wrong remainder). It now **skips loudly** instead.

A third fix is a genuine **soundness** repair found while exercising financial conservation proofs. A
decimal field/local *assignment* (`checkPath`'s SSA step) minted an **`intVar`** fresh handle while the
RHS was translated to a Real — a sort-mismatched binding that silently mis-modelled some writes. The
symptom: a transfer that skims a cent (`bob = bob + amt - 0.01`) could "verify" the conservation
`alice + bob == old.alice + old.bob` it actually breaks. Now a decimal-named target gets a `realVar`
fresh handle and an `asReal` RHS (mirroring the return-binding), so the SSA equality is sort-matched and
the skim is correctly refuted.

**Still out of fragment (reported):** `BigDecimal.abs()`. (*Extremum* over a decimal-element collection —
`List<BigDecimal>.max()` / `.min()` — was foreshadowed here as a small follow-on of `.sum()` (Phase 70);
it **shipped in Phase 76** as the Real witnessed extremum.) The divide-by-zero obligation for a *decimal*
divisor is also still checked on the int shadow
(sound — it refutes rather than wrongly verifying — but imprecise for a provably non-zero decimal divisor;
a literal/int divisor like `(a + b) / 2` is unaffected).

---

## Phase 68 — Financial proofs: conservation & no-cents-lost  *(application; partial)*

A real-world driver: large financial institutions model currency and prices with Groovy + BigDecimal,
and want proofs like *"no money is lost in an account transfer"* and *"no fractional cents are syphoned
in an interest/trade calculation"*. This phase records where the framework sits and what Z3 Real can and
can't do for money.

**Z3 Real is an excellent vehicle for conservation, with one caveat.** BigDecimal `+`/`-`/`*` are *exact*
(never lose precision), and Z3's Real sort models exact rationals — so they coincide exactly, and a
conservation invariant (`alice + bob == old.alice + old.bob`) is a faithful, sound proof. Two- and
N-fixed-account transfers verify today (scalar BigDecimal fields + `old`), and the skim that breaks
conservation is refuted (after the Phase 67 assignment-soundness fix). The caveat: BigDecimal `/` either
terminates exactly or *throws/rounds*, whereas Z3 Real gives the exact rational (1/3) — so a proof using
`/` can assert something true over rationals but false over rounded BigDecimal. **Rounding itself
(`setScale`, `RoundingMode`) is not modelled** — and that is exactly what "no fractional cents" needs.

**The soundest money model is integer minor units (cents), and the framework is strongest there.** Cast
the "no cents syphoned" proof in integer cents: the credited (floored) amount plus the retained remainder
equals the exact interest, and the remainder is bounded `[0, den)` — both verify today via NIA + exact
`intdiv`/`%` (Phase 48/50), and a calc claiming it credits the *exact* interest is refuted whenever a
remainder exists. This is the round-trip identity (`result*den + p*num % den == p*num`) — salami-slicing
made impossible.

**Dynamic-collection conservation — shipped for both Int (Phase 69) and decimal (Phase 70).** The
keystone for "transfer preserves the total over N accounts" is a **sum-under-store law**: it landed for
`int[]`/`List<Integer>` in Phase 69 (integer-cents) and for `List<BigDecimal>` in Phase 70 (Real-element
arrays + a Real-codomain `sumReal`). So both models prove dynamic N-account conservation. Out of
fragment when this phase shipped — both since closed: decimal `.max()`/`.min()` over a collection
(**shipped in Phase 76**, the Real extremum), and `BigDecimal[]` (array, vs `List<BigDecimal>`) element-type
collection (generalised to array component types in **Phase 77**). (Integer minor units remain the
recommended model regardless.)

---

## Phase 69 — Sum-under-store law: N-account conservation  *(shipped)*

The additive analogue of the Phase 12 `count`-under-store law, and the keystone for conservation over a
*dynamic* array of money. At each `a[i] = v` store, `checkPath` now asserts the ground instance

```
0 <= i < N  ⟹  sum(store(a,i,v), 0, N) == sum(a, 0, N) - a[i] + v        (and == sum(a,0,N) otherwise)
```

— a true theorem of `sum`, gated (like the count law) to arrays whose `.sum()` a contract actually
references (`sumArrayNames` over the pre- and postcondition), so ordinary stores pay nothing. Two
compensating stores (`bal[i] -= amt; bal[j] += amt`) then leave `bal.sum()` invariant, so an N-account
transfer **proves the total is conserved** — stated against the entry total (`bal.sum() == 100`) or, via
the extended `listAggHandles`, against `old.bal.sum()` (the natural "no money is lost" form). The prefix
base/step axioms (Phase 51) aren't needed here — the ground store law carries it — so the proof is robust.

**Verify is clean; refutation is the weak direction.** Correct conservation discharges by ground reasoning
(UNSAT found reliably). A *violation* (a skim, `bal[j] += amt - 1`) makes Z3 search for a model satisfying
the quantified sum axioms and times out → it fails the build as a loud "could not decide", not a witnessed
counterexample (and the integer-only PBT fallback can't evaluate the array). Honest — never a silent pass —
but a counterexample-producing refutation would need either a model-construction improvement or a
collection-aware PBT pass. The *scalar* BigDecimal syphon (Phase 68) still refutes cleanly, since it uses
no sum primitive.

Also in this slice: a **display fix** — a decimal name's Int model value is a meaningless shadow (its real
value lives in the Real sort the Int model-walk doesn't read) and a decimal scalar has no size, so both are
suppressed from the counterexample rather than printed as `price = 0, price.size() = 0`.

---

## Phase 70 — `List<BigDecimal>.sum()`: Real-element arrays  *(shipped)*

The decimal half of the dynamic-collection slice. A `List<BigDecimal>`'s *contents* are now modelled as an
`Array Int Real` and `.sum()` as a Real-codomain aggregation — completing the financial story so that
conservation over a *dynamic* list of money (not just fixed fields) is provable.

Most of the array machinery was already sort-general — `arraySortsFor` routes by `sortFor(elementType)`,
and `select`/`store` are sort-polymorphic — so the new pieces are surgical: a backend `realSort` /
`sumReal` (an `(Array Int Real, Int, Int) -> Real` func decl) / `isReal` test; `sortFor(BigDecimal/Double/
Float) → realSort` (so a decimal list's `arrayFor` mints `arrayVarOfSort(name, Int, Real)`); a decimal
branch in the `.sum()` handler lowering to **`sumRealOf`** (Real base/step axioms, the analogue of
`sumOf`); `translateInSort(e, realSort) → asReal(e)` for the store value; and the Phase 69 sum-under-store
law generalised to pick `sumReal` for Real elements. One `asReal` fix: its fallback no longer wraps an
*already-Real* handle (a decimal element read `xs[i]`) in `int→real` — it queries `isReal` first. The
`.sum()` element-type lookup also strips the `old$` prefix so `old.xs.sum()` finds the live element type.

So `xs.sum() == xs[0] + xs[1]` proves for a 2-element decimal list (base/step axioms unfold), and a
`List<BigDecimal>` transfer proves `bal.sum() == old.bal.sum()` — "no money lost" over dynamic accounts.
Verify is clean; a skim is the weak refutation direction (sum-axiom model construction → timeout), so it
fails the build as a loud "could not decide", exactly as the Int case (Phase 69). Out of fragment when this phase
shipped (both since closed): decimal `.max()`/`.min()` (a Real extremum primitive over the same Real array)
— **shipped in Phase 76** — and `BigDecimal[]` array element-type collection — **Phase 77** generalised
`collectListElementTypes` to array component types.

---

## Phase 71 — Soundness hardening (pre-public sweep)  *(shipped)*

An adversarial sweep of "should-refute" cases across sort boundaries and recent features — the kind of
silent false-verify or crash that would embarrass a public release — turned up two issues, both fixed:

- **Boolean *field* write crashed.** A `boolean` field `b = !b` minted an `intVar` SSA fresh handle (the
  `collectBooleanLocals` scan only covered body *declarations*, not params/fields/`result`), so the
  binding hit `eq(intFresh, boolRhs)` / `not(intExpr)` and threw a Z3 `GroovyCastException` — the boolean
  sibling of the Phase 67 decimal-assignment bug. `collectBooleanLocals` now also collects boolean params,
  declaring-class fields, and the implicit `result`, so every boolean name gets a `boolVar`. (String, enum,
  set, map, and decimal field writes were already sound — confirmed by the same sweep.)

- **A contradictory `@Requires` passed vacuously.** Under a precondition that can never hold, every
  `@Ensures` verifies trivially — the silent *vacuous* pass the project warns about most. Now
  `checkPreconditionSatisfiable` asserts the encoded precondition (plus class invariants) and, if Z3
  returns a definite UNSAT, reports a loud **"Vacuous precondition"**. Conservative and sound: it fires
  only when the precondition fully translates and is provably unsatisfiable (UNKNOWN/SAT stay silent), and
  is best-effort so it can never break the build by itself. Asserting a *subset* of conjuncts being UNSAT
  implies the whole is UNSAT, so partial translation can't cause a false positive.

**The broader systematic pass.** After those two fixes, ~45 further adversarial cases were run across the
full matrix — every scalar/collection sort × {param, field, local, result} × {assignment, `old`-snapshot,
mutation, size/count/membership law, loop (while/for/for-in), induction, NIA, div/mod, overflow, string
contents, `@Modifies` frame, `<=>`/`==>`, nested `Map<K,Set<V>>`, quantifier, vacuity} — each constructed
to *demand a refutation, skip, or vacuity flag*. **No new soundness bug surfaced**: every should-refute
case refuted, vacuity flagged across String/size/decimal/null, recursion-without-`@Decreases` skipped
loudly, and a bounded `every` over array contents refuted (the array-quantifier direction, unlike the
sum-axiom direction, *is* refutable). Two cases verified, both expected-and-sound: `old` of a *parameter*
soundly tracks the entry value (a reassigning body's false unchanged-claim refutes; arithmetic on it is
blocked by Groovy's own type checker), and the **heap-aliasing** case (two object params, field writes
through both) verifies a claim that is false only under aliasing — the documented non-goal. The curated
strongest anchors are now permanent tests, closing the coverage blind spots that had let the boolean-field
and decimal-assignment bugs exist. *(One crash was found but was upstream: groovy-contracts'
`DynamicSetterInjectionVisitor` NPE'd on an `@Invariant` on a static nested class, at instruction-selection,
independent of groovy-verify — fixed in
[GROOVY-12066](https://issues.apache.org/jira/browse/GROOVY-12066); a nested-static regression test now
guards it.)*

---

## Phase 72 — `double`/`float` are IEEE-754, not exact (skip)  *(shipped)*

A soundness fix found while assessing whether the floating-point non-goal had moved. The BigDecimal work
(Phase 61) routed `Double`/`Float`/`double`/`float` to the exact **Real** sort alongside `BigDecimal` — but
only `BigDecimal`'s `+`/`-`/`*` are *exact*; `double`/`float` are IEEE-754, so an exact-Real model is
**unsound**: `(a + b) - b == a` and `0.1d + 0.2d == 0.3d` hold in Real but are false at runtime, and the
verifier was silently "proving" them. (Modelling a `double` as exact *Int*, the pre-Phase-61 default, was
unsound the same way.) The fix narrows the decimal/Real path to `BigDecimal` only (`isDecimalType`,
`isDecimalElementType`, the decimal-literal checks) and adds a `doubleNames` skip-set: any reference to a
`double`/`float` name translates to null, so a contract over it **skips loudly** — the correct realisation
of the floating-point non-goal (exact reasoning over IEEE-754 needs Z3's FP theory, which stays out of
scope). `BigDecimal` is unaffected and remains a faithful exact-Real model.

---

## Phase 73 — IEEE-754 floating point: a straight-line `double`/`float` fragment  *(shipped)*

Phase 72 made `double`/`float` *skip* (exact Int/Real is unsound for them). But Z3 has a **floating-point
theory** that models IEEE-754 *bit-exactly* — round-nearest-even, NaN, ±∞, signed zero, subnormals — so it
is *faithful* to the JVM runtime, the opposite of the exact-Real over-reach. This phase supersedes the
skip with a real sub-fragment, built as a parallel **FP path** mirroring the Real one:

- backend FP primitives — `Float64`/`Float32` sorts, RNE-rounded `fpAdd`/`fpSub`/`fpMul`/`fpDiv`/`fpNeg`,
  IEEE comparisons (`fpEq` — **NaN ≠ NaN** — `fpLt`/`fpLeq`/…), `fpIsNaN`/`fpIsInfinite`, literals from a
  `double`, and an `isFp` sort test;
- the Phase-72 `doubleNames` skip-set becomes an `fpNames` map (name → precision); a `double`/`float`
  name resolves to an `fpVar`, a `Double`/`Float` literal to an `fpLit`, and `asFp`/`isFpValued` carry FP
  arithmetic + comparisons through `translateBinary`, the result-binding, and `Double.isNaN`/`isFinite`/
  `isInfinite`;
- **straight-line only** — `asFp` returns null (→ loud skip) for anything not purely FP (an int operand, a
  transcendental, a loop body), so the unsound/expensive cases stay out.

The flagship is the **same expression proven in two number models**: `0.1 + 0.2 == 0.3` for `BigDecimal`
(exact decimal) *and* `0.1d + 0.2d != 0.3d` for `double` (IEEE-754) — both verify. Exact FP facts prove
(`0.5d * 2.0d == 1.0d`); the highest-value class, **no-NaN / finiteness**, proves (`Double.isFinite(x) ⟹
!Double.isNaN(x + x)`); and it's sound — a false claim refutes (`(a + b) - b == a` is refuted, FP
non-associativity proven; `x == x` is refuted because a NaN isn't equal to itself; the no-NaN claim
refutes without the finite guard). `Math.sqrt` and `Math.abs` are modelled too, on Z3's `fp.sqrt` (RNE)
and `fp.abs`: `x >= 0 ⟹ Math.sqrt(x) >= 0 ∧ !isNaN`, `Math.abs` non-negative for non-NaN — and soundly,
`Math.sqrt(x)` without a non-negative guard *can* be NaN (refutes), `Math.abs(x) < 0` refutes. (`sqrt`
only models a double-precision argument, since Java widens a `float` argument to `double`.) Z3 bit-blasts
FP, so it's the expensive end and subject to the per-VC timeout, but small straight-line snippets are
fast. **Still out of fragment:** FP *loops* (accumulated rounding error), the other transcendentals
(`sin`/`cos`/`exp`/`log`/… — no Z3 FP primitive), and tight relative-error bounds.

**Follow-on — FP division + HumanEval 045 (`triangle_area`).** Completing FP `/`: `isDecimalExpr` no longer
claims a `/` whose operands are `double`/`float` (Groovy's int/BigDecimal `/` is exact-Real division, but
FP `/` must reach the FP branch as `fp.div`), and an FP-valued divide carries **no** divisor obligation
(IEEE `x/0.0` is `±Inf`/NaN, not a thrown `ArithmeticException` — `dischargeObligationUnder` skips it
silently). With that, `triangle_area(a,h) = a*h/2` ports: the doctest `area(5,3) == 7.5` is exact; positive
sides prove `result >= 0` (real FP sign reasoning — `a*h/2` is positive-or-`+0`, never NaN); but **not**
`result > 0` (tiny positive sides underflow `a*h` to `+0.0` — a true IEEE fact, false in exact arithmetic);
and the formula `result == a*h/2` needs a finiteness `@Requires` (else a NaN input makes even `x == x` false).

---

## Phase 74 — `Range.containsWithinBounds`: bounds-only interval membership, all range forms  *(shipped)*

The first slice of range support (Tier 1 of the range-fragment assessment). Groovy's
`Range.containsWithinBounds(v)` is a *bounds-only* membership test — it ignores the step, which is exactly
what distinguishes it from `contains` (`new NumberRange(1,5,2).contains(4)` is **false**, but
`.containsWithinBounds(4)` is **true**). That makes it lowerable with **no enumeration**.

Covers **every Groovy range form**: closed `a..b`, left-open `a<..b`, right-open `a..<b`, and open
`a<..<b` (the Groovy 4+ `<..`/`..<` operators). Decoded from `NumberRange.containsWithinBounds` (which sorts
its endpoints and is `reverse`-aware), each endpoint keeps *its own* inclusivity, and the two order
orientations are OR'd, giving an order-agnostic predicate exact for forward, reverse **and** equal bounds:
`(a ≤/< v ∧ v ≤/< b) ∨ (b ≤/< v ∧ v ≤/< a)` — `≤` where the endpoint is inclusive, `<` where exclusive.
(So e.g. the reverse-open `4<..2` correctly works out to `{2,3}`.)

`translateMethodCall` recognises a range literal (`RangeExpression`, reading `isExclusiveLeft`/
`isExclusiveRight`) and a `new NumberRange(a,b,step)` / `new IntRange(a,b)` constructor
(`ConstructorCallExpression`; the boolean-first `IntRange(inclusive,…)` overload is rejected). The
comparisons are built as *synthetic* `<`/`<=` `BinaryExpression`s and re-`translate`d, so they route through
the existing per-sort dispatch for free — Int bounds compare in Int, `BigDecimal` bounds in the exact
**Real** sort (so `(1.5<..<4.5).containsWithinBounds(2)` proves). Exact *and* symbolic, and the exclusivity
shows up: a param in `(1,4]` is provably within `(1<..4)`, while a non-strict `x >= 1` is **not** enough
(`x == 1` is excluded by the open left → refutes).

Pure bounds for every range kind — this is the documented `Range` contract: `containsWithinBounds` is
"between the from and to values", explicitly distinct from `contains` (the interface Javadoc gives
`containsWithinBounds(2) == true` while `contains(2) == false`). **Upstream bug found and fixed:**
`IntRange.containsWithinBounds` used to just `return contains(o)` (integer membership), so
`(2..4).containsWithinBounds(2.5)` returned `false` at runtime while the decimal-typed `(2.0..4.0)`
`NumberRange` returned `true` for the same interval — a type-dependent inconsistency that violated the
interface contract, surfaced while building this slice and fixed in
[GROOVY-12067](https://issues.apache.org/jira/browse/GROOVY-12067) (`IntRange` is now pure-bounds too). The
verifier models pure bounds for all range kinds, matching both the fixed runtime and the contract, so any
numeric `v` is exact regardless of endpoint type. A **character/`String`** range (no modelled
lexicographic order) skips; a numeric pre-guard plus a term-construction `try/catch` (terms aren't asserted
until `checkPath`, so a throw is a clean skip, not a corrupt session) ensure a non-arithmetic comparison
never crashes. **Still out of fragment** (Tier 2): `contains`/`==`/`.step`/`.toList` over a
range — these need step-aware *enumeration* of a constant range to a list literal (then they ride the
existing list machinery), plus a list-to-list `==` fold; non-constant or character ranges stay out.

---

## Phase 75 — infinite-stream `every` / `any`: the property you can't test  *(shipped)*

The sharpest motivation for a verifier the project has: a property of an **infinite stream** cannot be
tested — a true `every` over an unbounded `Stream.iterate(seed, f)` *never returns* (a passing test would be
a hang). The only way to know every element is even is to **prove** it. And `iterate` is a loop in disguise
(`s(0)=seed, s(k+1)=f(s(k))`), so `.every{P}` over it is a loop invariant — the proof is induction, the same
base + preservation the loop VCs already do.

**Dual runtime+verify forces a bound.** These contracts stay dual — the same `@Ensures` is compiled by
groovy-contracts into an *eager* runtime assert — so a terminal `every`/`any` over an unbounded source would
loop forever at runtime (a true `every` never short-circuits). So a `.limit(n)`/`.take(n)` is **required**:
it is what lets the contract degrade to a *terminating* runtime spot-check. An unbounded terminal `every`
(no bound) is **not** blessed as verified — it skips loudly (the seed of a later termination check),
nudging the developer to add a bound. The bound's *value* is the runtime's spot-check depth; the verifier
reaches far past it.

`translateMethodCall` recognises `iterate(seed, f).limit(n).every|any{ P }` — the `iterate` holder is not
pinned (works for `Stream`/`IntStream`/a GDK iterator); the shape `iterate(seed, oneArgClosure)` is the key.
The closure parameter is bound to an SMT term via the `env` map and the body re-`translate`d (no AST
substitution). Given the required bound, **two regimes:**

- **Bounded unroll** — a literal `.limit(N)` (`N ≤ 256`) expands to `⋀ₖ P(fᵏ(seed))` (or `⋁` for `any`). An
  *exact* equivalence — proves exactly the bounded contract the runtime checks; a failing element is a
  counterexample. `iterate(0){ n+2 }.limit(10).every{ even }` proves; `.any{ it == 6 }` finds the witness.
- **Induction** — a *symbolic* (or large) `.limit(n)`: `every{P}` becomes `P(seed) ∧ ∀x. (P(x) ⟹ P(f(x)))`
  — base + preservation. The runtime checks the actual `n`; the verifier proves P for **every** element
  (hence for any `n`) — reaching past the runtime's depth. So `iterate(0){ k+2 }.limit(n).every{ even }`
  proves all even, and `iterate(0){ (k+1)%10 }.limit(n).every{ 0 <= it < 10 }` proves the stream is
  **bounded for all elements** — hence its `+1` never overflows, a fact about element 2³¹ no test can reach.
  Honest negatives: a monotone `iterate(0){ k+1 }` has no finite bound and is *refused*, and the base case
  bites (an odd seed refutes "all even" even though `×2` preserves evenness).

**Soundness — the polarity gate.** `base ∧ step` is *stronger* than the `every` it stands for (sufficient,
not necessary): sound to **prove**, unsound to **assume**. So the induction encoding fires only for
stream-`every` nodes in **positive goal position** — `translateGoal` (called at the two postcondition-proof
sites) runs a polarity walk (`markPositiveEvery`: preserved through `&&`/`||` and an `==>` consequent,
flipped by `!`/`==>` antecedent, stopped elsewhere) and records the positively-placed nodes; everywhere else
(assumptions, negated positions) the stream-`every` is not strengthened and simply degrades to its runtime
check rather than risk a wrong verify. The bounded-unroll regime, being exact, needs no gate. `any` under a
symbolic limit is an existential that induction can't establish, so it skips. Int-element streams only this slice.

**Still out of fragment:** decimal/FP-element streams; stateful `generate(supplier)` (impure); and a later
**termination** overlay — turning the unbounded-`every` skip into a first-class diagnostic
("infinite source consumed without `.limit`/`.take` — would not terminate; add a bound"), and proving the
3-arg `iterate(seed, hasNext, next)` *terminates* via a `@Decreases`-style variant.

---

## Phase 76 — `List<BigDecimal>.max()` / `.min()`: the Real witnessed extremum  *(shipped)*

First slice of element-sort-generic lists: make the Phase-60 witnessed extremum serve **Real** (`BigDecimal`)
contents, not just Int. `maxMinOf` gained an `elemSort` parameter and mints the extremum constant `r` via a
new `varOfSort` helper (`realVar` for Real, `intVar` for Int); everything else is **unchanged**, because the
order comparisons (`le`/`ge`) and `eq` are arithmetic-polymorphic over Int and Real in Z3 — only the constant
is sort-specific. The `.max()`/`.min()` dispatch now mirrors `.sum()`'s element-type detection (strip
`old$`, look up `listElementTypes`): `null` → Int extremum, `BigDecimal` → Real extremum, String/enum → skip.

So `List<BigDecimal>.max()`/`.min()` carry the two defining facts — `r` bounds every element
(`∀i. xs[i] <= r`) and is achieved by one (`∃j. xs[j] == r`, guarded by non-emptiness) — and they **compose**:
`xs.max() >= xs.min()` proves for any non-empty decimal list (min is achieved at some `j`, and the max-bound
instantiates there). This completes the `List<BigDecimal>` story alongside the Phase-70 `.sum()`.

**Why this is the right shape.** Pushing `min`/`max` through is what forces a clean element-sort dispatch.
`min`/`max` are a *witnessed extremum* — an order comparison plus equality — so they generalize to Int, Real,
**and** FP (a later slice, under a no-NaN guard). `sum` does **not** generalize to FP: IEEE addition is
non-associative, so a list's sum depends on fold order and the Phase-70 sum-under-store law is false in FP.
So the element-generic future is: min/max for all element sorts, sum for Int/Real only. (FP-element arrays
followed in Phase 77.)

---

## Phase 77 — FP-element arrays (`double[]`) + the NaN-guarded FP extremum  *(shipped)*

The second element-sort-generic slice: IEEE-754 element arrays. `sortFor` routes `double → Float64`,
`float → Float32` — and **closes a latent soundness trap**: a non-Int element type used to fall through to
the `Int` default (so a `double[]` would have been modelled as `Array Int Int`); now it's an FP-element
array. The reads come for free — `translate(xs[i])` is a `select` that inherits the array's element sort, so
it's FP — and `isFpValued`/`asFp` gained the `xs[i]` (FP-element read) and `xs.max()`/`xs.min()` cases plus
an "already-FP-sorted" fallback, so comparisons and arithmetic on FP elements route to the FP theory. A
bounded `∀`/`∃` over the elements instantiates: `(0..<xs.length).every { xs[it] >= 0.0d }` as a precondition
lets `xs[0] >= 0.0d` prove. `VerifyChecker` now records non-Int **array component** types (not just list
generics) into `listElementTypes`, so a `double[]` param/field routes through `sortFor`. (Contracts use
`double[]` rather than `List<Double>` *originally*: a generic list's element type *erased* to `Object` inside
the contract closure under `@TypeChecked`, so `xs[it] >= 0.0d` wouldn't compile — arrays keep their component
type. **GROOVY-12071 lifted that**, so `List<Double>` element predicates now compile too; both forms work.)

**FP min/max is sound only under no-NaN.** FP is *not* totally ordered: Groovy's `max`/`min` returns NaN when
any element is NaN, and NaN is neither `fpLeq`-comparable nor `fpEq` to anything — so a `BigDecimal`-style
unconditional `∀i. xs[i] <= r` would be (a) **unsound** (it's false when `r` is NaN) and (b) vacuity-prone
(unsatisfiable if any element is NaN). So the FP branch of `maxMinOf` guards both facts by **all-non-NaN**
(`∀i. !isNaN(xs[i])`): `allNonNaN ⟹ (∀i. xs[i] <= r)` and `allNonNaN ⟹ (lo<hi ⟹ ∃j. xs[j] == r)`. When NaN
may be present the guard is simply false → no constraint, no vacuity; under a `!Double.isNaN` precondition
the guard discharges and the extremum proves. Verified empirically: `double[].max()` bounds every element
**under** `(0..<n).every{ !Double.isNaN(xs[it]) }` (and `max >= min` composes), and **refutes** without it.

**Scope (an honest correction to the original "unlocks the FP-list HumanEval cluster" claim).** What
genuinely works is FP min/max via the **axiomatised `.max()`/`.min()` spec helper** (the property tests
above) plus FP element predicates. The named HumanEval ports do **not** actually port, though: `rescale_to_unit`
returns a *transformed list* (FP list output — not modelled), and a hand-written `max_element` **witnessed-
extremum loop** over `double[]` fails *preservation* — Z3 returns a counterexample even bound-only and even
with `!Double.isNaN(m)` + a full-array no-NaN carried in the invariant. FP comparisons are *bit-blasted*, not
native linear arithmetic, so the quantifier-instantiation + `<=` transitivity that makes the **Int and
BigDecimal** witnessed-extremum loops (Phase 60/76) go through don't carry to FP inside a loop invariant. So
the FP min/max capability is real at the *spec-helper* level, but not as a loop-verified HumanEval port.
**Still out:** FP `.sum()` (non-associative); `has_close_elements` (nested pairwise quantifier); FP loops with
a quantified invariant (the bit-blasting/transitivity gap above). (`List<Double>` *scalar* element predicates,
once an `@TypeChecked` erasure gap that `double[]` worked around, now compile post-GROOVY-12071.)

---

## Phase 78 — list-literal returns + constant-index `result[k]`  *(shipped)*

The first half of the fixed-arity-product story (and step 1 toward `Tuple` support). Returning a list
*literal* used to be rejected outright — `return [s, p]` gave *"return expression `[1, 2]` is outside
fragment"* — because the result-binding only knew how to bind `result` to a *scalar* handle (and Phase 45b
aliased only `result.size()`, never the contents). Now the result-binding tries `tryRecordFactoryAssign`
first: if the return expression is a list/`List.of`/map/set **factory container**, `result` is recorded as
that container (size + non-null pinned), so `result.size()` and a **constant-index** `result[k]` fold to the
k-th returned element via the existing peephole fold. Wired at both the straight-line return site (`checkPath`)
and the loop return site (`checkUse`); the scalar/decimal/FP binding stays the fallback.

So a method may return `[a, b, …]` and have `@Ensures` reference its elements: the **faithful HumanEval 008
(`sum_product`)** now ports as `return [sum, product]` with `@Ensures({ result[0] == xs.sum() && result[1]
== xs.inject(1){a,x->a*x} })` (each element proven against its aggregate; a wrong element claim refutes) —
where it previously had to collapse to `s + p` for lack of list/tuple returns.

**`int[]`-typed returns ride this — two spellings.** (1) A method declared to return `int[]` whose body is a
*list literal* `[s, p]` needed no code: Groovy implicitly coerces the literal to the array, and
`tryRecordFactoryAssign` keys off the return *expression* (a `ListExpression`), so `result` binds as a list
factory regardless of the declared array type. The `sum_product` flagship ports with an `int[]` return this
way. (2) The *constructed* array literal `new int[]{s, p}` — an `ArrayExpression` with an initializer — is now
recognised in `factoryContainerFor` as a fixed-arity list-kind factory over its initializer expressions (the
array dual of a list literal), so it binds `result` identically; a body local `int[] r = new int[]{…}` records
as a factory too. Both fold `result[k]` / `result.length` / component-wise `==` via the Phase 78/81 machinery.
Locked by `P78 int[] return` tests (each spelling + crisp size-pin / element refutes).

**Sized allocation `new int[n]` (shipped).** The *fresh* array form — an `ArrayExpression` with
`sizeExpression != null` and no initializer — is a length-`n` array Java zero-fills. It isn't a fixed-arity
literal, so instead of a `FactoryContainer` it's modelled through the size/array oracles:
`Encoder.tryRecordSizedArrayAssign` (the `factoryContainerFor == null` fallback inside
`tryRecordFactoryAssign`, so every assignment/return call site picks it up) pins `sizeOf(name) == n`,
non-null, and — for an Int-element array — binds a **const-0 content array** (new backend
`constIntArray`, Z3 `mkConstArray`). So `new int[n]` as a return proves `result.length == n`, an unwritten
element reads `0`, a body local `int[] r = new int[n]; r[i] = v` bounds-checks and threads the store, and a
wrong length refutes. Single dimension; a non-Int element sort keeps havoced contents (sound). The `n < 0`
`NegativeArraySizeException` is not modelled — a negative size makes the index range unsatisfiable, so no
out-of-bounds is mis-verified (and a length-`n` postcondition stays sound: if it throws, the method never
returns). Locked by the `sized int[]` tests. **Still out:** multi-dimensional `new int[m][n]`; non-Int
zero-fill (`new double[n]` defaulting to `0.0d`).

**Still out (the `Tuple` layer, next):** *heterogeneous* fixed products with **named** accessors
(`.v1`/`.vN`/`.first`/`.second`), `new TupleN(...)` / `Tuple.tuple(...)` construction, and **multiple
assignment** (`def (a, b) = pair()`). A list literal is the *homogeneous, positional* case; a `TupleN` adds
per-slot types and names — modelled as a record of typed components on this same constant-index foundation.
Symbolic-index `result[i]` stays out (heterogeneous → no single element sort).

---

## Phase 79 — `Tuple` / `TupleN`: fixed-arity typed products  *(shipped)*

The named/heterogeneous half, built directly on Phase 78. `factoryContainerFor` now recognises
`Tuple.tuple(a, b, …)` (a `MethodCallExpression` on the `Tuple` class) and `new TupleN(a, b, …)` (a
`ConstructorCallExpression` whose type matches `Tuple\d+`) as **list-kind factory containers** — so the
existing index/size/first/last folds *and* the Phase-78 return-binding apply unchanged, and a returned tuple
binds `result`. Heterogeneity falls out for nothing: a factory container holds the slot **AST expressions**,
and each accessor translates its slot independently in its own sort — `new Tuple2(1, "hi")` gives an Int
`v1` and a String `v2` with no special machinery.

Accessors added: **named slots** — `.v1`/`.vN`, `.first`/`.second` (property form, in `translate(PropertyExpression)`)
and `.getV1()`/`.getVN()`/`.second()` (method form, in `foldFactoryMethodCall`) — via a single
`tupleSlotIndex` mapping (`v1`/`getV1`/`first` → 0, `v2`/`getV2`/`second` → 1, …). Constant-index `t[k]` and
`.size()` come from the Phase-78 list-factory folds. **Multiple assignment** `def (a, b) = rhs` desugars in
`BodyEncoder` to a fresh temp bound to `rhs` once, then `a = tmp[0]; b = tmp[1]` (a `TupleExpression` LHS —
which `ArgumentListExpression` extends; each slot read folds through the factory).

So `sum_product` ports as a **typed** `Tuple2<Integer,Integer>(sum, product)` with
`@Ensures({ result.v1 == xs.sum() && result.v2 == xs.inject(1){a,x->a*x} })`, and a wrong slot claim refutes.
Tuples are immutable, so there are **no `@Modifies`/havoc concerns** (a real simplification vs. collections).

**Still out:** symbolic-slot `t[i]` (heterogeneous → no single element sort); tuple **parameters** with
`.vN` access (Phase 80, below); component-wise tuple `==` and nested tuples.

---

## Phase 80 — tuple parameters with `.vN` access  *(shipped)*

Phase 79 bound *constructed/returned* tuples as factory containers (the slot expressions are known). A tuple
**parameter** is the dual: its slots are the *caller's* values, so there are no slot expressions — only the
declared `TupleN<...>` type. So a tuple param is modelled exactly like a Phase-45 object param (`b.field →
b$field`): `VerifyChecker.collectTupleParams` records `name → TupleN ClassNode` (params + fields) into a new
`tupleParams` map threaded to the `Encoder`, and each slot access mints a fresh **typed entity** `t$vN` in
the slot's sort (the slot type from the generic arguments, via `sortFor`) — the caller's uninterpreted
component value, consistent across references.

`tupleSlotEntity(name, k)` backs three access forms: `.v1`/`.vN`/`.first`/`.second` (property, in
`translate(PropertyExpression)`), `.getVN()`/`.second()` (method), and constant-index `t[k]` (in the
`LEFT_SQUARE_BRACKET` handler); `t.size()`/`t.size` fold to the arity. Heterogeneity is exact — a
`Tuple2<Integer,String> t` gives an Int `t$v1` and a String `t$v2`. So `@Ensures({ result == t.v1 })`,
`@Requires({ t.first >= 0 && t.second >= 0 })`, and `t.size() == 2` all verify, and `t.v1 >= 0 ⇒ result > 0`
refutes.

**Was a known limit, now fixed (GROOVY-12071):** slot *arithmetic* inside a *contract closure* — `t.v1 + t.v2`
— used to fail `@TypeChecked` because the slot generic erased to `Object` in the re-parsed closure
(`Object#plus`); GROOVY-12071 restored the closure's generics, so slot arithmetic/ordering now type-check
directly (comparisons like `result == t.v1` / `t.first >= 0` always worked). **Still out:** symbolic-slot `t[i]`, nested tuples, and string-slot *methods* in contracts
(`t.v2.length()` — the slot isn't yet recognised as a string receiver). (Component-wise `==` followed in Phase 81.)

---

## Phase 81 — component-wise tuple / list `==`  *(shipped)*

Equality over **fixed-arity products**. `tupleComponents(e)` extracts a side's component handles when `e` is
a factory container (a list literal, `Tuple.tuple(...)`, `new TupleN(...)`, `List.of(...)`) *or* a tuple
parameter (its `t$vN` slot entities). In `translateBinary`, a `COMPARE_EQUAL`/`COMPARE_NOT_EQUAL` whose
*both* sides yield component lists folds — ahead of the scalar paths, which would skip on a tuple operand —
to the conjunction of pairwise `eq`s (each in its component's sort), or `false` on a length mismatch
(Groovy's list/tuple equality); `!=` is the negation, and a sort mismatch between unlike products is a clean
skip. So two tuple params with equal components prove `a == b`, a tuple param proves `t == Tuple.tuple(5, 7)`
under `t.v1 == 5 && t.v2 == 7`, `Tuple.tuple(1,2) != Tuple.tuple(1,3)` proves, `Tuple.tuple(1,2) ==
Tuple.tuple(1,2,3)` refutes (different arity), and — the same fold for free — **list-literal equality**
`[1,2,3] == [1,2,3]` proves. **Still out:** symbolic-slot `t[i]`, equality against a *symbolic* list variable
(only fixed-arity products on both sides fold). (Nested tuples followed in Phase 82.)

---

## Phase 82 — nested tuples  *(shipped)*

Tuples whose components are themselves tuples, by making slot resolution **recursive**. For
constructed/returned tuples, `factoryContainerFor` gained a nested case: a constant-slot accessor
`X.vN`/`X[k]` on a list-kind product whose slot expression is *itself* a product returns that nested
container (recursing on the strictly smaller inner expression). Because every constructed-tuple fold
(property, index, `==`, size) routes through `factoryContainerFor`, they all handle nesting at once — so
`Tuple.tuple(Tuple.tuple(1,2),3).v1.v2` folds through to the leaf `2`. For tuple **parameters**,
`tupleParamRef` resolves an access chain to a `[flattenedEntityPrefix, TupleN type]`, descending through
nested tuple-typed slots, so `t.v1.v2` flattens to a fresh typed entity `t$v1$v2` (consistent across
references) in the leaf slot's sort. A shared `slotAccessor` helper recognises `.vN`/`.first`/`.second`/`[k]`.

**Was a known limit, now fixed (GROOVY-12071):** nested access used to work only in the method **body** — in a
*contract closure* `@TypeChecked` erased the nested generic, so `result.v1` was `Object` and `result.v1.v2`
wouldn't compile (`No such property: v2 for class Object`). GROOVY-12071 restored the closure's generics, so
`result.v1.v2` resolves in contracts too. The body still computes/binds nested values
(`Tuple.tuple(Tuple.tuple(1,2),3).v1.v2` folds to `2`; `int x = t.v1.v2` binds `t$v1$v2`). **Still out:**
symbolic-slot `t[i]`.

---

## Phase 83 — maps as named tuples (`m.key`)  *(shipped)*

Groovy's map literal is the *string-named* fixed-arity product (list = positional, `Tuple` = typed,
map = named), and the foundation was already there: a map literal `[sum: s, product: p]` is a `'map'`-kind
factory container, a returned map binds `result` (Phase 78), and the subscript form `result['sum']` folds via
`foldFactoryMapLookup`. The one gap was the **property form** `result.sum` — which *does* type-check under
`@TypeChecked` (map property access is allowed) but the verifier skipped. So this phase is one helper:
`foldMapPropertyByName(f, prop)` returns the value at the constant string key matching `prop` by a *direct
compile-time match* (no SMT key equality), or null if `prop` isn't an entry (so `m.size` etc. still reach
their own handling). Wired into `translate(PropertyExpression)`.

So `sum_product` now ports as the most self-documenting shape — `return [sum: s, product: p]` with
`@Ensures({ result.sum == xs.sum() && result.product == xs.inject(1){a,x->a*x} })` — joining the typed
`Tuple2` and positional `[sum, product]` forms; a wrong value refutes. The named map reads naturally for the
typical spec shape (each component *compared* to its aggregate). (Originally *arithmetic* on a map value in a
contract closure erased to `Object#plus`, like tuple slots / `List<Double>` — comparisons only; **GROOVY-12071
lifted that**, so `result.sum + result.product` type-checks too. See the Phase 84 update.) **Still out:**
non-constant keys, and map *parameters* (Phase 84, below).

---

## Phase 84 — map parameters with `.key` access  *(shipped)*

The dual of Phase 83 (and of the Phase-80 tuple-param work). A map *parameter* `Map<String,V> m` is already
modelled as a Z3 value array (Phase 27), so the subscript form `m['sum']` already read the value; the gap —
identical to Phase 83 — was the **property form** `m.sum`, which type-checks but the verifier skipped. One
helper `foldMapParamProperty(obj, prop)` routes `m.<key>` to a `select` of the map's value array at the
constant string key (`m.sum ≡ m['sum']`), in the value sort, placed *after* the `.size`/cardinality handling
and skipping a small reserved set (`empty`/`class`/`metaClass`) so map-API properties aren't misread as data
keys. It fires only for an **explicitly `String`-keyed** map and guards the `select` in a `try/catch` — a raw
`Map` / non-String key sort skips loudly (a robustness fix: it previously crashed Z3 with a key-domain sort
mismatch). Unlike a tuple param's fixed slots, a map param's keys are the caller's, so each `m.key` is a
fresh uninterpreted value in the value sort — consistent (same key ⇒ same `select`), e.g.
`m.sum == 3 ⇒ result == 3`, and a wrong value refutes.

**The erasure pattern is universal** (the honest correction to Phase 83): every generic-typed accessor — a
`List<Double>` element, a tuple slot, a map value (factory *or* param) — erases to `Object` inside a
re-parsed contract closure. So *arithmetic* (`m.x + m.y`) always fails `@TypeChecked` there; `==` is reliably
lenient; *ordering* comparisons are inconsistent (`m.x >= 5` compiles, but `result >= args.second` does not —
`Integer#compareTo(Object)`). The safe idiom across all of them: `==` (or simple bounds) in the contract,
arithmetic/ordering in the body.

**Update — GROOVY-12071 lifts this entirely.** The erasure above was a `@TypeChecked` bug: the
re-parsed contract closure dropped the method's declared generic types. GROOVY-12071 restores them, so every
generic-typed accessor keeps its type in the contract — `m.x + m.y`, `t.v1 + t.v2`, a `List<Double>` element
`>= 0.0d`, and nested `t.v1.v2` all type-check *and* verify with no cast and no "compute in the body" idiom.
The `(int)` casts and the raw-`Map` (`Map` → `Map<String, Integer>`) declarations the earlier examples used
were removed across the suite; a `GROOVY-12071` test group guards the dependency. The one cast that *stays* is
unrelated to erasure: the *seeded* GDK `sum(initial)` overload returns `Object` by signature (`below_zero`),
not an erased generic — so it still needs `(int)`.

**Named-argument maps are not verifiable** (the answer to "can we verify `def add(Map args)`?"). Groovy's
named-arg call `add(first: 1, second: 2)` collects a `Map` — but the idiom's natural form is a **raw `Map`**
with `Object` values, so even the *body* `args.first + args.second` is `Object#plus` under `@TypeChecked`
(which the verifier requires). The call syntax itself adds nothing to verify (it's a caller concern); the
method is just a map-param method, and a raw map is at odds with static typing. A *typed* `Map<String,V>`
method body works, and post-GROOVY-12071 its *contract* does too — but the named-arg idiom's natural form is
a **raw** `Map`, whose `Object` values have no generics to restore, so even the body `args.first + args.second`
is `Object#plus`. So: no — and the crash it used to provoke is now a clean skip. **Still out:** non-constant keys; map property `m.size` on a literal `size` key (the
method wins).

---

## Phase 85 — compound assignment operators (`+= -= *= /= %=`)  *(shipped)*

A statement-level desugar: Groovy keeps `s += xs[i]` as a distinct `PLUS_EQUAL` token (not pre-lowered), so
the body processors skipped it as an "unsupported statement." `Encoder.isCompoundAssign` / `desugarCompoundAssign`
rewrite `lhs OP= rhs` to the plain assignment `lhs = (lhs OP rhs)`, and both statement processors —
`BodyEncoder` (straight-line) and `LoopEncoder` (loop region) — desugar before their existing
variable/field/array-element assignment paths run, so all targets work uniformly: `s += xs[i]` (variable),
`a[i] += 1` (array element → an array store), and `this.f += e` (field). So `sumProduct`'s loop can read
`while (i < xs.size()) { s += xs[i]; p *= xs[i]; i += 1 }` and still verify, and a wrong result refutes.

**No overlap with contracts** — the obvious worry, ruled out: a contract closure is a side-effect-free
boolean predicate and never contains an assignment, so `+=` only ever appears as a *statement* in a method
body, handled by a code path entirely separate from the contract-expression translator. The desugar can't
touch contract semantics. (`==` vs `=` vs `+=` stay cleanly partitioned: `==` is contract equality, `=`/`+=`
are body statements.)

---

## Phase 86 — pre/post increment & decrement (`++` / `--`)  *(shipped)*

The sibling of Phase 85. The for-loop *update* slot already normalised `i++`/`--i` (Phase 59
`normalizeUpdate`), but `++`/`--` as **statements** elsewhere — straight-line `s++`, a while-body counter
`while (i < n) { c++; i++ }` — skipped ("statement with no modelled effect" / "unsupported statement in loop
region"). `Encoder.isIncDec` / `desugarIncDec` rewrite the inc/dec *statement* to `i = i + 1` / `i = i - 1`,
wired into `BodyEncoder` and `LoopEncoder` alongside the compound-assignment desugar. **As a statement the
pre/post distinction is irrelevant** — `i++` and `++i` differ only in the expression's *value*, which a
statement discards — so all four (`i++`/`++i`/`i--`/`--i`) collapse to the same assignment, and the operand
may be a variable, array element (`a[i]++` → an array store), or field. A wrong result refutes. Same
no-overlap-with-contracts property as Phase 85 (predicates never contain `++`).

**`++`/`--` in expression position (shipped) — variable target *and* array index.** A side-effecting inc/dec
used for its value (`x = i++`, `a[i++] = v`, `x = a[i++]`, `x = ++i`, and the two-cursor copy
`dst[j++] = src[i++]`) is **hoisted** out of the enclosing statement into an explicit sequence by
`Encoder.expandIncDecStatements`: **post**-forms become `[…uses operand…, …, operand = operand ± 1, …]` (the old
value, then the side effect) and **pre**-forms `[operand = operand ± 1, …, …uses operand…]` (side effect first,
new value). All inc/decs are collected and replaced by their operands (`replaceAllIncDec`), pre's hoisted
before and post's after.

**The safety condition — two sound routes (`appearsOnceSafe || evalOrderAssignSafe`).** A hoist is sound when
every other read of an inc/dec'd variable sees the value the hoist gives it. This was *learned the hard way*:
the first cut hoisted a single inc/dec unconditionally, which was **silently unsound** when the variable was
*also read after its own increment* — `x = i++ + i` proved `result == 0`, but Java advances `i` mid-statement
so the second `i` is `1` and the real value is `1`.

- **Route 1 — occurs exactly once** (`appearsOnceSafe`, a complete `countVarOccurrences` traversal). If each
  inc/dec variable appears only at its own site there is no interaction at all: pre's move before, post's
  after, in any order. Shape-agnostic. Closes the `i++ + i` hole *and* — distinct variables each satisfy it —
  enables the two-cursor `dst[j++] = src[i++]`.
- **Route 2 — evaluation order** (`evalOrderAssignSafe`). Admits the very common single-index `dst[i] =
  src[i++]`, where `i` appears twice but the hoist is still sound. Restricted to a slice we can order exactly:
  an assignment `LHS = RHS` built only from left-to-right shapes (vars, constants, arithmetic/subscript
  `BinaryExpression`s, inc/decs — no calls/properties/ternaries), no inc/dec in the LHS, every inc/dec on a
  simple var that is not the write target. Java evaluates the LHS index, then the RHS, then stores, so the
  check is per inc/dec in evaluation order: a **post** (`i++`, hoists *after*, all reads see the old value)
  must be the **last** occurrence of its variable — `dst[i] = src[i++]` ✓ (LHS `i` is earlier), `x = i++ + i`
  ✗ (a later read wants the new value); a **pre** (`++i`, hoists *before*, all reads see the new value) must
  be the **first** occurrence — `x = ++i + i` ✓, `dst[i] = src[++i]` ✗ (the LHS index, evaluated first, must
  read the old value). `i = i++` / `i = ++i` are excluded (inc var == write target — Java's store clobbers).

Anything outside both routes still skips loudly.

The hoist runs at the head of **every** body walk so all consumers agree: the VC passes
(`BodyEncoder.walkStatements`, `LoopEncoder.symExec`) and the obligation passes (`collectVfObligations` and
`dischargeRegion`). The `i = i + 1` re-assignment the hoist introduces throws the single-assignment value-flow
pass out — so the straight-line fallback was re-pointed from the value-flow-*blind* `dischargeObligationsHavoc`
to `dischargeRegion`, which threads the preceding statements (SSA), so an `a[i]` bounds check sees the reaching
`i` and a *later* access sees the bumped index. **Two lessons (both re-learned):** (1) the synthetic rewritten
`a[i]` must carry a **source position** (`stampedBinary`), or its bounds diagnostic is *silently dropped* — the
exact Phase-49c trap, and it read as a clean compile (looked sound, was silently unsound) until probed with an
out-of-bounds case; (2) routing through `dischargeRegion` is strictly more precise than the blind fallback, with
no regressions. So `a[i++] = v` / `x = a[i++]` store/read at the old index, the `a[i++]` array-fill loop
verifies, a sequence threads the index, and an out-of-bounds `a[i++]` refutes. Locked by `P expr inc/dec`.

---

## Phase 87 — Euclid's gcd via the `Gcd.of(a, b)` helper (HumanEval 013)  *(shipped)*

The two-*argument* sibling of the Phase 55/63 recurrence helpers (`Fib.of`/`Trib.of`). A new `verification.Gcd`
spec helper (executable Euclid, so the groovy-contracts runtime check still works) is recognised by `Encoder`
from the `Gcd.of(a, b)` shape and lowered to an uninterpreted `gcd$ : (Int, Int) -> Int`, constrained
mint-once by Euclid's defining axioms:

- **base** `∀x. gcd(x, 0) == x` (triggered on `gcd(x, 0)`),
- **step** `∀x, y. y ≠ 0 ⟹ gcd(x, y) == gcd(y, x % y)` (triggered on `gcd(x, y)`).

`gcdOf` mirrors `tribOf` but mints a *two*-bound-variable step quantifier and reuses the existing
`intRem` primitive for `x % y`. The flagship proof is **iterative-Euclid-equals-`Gcd.of`**: the loop invariant
`Gcd.of(x, y) == Gcd.of(a, b)` is preserved across `t = x % y; x = y; y = t` by e-matching the step axiom
(`y ≠ 0` from the guard) to `gcd(x, y) == gcd(y, x % y)`; at exit (`y == 0`) the base axiom collapses
`gcd(x, 0)` to `x`, so `result == Gcd.of(a, b)`; and it terminates on `@Decreases({ y })` because Z3's
Euclidean `mkMod` already knows `x % y ∈ [0, y)` for `x ≥ 0, y > 0`. A literal pair also unfolds
(`Gcd.of(12, 8)` → `gcd(8, 4)` → `gcd(4, 0)` → `4`).

**Prove/refute asymmetry (honest boundary, shared with `fib`/`trib`).** A *true* spec proves fast (UNSAT of
the negation via e-matching), but refuting a *false value* — e.g. `Gcd.of(12, 8) == 5` — only soft-fails on
"could not decide / timeout": finding a SAT model under an infinitely-instantiable recurrence axiom defeats
MBQI. Still **sound** — it is rejected, never a false pass — but it yields no counterexample, so the bad-case
test instead exercises a crisp, quantifier-free refutation (dropping the non-negativity precondition fails
the Euclid bounds invariant `x ≥ 0 ∧ y ≥ 0` on entry, counterexample `a = -1`).

**`Lcm.of(a, b)` (shipped) — the multiplicative sibling.** A `verification.Lcm` runtime helper
(`(a / gcd) * b`, dividing by the gcd first to stay exact and avoid `a * b` overflow) recognised like
`Gcd.of`, lowered to an uninterpreted `lcm$` built on `gcd$`: base (`∀a. lcm(a,0)==0`, `∀b. lcm(0,b)==0`)
plus the **fundamental identity** `∀a,b. lcm(a,b) * gcd(a,b) == a * b` (sound — `(a/gcd)*b` satisfies it by
construction, since the gcd divides `a`). So the identity proves symbolically, `Lcm.of(4,6)==12` unfolds via
Euclid + NIA, and `lcm(a,0)==0` proves. Co-shipped a sound, broadly-useful **gcd-nonzero** axiom
(`∀a,b. (a≠0 ∨ b≠0) ⟹ gcd(a,b) ≠ 0`) so the `a.intdiv(Gcd.of(a,b))` divide-by-gcd idiom discharges its
divisor obligation (without the precondition, `gcd(0,0)==0`, so it's loudly *not* discharged — sound).
Like the other recurrence helpers, **prove-friendly but refute-hostile**: a false value (`Lcm.of(4,6)==13`)
soft-fails to a loud "could not decide" rather than a crisp counterexample.

**Still out:** the `(a/gcd)*b == lcm(a,b)` *formula* proof (needs an extra `gcd | a` divisibility lemma);
multi-arg / list gcd (`[a, b, c].inject{…}` fold over `Gcd.of`); any *refutation* of a recurrence-helper
value (the MBQI gap above).

---

## Phase 88 — `do … while` body-runs-once semantics (a soundness fix)  *(shipped)*

`do B while (G)` is semantically `B; while (G) B` — the body executes once **unconditionally** before the
first guard test. The loop machinery (Phases 7/59/63) had recognised the do-while *guard* but otherwise ran
the **plain `while` VCs**: establishment checked the invariant at loop *entry* (before the body). That was
**silently unsound**. Counterexample (caught by a probe, now a regression test):

```groovy
@Requires({ n == 0 }) @Ensures({ result == 0 })
static int f(int n) {
    int i = 0
    @Invariant({ i == 0 })          // holds at entry (i==0)…
    @Decreases({ n - i })
    do { i++ } while (i < n)        // …but the body runs once → i==1 → result is 1, not 0
    return i
}
```

At `n == 0` the while-model reasons: establishment `i==0` holds at entry ✓; preservation is **vacuous**
(`i==0 ∧ i<0` is unsatisfiable, so the guard is never true); exit `I ∧ ¬G` pins `i==0` → it **proved**
`result == 0`, which is false at runtime. Pure silent unsoundness — the worst failure mode for this project.

**The fix** (small and surgical): `LoopSpec.isDoWhile` is set in `ContractExpansionTransform` (the loop is a
`DoWhileStatement`), and `checkEstablishment` runs the body **once** (`symExecBodyWithExits`, no guard
assumed) before checking the invariant — so the invariant is required to hold *after* the mandatory first
iteration. Preservation / progress / use (the residual `while`) are **unchanged** — that's the whole point of
the `B; while (G) B` decomposition. The establishment diagnostic is now do-while-aware ("Cannot prove loop
invariant holds **after the do-while's first iteration**"), since for a do-while the invariant may legitimately
hold on entry yet fail post-body. The fix both **closes the soundness hole** (the `f` above is now rejected at
establishment) and **enables** correct body-first loops: `@Invariant({ 1 <= i && i <= n })` on a `do { i++ }
while (i < n)` verifies (the `1 <= i` clause is false at entry but true after the first `i++`), proving
`result == n` — which the old pre-body establishment would have wrongly rejected.

## Phase 88b — do-while early return on the first iteration (a soundness fix)  *(shipped)*

The Phase 88 note above guessed an early `return` inside a do-while body was merely *imprecise* ("sound — it
skips/rejects"). It was not — probing turned up a **latent unsoundness**. A do-while in-body exit is
partitioned as a Phase-49b `'inBody'` early exit and checked by `checkEarlyExit` assuming
`(invariant ∧ guard)` at body entry. But a do-while runs its body *once before* the first guard/invariant, so
the exit can fire on the first iteration from the **entry** state, where the invariant isn't established and
the guard isn't checked. If the invariant is false at entry, that assumption is contradictory and the exit's
`@Ensures` is *vacuously* verified — so `do { if (i==5) return i; … } while (i>0)` under `@Invariant({i==0})`
falsely proved `result == 0` though it returns `5` (establishment passed vacuously too: it asserts ¬(exit
guard), which `i==5` makes UNSAT).

**The fix:** `checkEarlyExit` now splits into `checkEarlyExitPath(…, doWhileFirstIter)` and, for a do-while
in-body exit, runs it **twice** — the existing later-iteration check (`invariant ∧ guard`) for iterations ≥ 2,
**plus** a first-iteration check from the *entry* state (prefix-exit guards false, then the loop prefix; no
invariant, no guard), exactly the precondition `checkEstablishment` uses. Both must pass. So the false-at-entry
case now refutes (first-iteration check: `i==5` ⟹ `result==5 ≠ 0`), while valid first-iteration exits verify —
including the guard-false-at-entry shape (`@Requires({n==0})`, body runs once and returns). Plain `while`
loops are unaffected (`isDoWhile` false ⟹ only the standard path runs); the P49/P49b/P49c suites are green.
Locked by the `P88b do-while early-return` tests. **Lesson (again):** a "looks imprecise, surely sound"
assessment is worth *probing* — this one was silently unsound, the exact shape Phase 88 itself was.

---

## Phase 89 — Reference identity + identity-keyed field maps  *(slices 1–2 shipped; 2b closed as a dual-tenet boundary)*

**Status:** **slices 1 & 2 shipped** — reference identity (`===` / `!==` / `.is()`), identity-keyed field
*reads* (slice 1) **and** straight-line field *writes* (slice 2, the headline "write through `a` observed
through `b` iff they alias"). The **`old(obj.field)`-relative `transfer`** mutator (slice 2b) was investigated
and **deliberately not pursued** — it cannot be an executable groovy-contracts contract (a dual-tenet boundary,
detailed below). A **contained** revisit
of the Heap / aliasing non-goal (below) — the *flat-field* slice of it, with a boundary that can be stated in
one sentence. This carves out the part of aliasing that pays back (two-object mutators, frame soundness under
sharing) while explicitly leaving the part that doesn't (object-graph shape, reachability, separation logic).

**Slice 1 (shipped).** An object parameter whose class is shared by *another* object parameter is
*alias-modelled*: its Int fields read through a per-`(class, field)` map indexed by the object's identity
(`select(f$, id(a))`), and `a === b` / `a.is(b)` lowers to `id(a) == id(b)`. So `a.is(b) ⟹ a.f == b.f` is
provable (array congruence) and refuted without it. Single-object-param (and distinct-class) methods keep the
per-name `b$field` model untouched — **zero regression** — and the bare-field path used to assume a foreign
class invariant (Phase 45) is identity-keyed for alias-modelled receivers too, so an assumed `count >= 0`
still constrains the map read. Implementation: `Encoder.isAliasModeled` / `objId` / `fieldMap`; the read
hooks in `varFor` (bare field under a receiver) and the explicit `recv.field` translation; `===`/`!==` in
`translateBinary` and `.is()` in `translateMethodCall`. Read-only and Int-field-only by design.

**Slice 2 (shipped) — straight-line field writes.** Body assignment `a.f = v` becomes `f$ = store(f$, id(a), v)`
— a new `PropStore` path step (`BodyEncoder`) applied via `Encoder.storeField`, which rebinds the field-map
through the SSA-able array env (`arrayFor`/`bindArray`), so a later read — *including through an aliased
reference* — sees the store. This lights up the conceptual core: **a write through `a` is observed through `b`
exactly when `a === b`** (`a.is(b) ⟹ (a.balance = 100 ⟹ b.balance == 100)`, refuted without the alias) — the
"mutate via one handle, observe via another" reasoning the per-name model structurally cannot do. Int fields,
straight-line bodies.

**Slice 2b (investigated — deliberately NOT pursued, a dual-tenet boundary).** The full `transfer` relates the
post-state to the *pre-state* (`from.balance == old(from.balance) - amt`), which needs `old(obj.field)`. The
slice-2b plan was to start with a *dual-tenet check* — does groovy-contracts capture a parameter's field at
runtime? — and the answer is **no**: groovy-contracts' `old` is a **`Map` of `this`-class field snapshots keyed
by field name** (`OldVariableGenerationUtility.addOldVariableMethodNode` iterates `classNode.getFields()`;
`PostconditionGenerator` binds it as a `Map`-typed closure parameter), with **no `old(expr)` form** and, for a
`static` method, an **empty `old` whose references are rejected at compile time**. So `old(from.balance)` for a
parameter can only ever be a *verify-only* spec that **throws at runtime** when the dual check fires — which
breaks the executable-specs tenet that is the whole point. Implementing it would make the verifier bless a
contract that can't run, the inverse of the project's value. **So `old`-of-parameter-field is not implemented.**
The dual-compatible reasoning over the same write machinery is the slice-2 headline (no `old`). A genuinely
*dual* pre/post-relating mutator would need `this`-class *scalar* fields (where `old.field` works and is already
supported, Phase 13/45) — not object-reference parameters. (Also out, for the same scoping reasons: `@Modifies`
per-`(field, identity)` caller framing, and writes under loops/recursion — `PropStore` is handled in the main
body replay, not the recursion-termination / early-exit replays.)

**Update — GROOVY-12078 lifts the dual-tenet objection for *scalar* parameters.** Groovy now captures *old
parameter values* in `@Ensures` (incl. static methods). For a primitive param this is a capture *by value* at
entry, so the verifier's existing `old$<name>` snapshot machinery (Phase 13/45) — which already worked for any
name, field or param — is now **dual-valid**: `@Ensures({ result.a == old.b && result.b == old.a })` over
`static Map swap(int a, int b) { (a, b) = [b, a]; [a: a, b: b] }` (params reassigned by the swap) both
**verifies and runs**, with *no verifier change*. A wrong relation (`result.a == old.a`) refutes. Untyped
params work too (only the *return* must be typed `Map`, not `def`, so `result.a` resolves as a named-tuple
read). **Still to confirm — `old` of an array element / object-param field** (`old.a[1]` / `old(from.balance)`):
the verifier deep-models these as entry *contents*, so it's dual-valid only if GROOVY-12078 deep-snapshots at
entry; a *shallow* reference capture would read the mutated value at exit, making the in-place-array-swap spec
verify-only (the verifier proves it, the runtime contract behaves differently). Pending that, only the scalar
form is shipped as a test.

**The problem it removes.** Today a foreign-receiver field `b.field` translates to a *per-name* SMT entity
`b$field` (`Encoder.groovy:208`), "sound only under the no-aliasing assumption" (`:209`). Two references of
the same type therefore become two distinct variables — the verifier *silently* treats them as different
objects. So a write through `a` can never be observed through `b`, and any multi-object method built on the
per-name scheme would bake in disjointness: `transfer(x, x)` would mis-verify. That is the same
looks-fine/is-silently-unsound shape Phase 88 (`do-while`) turned out to have, so the fix is to build
multi-object support correctly *from the start* rather than patch it later.

**The encoding — the heap is one array per field, keyed by object identity** (reuses the array theory already
used for collections; no new solver capability):

| construct | encoding |
|---|---|
| object reference `a` | an opaque identity `id(a)` — an `Int` (or uninterpreted-sort) constant |
| field read `a.f` | `select(f$, id(a))`, where `f$ : ObjId → T` is *the* map for field `f` of that class |
| field write `a.f = v` | `f$' = store(f$, id(a), v)` |
| `a === b` / `a.is(b)` | `id(a) == id(b)` (and `!=` for `!==`) |
| `new C()` | a fresh `id` distinct from every live identity (the fresh-set-element trick) |
| two params `a, b` of the same class | identities **unconstrained** — the solver weighs *both* the aliased and the disjoint case |

Aliasing then falls out for free: `a.f` and `b.f` are `select(f$, id_a)` / `select(f$, id_b)`, equal **iff**
`id_a == id_b`. A `@Requires({ !from.is(to) })` adds `id_from != id_to` and the disjoint proof closes; without
it, the aliased model is live and a method that breaks under aliasing is **refuted**.

**VC / framing changes** (all extensions of existing machinery, no new theory):
- field read/write translation moves from the per-name `b$field` entity to `select`/`store` on `f$`;
- `old` snapshots the *whole* field-map `f$` (as it already snapshots array contents for collections);
- `@Modifies({ from.balance, to.balance })` frames *which `(field-map, identity)` cells* may change — the
  caller havocs `balance$` only at `{id_from, id_to}` and leaves every other field-map and cell intact;
- `new C()` mints a fresh identity asserted distinct from all in-scope references;
- method parameters of the same class start with **unconstrained** identities (aliasing is not assumed away).

**Worked example — proves when disjoint, refutes under aliasing** (impossible to express today):

```groovy
@Requires({ !from.is(to) && from.balance >= amt && amt >= 0 })
@Modifies({ [from.balance, to.balance] })
@Ensures({ from.balance == old(from.balance) - amt && to.balance == old(to.balance) + amt })
void transfer(Account from, Account to, int amt) { from.balance -= amt; to.balance += amt }
```

With `id_from != id_to` the two `store`s don't interfere → it **verifies**. Drop the `!from.is(to)`
precondition and the verifier returns the aliasing counterexample (`from === to`: balance ends at
`old − amt + amt = old`, not `old − amt`) → it **refutes** — a refutation the current per-name model cannot
produce (it would wrongly verify).

> **Dual-tenet caveat (the slice-2b finding).** This exact `transfer` is **not** an executable groovy-contracts
> contract: `old(from.balance)` cannot run at runtime. groovy-contracts' `old` is a **`Map` of `this`-class
> field snapshots keyed by field name** (`OldVariableGenerationUtility` / `PostconditionGenerator`) — it never
> captures a *parameter's* field, there is no `old(expr)` function form, and for a `static` method `old` is an
> empty map whose references are rejected at compile time. So `old(from.balance)` would be a *verify-only* spec
> that throws when the runtime check fires — which violates the executable-specs tenet. The **dual-compatible**
> way to exercise the same write machinery is the slice-2 headline (no `old`): a write through `a` observed
> through `b` iff `a === b`. The `old`-relative `transfer` is therefore **deliberately not pursued** — see
> Slice 2b below.

**What it unlocks:** two-object mutators (`transfer`, `swap`, `merge`), `@Modifies` framing that is honest
under sharing, "mutate via one handle / observe via another", reflexivity facts (`a === b ⟹ a.f == b.f`), and
"requires distinct inputs" specs — across object *parameters*, `this`, and `new`-minted objects.

**The boundary (one sentence, easy to teach):** *each field is a flat map from object identity to value; two
references alias exactly when `a === b`; we model field read/write, reference equality, and `new` freshness —
but not the* shape *of object graphs.* Concretely **out:** object-pointer linked structures (`next`/`left`/
`right`) and any reachability / "everything reachable from `x`" / separation reasoning (use an index array
like the Phase 16–26 DFS does); quantifying over *all* objects (`∀ obj. P(obj.f)`) — the moment you need that,
you are in separation-logic territory, which stays a non-goal. Collections of mutable objects are a follow-on
(a `List<C>` becomes `ObjId`-valued, composing this with the existing array model).

**Cost / risk.** Touches the field-translation core (the `b$field` path) and makes `@Modifies`/`old`/havoc
per-`(field, identity)` rather than per-name — a real phase, not an afternoon, though every piece reuses the
array/`old`/framing machinery already shipped. The discipline that keeps it a *slice* and not a slippery
slope: only *named* references and `new` get identities; no `∀`-over-objects. Value-to-cost is high precisely
because it also closes a latent soundness gap, not just adds expressiveness.

## Phase 90 — bare multiple assignment / swap `(a, b) = rhs`  *(shipped)*

Phase 79 shipped the *declaration* form `def (a, b) = [1, 2]`; this adds the bare **reassignment** form
`(a, b) = [b, a]` — the infamous swap — on existing locals. AST-wise the difference is small (the swap is a
`BinaryExpression` ASSIGN with a `TupleExpression` LHS, vs a `DeclarationExpression`), so `BodyEncoder` routes
both to a shared `tupleMultiAssign`.

**The catch — parallel semantics under aliasing.** The first cut reused Phase 79's desugaring (one temp bound
to the factory, then `a = tmp[0]; b = tmp[1]` via lazy slot reads) and it **failed the swap**: `tmp[1]`
re-reads the *expression* `a` at use time, *after* `a = tmp[0]` already overwrote it, so the swap collapsed
(`a` and `b` both ended up `4`). Phase 79 only ever worked because its examples had *constant* elements.

The fix mirrors how a compiler lowers parallel assignment: **snapshot each rhs element into its own temp
first, in source order, then write the targets** —

```
(a, b) = [b, a]   ⟿   __ma0 = b;  __ma1 = a;   a = __ma0;  b = __ma1
```

`__ma1` captures the old `a` *before* `a = __ma0` runs, so the swap is correct regardless of which targets the
rhs mentions. Element expressions are extracted for the factory shapes (`[…]`, `Tuple.tuple(…)`, `List.of(…)`,
`new TupleN(…)`); a non-factory rhs (opaque list value — not itself a target, so no aliasing risk) keeps the
temp + slot-read path.

**Soundness guard.** A non-variable target (`(a[i], a[j]) = …`) would be *silently un-modelled* by the
assignment loop — a later read would see a stale value (the Phase-49c silent-skip trap). So any non-`Variable`
target makes the whole statement skip **loudly** instead. (Declaration targets are always fresh variables, so
this never trips that form.) Array-element swap targets are a possible future slice (they'd need `ArrayStore`
steps for the targets).

**Shipped tests**: `(a, b) = [b, a]` verifies the parallel result; a *sequential* value (both → 4) refutes,
proving we model parallel not sequential; swap via `Tuple.tuple`; 3-way rotation `(a, b, c) = [c, a, b]`.

---

## Phase 91 — nested loops (two levels, compositional cut-points)  *(shipped)*

The long-standing "one annotated loop per method" limit is lifted to **two levels**: an annotated loop
directly inside another annotated loop's body. Each loop is cut by its own `@Invariant`/`@Decreases`; the
proof composes by the textbook rule — the outer loop treats the inner loop as a *summarised* construct, and
the inner loop is verified separately.

**The three moving parts** (all required for soundness — skipping the inner verification would mean
*assuming* an unproven inner invariant):

1. **Capture recurses** (`ContractExpansionTransform.captureLoops`). Nested loops now get their `LoopSpec`
   stashed too. Because the outer body is copied *shallowly* (`loopBodyCopy`), the inner loop node is shared,
   so the metadata set on it is visible through `site.spec.body`.
2. **Summarise during sym-exec** (`LoopEncoder.symExec` → `summarizeInner`). When sym-exec reaches a nested
   annotated loop — whether on the VC body walk *or* the obligation pass's `preceding` replay (the two share
   `symExec`, so they can't diverge) — instead of throwing it **havocs the variables the inner body writes
   (scalars via `havoc`, array contents via `havocArray`), then assumes `inner_inv ∧ ¬inner_guard`** — the
   inner loop's post-state. The frame is computed by a strict `innerFrame` partitioning writes into scalars
   and arrays; anything else (a field, a *collection* mutator that changes size, an unrecognised construct)
   returns false → **loud skip**, since under-havocking would let the outer keep a value the inner loop
   changed. Array *size* is deliberately not havoc'd (`a[k] = v` changes contents, not length).
3. **Verify the inner loop's own VCs** (`verifyNestedLoops`). Preservation and progress **reuse the standard
   `checkPreservation`/`checkProgress` verbatim** against an inner `LoopSite` — they're self-contained under
   `inner_inv ∧ inner_guard`. Establishment is custom (`checkNestedEstablishment`): `precondition ∧ class-inv
   ∧ outer_inv ∧ outer_guard ∧ ⟦outer-body stmts before the inner loop⟧ ⇒ inner_inv`.
4. **Discharge the inner loop's index/bounds obligations in ITS context** (`verifyLoopObligations` step 5). An
   inner `a[k] = …` must be bounds-checked under `inner_inv ∧ inner_guard`, where `k` is constrained — *not*
   under the outer invariant (where it isn't). `dischargeRegion` skips the inner loop's own sites and a
   dedicated pass re-discharges the inner body. **This is load-bearing for soundness**: a probe with
   `a.length >= n` (too small) for a flat fill that reaches `~n*m` is correctly caught as a possible
   `IndexOutOfBoundsException` — proving the inner bounds really are enforced, not skipped.

**The subtle point — the inner preservation is NOT under `outer_inv`.** The outer invariant is generally
*false* mid-inner-loop (e.g. `count == i*n` while the inner loop is incrementing `count`), so assuming it
would be unsound. The inner invariant must be self-contained — exactly as a standalone loop's would be.

**Why it's sound — proven by the probe set, not asserted.** The danger is a *too-weak* inner invariant that's
provable on its own yet doesn't pin the accumulator. It can't sneak a false outer result through: the inner
summary havocs the accumulator and the weak invariant fails to re-constrain it, so the **outer preservation
fails** (its counterexample literally shows `count$havoc$… = 8` unconstrained). Verified directly as a test.

**Inner loops may fill arrays.** `a[k] = v` in the inner body is supported (the scalar-only restriction of the
first cut is lifted): the summary havocs `a`'s contents and re-constrains them from `inner_inv`, and the
inner bounds are checked in the inner context. A buffer-clear `while (j < m) a[j] = 0` with
`(0..<j).every { a[it] == 0 }` verifies — and so does the **flat *n×m* matrix fill** `a[i*m + j] = 0`, whose
store bound `i*m + j < n*m` is nonlinear (Phase 91b, below).

### Phase 91b — a verifier-supplied NIA monotonicity lemma

The flat matrix fill's store bound needs `i*m + j < n*m`, which reduces to multiplying `i < n` by `m ≥ 0` —
a monotonicity step Z3's nonlinear tactic won't take on its own. Two small, sound additions close it:

1. **Guarded ground lemmas** (`emitMonotonicityLemmas`, in the `IndexSite` discharge). For products in the
   obligation that share a factor, assert `(0 ≤ p ∧ 0 ≤ r) ⟹ 0 ≤ p*r` (sign — for the *lower* bound
   `0 ≤ i*m + j`) and `(p < q ∧ 0 ≤ r) ⟹ p*r + r ≤ q*r` (monotonicity — for the *upper* bound), both
   orderings. Each is universally true, so asserting it is **sound by construction** (it can only help the
   proof direction); built from the original AST so the product terms unify with the goal's; scoped to that
   one solver session.
2. **Quantifier-strip for bounds** (`dropQuantifierConjuncts`). An array-index bound depends only on the
   index arithmetic and the size oracle — *never* on array contents or their aggregate. So for an `IndexSite`
   discharge, drop the conjuncts that carry a *quantified axiom*: `xs.every { … }`/`any`/closures **and**
   aggregation calls (`sum`/`product`/`count`/`min`/`max`/`inject`, whose `sum$`/`prod$`/… base+step axioms
   interfere the same way) — but **not** `size`/`length`, which a bound legitimately uses. Sound (dropping
   hypotheses only makes a proof harder), and it keeps Z3 out of the quantifier+NIA path that made it bail
   even *with* the lemma present. **This was the actual unlock** — with the lemma alone the bound still hung;
   the strip was the difference between "could not decide" and a clean proof. (Found by probe: the
   quantifier-free version of the same bound verified with the lemma, the quantifier-bearing one didn't. The
   aggregation case was added when the **flat matrix-sum** example — `sum == a[0..<k].sum()` carried as the
   invariant — hit the same wall as the `every`-bearing fill.)

Both are sound (the lemma is a true fact; the strip removes assumptions) and the out-of-bounds inner-store
test still refutes — the lemma relates to `n*m`, so a fill with only `a.length ≥ n` is still caught. Honest
limit: still a *heuristic* — self-products (`i*i`), three-way products, and bounds not reducible to
"multiply an inequality by a non-negative factor" remain "could not decide".

**Boundaries (all skip loudly, sound):** an *un-annotated* inner loop (no invariant to summarise with); an
inner loop that mutates a **collection's size** (`xs.add` — would need size havoc, deferred); three-deep
nesting; more than one inner loop in a body; an inner loop nested under an `if` (not a direct body
statement). The single-loop path is byte-for-byte unchanged (zero regressions across the suite).

**Shipped tests**: `count = n*n` and the rectangular `count = n*m` double loops verify end-to-end; the
buffer-clear array fill verifies; the **flat n×m matrix fill verifies** (via the Phase-91b lemma); false outer
postcondition refutes; false (off-by-one) inner invariant is caught at the inner loop's *entry*; the
weak-inner-invariant soundness anchor; an out-of-bounds inner store is caught; and the loud-skip boundaries
(un-annotated, collection-mutator, 3-level).

---

## Phase 92 — recursive/contracted call in a return expression, auto-hoisted  *(shipped)*

The verifier already modelled a recursive call as a single-assignment local RHS — `int rest = f(n-1);
return n * rest` — binding the local to the callee's `@Ensures` (the inductive hypothesis, for a self-call
with `@Decreases`). But the *same* call sitting directly in a return expression — `return n * f(n-1)`
(compound) or `return f(n-1, acc)` (bare tail call) — skipped, because a method call isn't a fragment
expression and `translate()` bailed. So the inductive factorial needed hand-hoisting into two lines, and a
`@TailRecursive`-shaped accumulator (`return helper(n-1, next)`) couldn't be reached at all.

This closes the gap by hoisting automatically: at the one point where the return-expression translation
returns null, each contracted/self call in the return is rewritten (via an `ExpressionTransformer`) to a
fresh implicit local bound by `assumeCalleeEnsures` — the exact machinery the local-RHS path uses — then the
rewritten expression is re-translated. So `return n * f(n-1)` and `return f(n-1, acc)` now verify with no
source change.

**Additive and sound.** The hoist fires *only* where the verifier would otherwise skip (`resHandle ==
null`), so every previously-passing path is byte-for-byte unchanged. `assumeCalleeEnsures` declines (→ clean
skip, no mis-bind) when the callee has no usable or sort-matching `@Ensures` — so a non-int return, an
un-contracted call, or a sort mismatch still skips loudly rather than binding a garbage handle. The callee's
`@Requires` is discharged by the separate obligation pass over the *original* return expression, so the
precondition check is unaffected.

**Shipped tests**: the compound `return n * fact(n-1)` and the bare tail `return factHelper(n-1, next)`
(accumulator) both verify; a false `@Ensures` on a bare-return method still refutes at the base case; a
recursive call that breaks its callee's `@Requires` (`f(n-2)` reaching `f(-1)`) still refutes on the
precondition.

**Scope / boundaries:** int/long-returning methods (the fresh handle is an `intVar`). Boolean predicates and
collection-returning recursive tail calls still skip — the sort mismatch makes `assumeCalleeEnsures` decline
— so no regression, just not newly covered. Closes gap #2 of the `@TailRecursive` interaction; the other two
(transform ordering so the verifier sees the *pre*-transform recursive body, and exact-value NIA bounds)
remain open.

---

## Phase 93 — the `**` power operator (first slice: typing + congruence)  *(shipped)*

Z3's arithmetic has no variable-exponent power, so `base ** exp` lowers to an **uninterpreted**
`pow$ : (Int, Int) -> Int` carrying no value axioms. Two applications with the same `(base, exp)` share the
term (congruence), so `result == base ** exp` proves, while value properties — `2 ** n >= 1`, or even the
literal `2 ** 3 == 8` — honestly stayed "could not decide" (Phase 93b below lifts the literal and recurrence
cases with defining axioms). The point of this first slice is *typing*: Groovy's `**`
returns `Number`, so the int surface is `(base ** exp).intValue()` — `.intValue()` / `.longValue()` translate
the receiver and are identity on the integral `pow$` term, landing the expression in an `int` context.

Bare `2 ** n` (no `.intValue()` / cast) is a Groovy `Number`→`int` type error before the verifier sees it.

**Shipped tests**: `result == (2 ** n).intValue()` proves by congruence.

### Phase 93b — `pow$` defining axioms  *(shipped)*

The deferred value axioms now ship, minted once by `powOf` exactly like `fibOf`/`gcdOf`: base `∀b. pow(b,0)==1`
and step `∀b,k. k≥1 ⟹ pow(b,k) == b·pow(b,k-1)`, triggered on `pow(b,k)`. Two tiers of proof open up:

- **Tier 1 — literal exponent unfolds to a value.** `2 ** 3` e-matches down `pow(2,3) → 2·pow(2,2) → … →
  2·2·2·1`, so `(2 ** 3).intValue() == 8` proves and `== 9` refutes. (Was "could not decide" in Phase 93.)
- **Tier 2 — the doubling recurrence proves for *symbolic* n.** `2 ** (n+1) == 2 * (2 ** n)` e-matches the
  step on `pow(2, n+1)`. This is the verification analog of the runtime `(0..10).each { assert 1<<n == 2**n }`
  — and strictly stronger, since it holds for *all* `n ≥ 0`, not just the sampled range.

**The trade — symbolic value claims are now refute-hostile.** A false symbolic-exponent claim like
`2 ** n == 5` no longer yields a crisp counterexample; the step's e-matching unfolds `pow(2,n) → pow(2,n-1) →
…` and exhausts the per-VC timeout, so it soft-fails to "could not decide". Honest (never a false proof), and
the same trade the bit-blasted bitwise/FP fragments and the `Fib`/`Gcd` recurrences already make. Deeper
symbolic *value* facts (`2 ** n ≥ 1`) still need induction the finite e-matching can't reach — also "could
not decide". For a symbolic base the step's `b·pow(…)` is NIA (timeout-gated); for the common literal base it
stays linear.

**Bridge to `<<` (not yet).** A *symbolic* `1 << n` is a 32-bit bit-vector while `2 ** n` is `pow$` over Int,
so `1 << n == 2 ** n` for symbolic `n` is still a sort-mismatched loud skip. The literal rows (`1 << 3` is the
arithmetic `1·2^3`) now line up with `2 ** 3 == 8`. Recognising a power-of-two `<<` base as `pow(2, ·)` is a
separate slice. Note the machine identity is *false* past the width boundary anyway — Java masks the shift
count (`1 << 32 == 1`) while `2 ** 32` is `4294967296` — so any `int`-level `<<`/`**` equivalence belongs
behind a range guard / `@CheckOverflow`.

**Shipped tests (Phase 93b)**: literal `2 ** 3 == 8` / `!= 9` / base `2 ** 0 == 1`; the symbolic doubling
recurrence `2 ** (n+1) == 2 * (2 ** n)`; and the refute-hostile `2 ** n == 5` soft-failing to could-not-decide.

---

## Phase 94 — `void`-method (lemma) postcondition enforcement  *(shipped — a soundness fix)*

A `void` method's `@Ensures` was **silently not enforced**: `@Ensures({ 1 == 2 }) void bad() {}` compiled
clean, as did a false post-state claim (`@Ensures({ x == 99 }) void set5() { x = 5 }`). At runtime
groovy-contracts *does* evaluate and throw, so "verified" while the runtime fails was a silent unsoundness —
the failure mode the whole project is built to avoid.

**Root cause.** A value-returning method anchors its postcondition refutation on the *return expression*
(`p.result`, a positioned body node). A void method has none, so the code fell back to anchoring on the
{@code MethodNode} — and Groovy's `StaticTypeCheckingVisitor` **silently drops** an error anchored on a
`MethodNode` reached via the extension's `afterVisitMethod` path (the error never enters the collector). The
verification itself was running and *refuting* correctly; only the diagnostic was being swallowed. The fix
(in `checkPath`) anchors a void method's postcondition/invariant error on the **`@Ensures` expression**
(`postAst`, a positioned `BinaryExpression`) instead. One-line cause, but it took a negative control to find
— a false `@Ensures` "passing" looks identical to a real proof until you assert it *must* fail.

**What it unlocks — the lemma idiom, and with it genuine inductive `**` reasoning.** A lemma is canonically a
`void` method whose `@Ensures` *is* the claim. With enforcement:

- The pure void-lemma form of the doubling recurrence — `@Ensures({ 2 ** (n+1) == 2 * (2 ** n) })` — is now a
  **genuine** proof (was vacuous), off the Phase 93b step axiom.
- A **self-induction** void lemma (`@Decreases` recursion supplies the IH; the `pow$` step axiom does the
  arithmetic) proves a *symbolic-exponent* value fact: `@Ensures({ (2 ** n).intValue() >= 1 })` for
  `pow2pos(int n) { if (n > 0) pow2pos(n-1) }`. The base case (`2 ** 0 == 1 ≥ 1`) and the inductive step both
  bite — the negative control `2 ** n >= 2` is correctly *held to account* at `n = 0` rather than passing
  vacuously. This is the rung above the one-step recurrence on the path toward a `1 << n == 2 ** n` bridge.

The whole 905-test suite stays green under enforcement — i.e. no existing void-method test was silently
relying on the vacuous pass (a real risk the full-suite run had to rule out).

**Diagnostic position.** Captured `@Ensures` ASTs lose their source positions (they report line 1), so
anchoring on the contract AST would surface the error at the wrong line. Instead the void path mints a
positioned proxy `ConstantExpression` that copies the method's *real* declaration position — an `Expression`
(so STC surfaces it, unlike a `MethodNode`) carrying the true source line. So a void lemma's refutation now
points at its method declaration, like any other diagnostic. The class-invariant-only void path keeps the
`MethodNode` fallback (a void method with only an invariant isn't the lemma case); enforcing *that* the same
way is a follow-on.

**Shipped tests (Phase 94)**: false void `@Ensures` (const / post-state / over-param) all refute; a true void
`@Ensures` verifies; the genuine `doublesEachStep` void lemma; a false doubling variant soft-failing
(refute-hostile); and the self-induction `2 ** n >= 1` with its `2 ** n >= 2` negative control.

---

## Phase 97 — safe-navigation precondition carries the non-null fact  *(shipped)*

A precondition conjunct `recv?.foo()` can only be truthy when `recv` is non-null — Groovy's `?.` short-circuits
a null receiver to `null`, which is falsy. So when such a conjunct is *assumed* at a method's entry, the
receiver is non-null, and a later unguarded `recv.bar()` in the body discharges its null-dereference obligation
without a redundant explicit `recv != null`. Previously `@Requires({ s?.startsWith("user:") })` left `s` nullable
in the model, so `s.substring(5)` spuriously failed with `Possible NullPointerException`.

`assumeSafeNavReceiversNonNull` walks the precondition's **top-level `&&` conjuncts** (`collectAndConjuncts`)
and, for each that is a safe-navigation call/property `recv?.x` with a simple-variable receiver, asserts
`not(nullityOf(recv))`. Wired into both precondition-assumption paths — `assumeContext` (implicit-obligation
discharge) and `dischargeVfObligation` (value-flow); the deref check routes through the latter, which is why
both are needed. **Soundness rests on the conjunctive position**: the walk descends through `&&` only, so a
safe-nav under an `||` branch or a negation carries no non-null implication — `@Requires({ s?.startsWith("user:")
|| s == null })` still flags the NPE, and `s` really can be null there.

Scope: receiver must be a simple variable (a parameter/field name with a nullity oracle); `a.b?.c()` and
safe-nav in *value* position (`s?.length()` as a nullable int) are out — value-position `?.` would need a
nullable-int model. Pairs with the null-safe operators already handled (`==~`, GString) where the body never
dereferences the value, so no guard is needed at all.

**Shipped tests (Phase 97)**: `idLength` with a `s?.startsWith("user:")` precondition proves (no explicit null
guard); the `|| s == null` weakening still flags the `NullPointerException` (the soundness control).

---

## Phase 98 — Elvis operator `a ?: b`  *(shipped)*

`a ?: b` is `groovyTruth(a) ? a : b` — its condition is *Groovy truth on the first operand* (which is also the
then-branch), not a boolean. Elvis's AST node `ElvisOperatorExpression` subclasses `TernaryExpression`, so it
fell into the general ternary handler, which fed `a` straight in as the `ite` condition — for `n ?: 5` that
cast an `Int` term to `Bool` and threw `GroovyCastException`, **crashing the whole compile** (worse than a
loud skip). Fixed: a dedicated `ElvisOperatorExpression` case ahead of the ternary one, with `groovyTruth`
modelling the condition per operand type.

- **Integral operand** (`int`/`Integer`/…): `ite(a != 0, a, b)` — Groovy's int truth is exactly `!= 0`. So
  `n ?: 5` is `(n != 0) ? n : 5`: `@Requires({ n > 0 })` proves `result == n`, an `n == 0` guard proves
  `result == 5`, and an unguarded `result >= 5` correctly refutes (n could be negative).
- **`String` operand** (Phase 98b): non-null ∧ non-empty — `ite(¬null(s) ∧ stringLength(s) > 0, s, b)`, matching
  Groovy's String truth (`""` and `null` are both falsy). So `s ?: "d"` proves `result == s` under
  `s.length() > 1`, proves `result == "d"` when `s` is empty, and the unguarded `result == s` refutes.
- **Plain object reference** (Phase 98b): non-null — `ite(¬null(o), o, b)`. Sound *because* `isPlainObjectTruth`
  excludes types whose truth isn't simply non-null: numbers, `Boolean`, `String`/`GString`, collections/`Map`,
  arrays, and — the subtle one — any class that **overrides `asBoolean()`** (its truth is whatever that
  returns), detected via `getMethods('asBoolean')`.
- **Collection / `Map` operand**: skips loudly. A list/map has no single-term SMT value to thread through the
  `ite` (it's a size+array oracle bundle), so the operand doesn't translate and the Elvis returns null →
  "outside fragment". Their truth (non-null ∧ non-empty) is moot without a first-class value.
- **Non-nameable operand** (a method call, `a.b?.c`): skips — the non-null model needs a nullity oracle keyed
  by a simple name.

`?:` in *contract* closures was already concretely evaluated by `PureEvaluator`/`ContractTester`; this is the
symbolic-body encoder catching up. Reuses the `nullityOf` oracle from the Phase 97 safe-navigation work.

**Shipped tests (Phase 98)**: int `n ?: 5` proves under `n > 0` / `n == 0` and the unguarded `>= 5` refutes;
String `s ?: "d"` proves under non-empty / empty guards with the unguarded `result == s` refuting; object
`a ?: b` proves `result == a` under `a != null` with the unguarded form refuting; a `List ?: []` skips cleanly.

---

## Phase 99 — integer range membership `i in lo..hi` / `(lo..hi).contains(i)`  *(shipped)*

Range membership in a contract was a loud skip (`precondition '(i in (1..3))' is outside fragment`) — the
first blocker in idioms like `@Requires({ i in 1..3 })`. Now an *integer* range lowers to its bounds, reusing
the order- and exclusivity-aware predicate already built for `Range.containsWithinBounds` (Phase 74):
`(lo ≤/< i ∧ i ≤/< hi) ∨ (hi ≤/< i ∧ i ≤/< lo)` — `≤` at an inclusive endpoint, `<` at an exclusive one. So
`i in 1..3` is `1 ≤ i ≤ 3`, `i in 0..<3` is `0 ≤ i < 3`, both directions and `..`/`..<`/`<..`/`<..<` covered;
`i !in lo..hi` negates it. The `in` operator (a `BinaryExpression`) and `(lo..hi).contains(i)` (a method call)
both route through one `translateIntRangeContains` helper.

For an integer range (step 1) the integer-membership `contains` *coincides* with pure bounds — every integer
in the interval is a member. The two diverge for a step-sensitive / decimal case (`(1..3).contains(2.5)` is
`false` though 2.5 is within bounds), so the helper is **gated**: integer endpoints, and an **Int-sorted
value**. The value type can't come from the AST — a contract-closure variable like `i` reports `Object` — so
it's gated on the *modelled sort* instead (`session.isReal` ⇒ skip).

### Phase 99b — single-char `String` range membership `s in 'A'..'Z'`  *(shipped)*

A single-char `String` range *is* a regex character class: `s in 'A'..'Z'` ⟺ `s.matches("[A-Z]")`. So it
lowers to `str.in_re(s, re.range('A', 'Z'))` — the identical `reRange`/`stringInRegex` construction the regex
engine already builds for `[a-z]` (Phase 47d). `re.range` matches *exactly one* character in the code-point
interval, so a multi-character or empty `s` is a non-member for free — no separate length constraint. Endpoints
are constant single-char Strings, so direction and `..<`/`<..` exclusivity collapse to constant code-point
arithmetic on the `[lo, hi]` interval (an empty interval matches nothing). `translateStringRangeContains`
shares the two dispatch points with the integer helper. Gated: String-typed value (`isStringReceiver`),
single-char constant endpoints — multi-char endpoints (`'aa'..'zz'`, which Groovy iterates by string-increment,
not a char range), symbolic endpoints, or a non-String value skip loudly.

Consequence for the `@Ensures({ result in 'A'..'Z' })` example: the int-range precondition `i in 0..25` and the
char-range postcondition `result in 'A'..'Z'` both translate (the `'A'.next(i)` body lands in Phase 100, below).

**Shipped tests (Phase 99)**: `i in 1..3` and `(1..3).contains(i)` prove their bounds; exclusive `i in 0..<3`
proves `< 3`; the soundness control `i in 1..3` ⇒ `result <= 2` refutes with `i = 3`; `i !in 1..3` excludes the
interval. **Phase 99b**: `'M' in 'A'..'Z'` and `'5' in '0'..'9'` prove; `'m' in 'A'..'Z'` refutes; exclusive
`'B' in 'A'..<'C'` proves; a `String s in 'A'..'Z'` precondition carries through an identity body.

---

## Phase 100 — `String.next(i)` / `String.next()` (char shift)  *(shipped — single-char first slice)*

Groovy 6 has `String.next(int)` (the no-arg `next()` is the `i == 1` case): the last character incremented by
`i` — `'A'.next(2) == 'C'`, `'A'.next(25) == 'Z'`. (It's genuinely in 6.0; older Groovy throws
`MissingMethodException` on the `int` overload — so this models a *real* method, verified against the project's
`6.0.0-SNAPSHOT`.) First slice: **single-character** receivers, ASCII, no wraparound/Unicode.

`s.next(i)` lowers to a **fresh single-char string** `r` whose code point is `charAt(s,0) + i`, asserted
*conditionally* on `s` being single-char: `len(s) == 1 ⟹ (len(r) == 1 ∧ charAt(r,0) == charAt(s,0) + i)`. So a
multi-character receiver leaves `r` unconstrained — an honest "could not decide", never a wrong answer. The
result connects to range membership because `str.in_re` (Phase 99b) bridges to a char's code in Z3 (verified:
`s in 'A'..'Z'` proves `charAt(s,0) ∈ [65,90]`). So the original example now fully verifies:

```groovy
@Requires({ i in 0..25 })
@Ensures({ result in 'A'..'Z' })
static String letter(int i) { 'A'.next(i) }     // ✓  (widen to 0..30 and it refutes — 'A'.next(26) == '[')
```

**Receiver nullity** (resolved by Phase 101): a `String` *parameter* receiver `s.next()` no longer needs an
explicit `s != null` — a `s in 'A'..'Z'` precondition now implies it. Multi-char receivers and the
carry/wraparound at code boundaries remain out.

**Shipped tests (Phase 100)**: `'A'.next(i)` for `i in 0..25` proves `result in 'A'..'Z'`; widening to `0..30`
refutes; `s.next()` on `s in 'A'..'Y'` proves `result in 'B'..'Z'`; the soundness control `s in 'A'..'Z'` ⇒
`result in 'B'..'Z'` refutes at `s == 'Z'`.

---

## Phase 101 — range membership implies non-null  *(shipped)*

A top-level precondition conjunct `v in lo..hi` forces `v != null` — a `Range` never contains `null`, so the
membership can't hold for a null `v`. So an unguarded `v.foo()` in the body discharges its null-deref
obligation without a redundant explicit `v != null` (it removed exactly that guard from the Phase 100
`s.next()` param tests). Generalises the Phase 97 safe-navigation inference: the same
`assumePreconditionNonNullFacts` walk over top-level `&&` conjuncts now recognises a `Range`-right-operand
`in` alongside `recv?.foo()`, and asserts `¬null(v)` for the named value.

**Sound only for ranges, and only conjunctively.** List/Set membership is deliberately *excluded* — a
collection may hold `null`, so `x in [null, a]` doesn't imply `x != null`. And the implication holds only at a
top-level `&&` conjunct: weaken to `v in lo..hi || v == null` and `v` can still be null, so the walk descends
through `&&` only (verified by the `||` control, which still flags the NPE).

**Shipped tests (Phase 101)**: a `s in 'A'..'Z'` precondition lets `s.length()` deref with no explicit null
guard; the `|| s == null` weakening still flags the `NullPointerException`.

---

## Phase 102 — switch *expressions* (arrow form, simple literal labels)  *(shipped)*

A switch *expression* `switch(i){ case 1 -> 'a'; … }` desugars (by the time the verifier sees `ORIGINAL_BODY`)
into an IIFE: `{ -> <SwitchStatement> }.call()` — a no-arg closure wrapping a `SwitchStatement` whose cases
`return` their yielded value. The encoder recognises that exact shape (`soleSwitchOf` / `caseValueExpr`) and
lowers the switch to an **ite-chain**:

```
switch(i){ case 1->'a'; case 2->'b'; case 3->'c' }   →   ite(i==1,'a', ite(i==2,'b', ite(i==3,'c', UNMATCHED)))
```

so it's a single return expression that `checkPath` proves directly — no `BodyEncoder` change. The subject
compares in its own sort (int `eq` or, for a `String` subject, seq `eq` via `translateInSort`); the branch
values share a result sort (int or String). **UNMATCHED** is the `default ->` value, or — with no default —
a *fresh unconstrained* term of the result sort: Groovy yields `null` on no-match (verified — `letter(5) ==
null`, not an exception), so requiring it to satisfy a non-trivial postcondition is a sound conservative
refute, while a precondition covering every case makes the branch dead and lets the proof through.

With the range phases (99 / 99b) this closes the original target end-to-end:

```groovy
@Requires({ i in 1..3 })
@Ensures({ result in 'a'..'c' })
static String letter(int i) { switch(i){ case 1 -> 'a'; case 2 -> 'b'; case 3 -> 'c' } }   // ✓ proves
```

**Scope / out:** switch *expressions* only (a switch *statement* stays an "unsupported statement" skip);
single literal `int`/`String` labels (multi-label `case 1, 2 ->`, ranges, type/pattern labels, and complex
multi-statement case bodies skip loudly); decimal subjects and mixed-sort branches skip. Modelling no-match as
`null` precisely (rather than a fresh term) — for null-tolerant postconditions over a *reachable* no-match — is
a possible refinement.

**Shipped tests (Phase 102)**: the `letter` target proves; widening to `i in 1..4` refutes at the unmatched
`i = 4`; a false `result in 'a'..'b'` refutes (case 3 yields `'c'`); a `default ->` covering all cases proves
with no precondition; a `String`-subject switch proves.

---

## Phase 103 — low-bit mask `x & (2^k − 1)` as Euclidean mod  *(shipped — lands the OpenJML BitVectors proof)*

A low-bit mask `x & (2^k − 1)` keeps exactly the low k bits, which **is** the Euclidean mod `x mod 2^k` — for
*every* x (two's-complement, negative, even unbounded, since `2^k | 2^32`). So when one `&` operand is a literal
`2^k − 1` (`1, 3, 7, 15, 0xff, 0xffff, …`), the encoder lowers it to `intMod(x, 2^k)` (Z3 `mkMod`, `∈ [0, 2^k)`)
instead of a bit-vector `bvAnd`. A non-low-bit-mask `&` (e.g. `x & 0x0a`) keeps the faithful bit-vector path.

**Why:** a bit-vector `&` proves *range* facts but doesn't bridge to *arithmetic* `%` — Z3's bit-blasting and LIA
don't connect, so divisibility times out. Keeping the mask in LIA bridges to `+` / `%` / divisibility. This lands
the [OpenJML BitVectors tutorial](https://www.openjml.org/tutorial/BitVectors)'s culminating proof — round-up to
the next multiple of 16, where the spec is pure arithmetic but the body is a bit-trick:

```groovy
@Requires({ n <= 0x7ffffff0 })
@Ensures({ n <= result && result <= n + 15 && result % 16 == 0 })
static int roundUp(int n) { n + ((-n) & 0x0f) }       // ✓ proves; before, `result % 16 == 0` timed out
```

The `range` half (`n ≤ result ≤ n+15`) already proved from the bit-vector's `[0,15]` range; this slice closes the
divisibility half. It also makes parity / flag-masking (`x & 1`, `flags & 0xff`) *arithmetic* — cheaper than
bit-blasting and refute-friendly rather than timeout-prone. **Sound** by the exact identity; verified by a
soundness control (`result % 16 == 8` refutes with `n = INT_MIN`) and no regression in the existing `&`/`|`/`^`
tests (`6 & 3 == 2` still folds — `3` is a mask, `mod(6,4) == 2`).

**Shipped tests (Phase 103)**: the OpenJML `roundUp` proves range + `% 16 == 0`; `result % 16 == 8` refutes;
`x & 1 ∈ {0,1}` and `x & 7 ∈ [0,7]` prove arithmetically.

---

## Phase 104 — OpenJML "Max by elimination" (disjunctive loop invariant)  *(shipped — no engine change)*

A second port from [openjml.org/examples](https://www.openjml.org/examples/) (CC BY-NC), after the
BitVectors `roundUp` of Phase 103. `max(int[])` finds the index of a maximum by shrinking a window
`[x, y]` from whichever end is no larger until it collapses. The teaching point is the **disjunctive**
loop invariant: the running maximum sits at *one* endpoint, but which one flips as the window shrinks —
a single-disjunct invariant isn't preserved. The existing quantifier + `@Decreases` machinery (Phases
6/9 quantifiers, loop invariants) carries the disjunction through preservation and collapses both arms
at `x == y` to discharge `∀i. a[i] ≤ a[result]`. **No engine change** — purely a fragment-coverage
example, the disjunctive-invariant shape just hadn't been exercised before.

**Shipped tests (Phase 104, group `P104 OpenJML`)**: `max` proves `result` indexes a maximum;
flipping the postcondition to a *minimum* claim refutes. README gains an "OpenJML Examples" section
(BitVectors round-up + this), crediting the source under CC BY-NC.

**Test-harness note (not a phase):** `VerifyHarness.CASES` outgrew the JVM's 64KB per-method
bytecode limit — a single static initializer for all ~945 cases overflowed `<clinit>`. Split the
list literal across `casesPart1()` + `casesPart2()` helper methods (concatenated into `CASES`) so
each initializer stays under the limit; further cases can split again as needed.

---

## Phase 105 — read-only per-character string proofs (string-sequence, slice 1)  *(shipped)*

The first slice toward string-sequence reasoning (e.g. OpenJML `ChangeCase`). Measured the tractability
frontier first (six probes, each with a refutation control): Z3's native String/seq theory **does**
discharge a quantified loop invariant over `seq.nth` — so *read-only* per-character iteration (the string
analogue of the array "∀ element satisfies P" proofs) works end-to-end. Construction-**content** induction
(`(r ++ c).charAt(i) == f(s.charAt(i))`) **times out** — content-invariant tractability lives in Z3's
*array* theory, not its seq theory — so that's deferred to slice 2.

The only engine change is a **char-cast fold**: Groovy has no primitive char literal, so `('a' as char)` /
`(char)'a'` is the idiomatic way to write a code point, but the cast handler treated casts as transparent
and translated `'a'` as a one-character Seq term, so `s.charAt(i) >= ('a' as char)` mixed an Int with a Seq
and threw. Fold a char/integral cast of a single-char String (or `Character`) literal to its int code
(reusing the Phase-99b `singleCharCode`). Surfaced because `int`/`char >= String` doesn't even type-check
under `@TypeChecked` (Groovy's `Integer/Character#compareTo` rejects a `String` argument), so the cast is
the *only* type-valid char-literal spelling. The richer `s[i] in 'a'..'z'` range form needs string-subscript
bounds + invariant-fragment support and is a follow-on, not this slice.

**Shipped tests (Phase 105, group `P105 string-seq`)**: an `allLower` loop proves every char is in
`['a'..'z']`; tightening the claim to `['b'..'z']` refutes; a per-char `∀` precondition instantiates at a
constant index; an unconstrained position refutes.

**Slice 2 spike result (`nth`-of-concat lemma — negative, informs the path).** Before committing slice 2
(`ChangeCase`-style string *construction*), spiked whether a verifier-supplied `nth`-of-concat lemma
(prefix `0≤i<len(a) ⟹ nth(a++b,i)==nth(a,i)` + suffix, triggered on `nth(a++b,i)`, Phase-91b shape) lets the
construction-*content* invariant discharge. It does **not** — the `pad`-content loop still times out on
preservation *with* the lemma and even at a 30s solver budget, so it's logically stuck, not slow. A
*non-inductive* concat-at-point fact (`(s++"x").charAt(len(s))=='x'`) proves natively, lemma or not — so Z3's
seq theory handles flat concat-content fine; what it can't close is the **quantifier-on-quantifier
induction** (re-establishing `∀i<j+1` content from `∀i<j` across the concat step). That is exactly the shape
the **array** theory *does* carry (Act 5's matrix fill). **Conclusion: slice 2 should model the built string
as a char-code `Array Int Int` (build via `store`), not Z3 `str.++`** — routing content invariants onto the
array theory that already works, at the cost of char handling (literals via the Phase-105 cast fold;
`(char)(c-32)` narrowing). The native-concat-plus-lemma path is a dead end and was not productionised.

---

## Phase 106 — `ChangeCase` via the array theory (string-sequence, slice 2)  *(shipped — no engine change)*

The slice-1 spike's prescription, realised: model the char buffer as a **`char[]`** — an Int-element array,
since `char` is `isIntLikeType` — and OpenJML's `ChangeCase` falls out of the existing array-store +
quantified-loop-invariant machinery (the same that carries Act 5's matrix fill), with **no new engine code**
beyond Phase 105's char-cast fold. The functional form (read `a`, build a new `r`) needs no `old`, so the
full element-wise postcondition `result[i] == (a[i] ∈ ['a'..'z'] ? (char)(a[i]-32) : a[i])` proves directly.
This confirms the spike conclusion empirically: content invariants live in Z3's array theory, not its seq
theory — same proof shape, opposite tractability.

The developer-facing spelling has two char idioms: the literal `('X' as char)` (Phase 105 folds it to a code
point), and char arithmetic `(char)((int) a[i] - 32)` — the `(int)` is needed because `char[]` subscript
arithmetic boxes to `Number`, which `@TypeChecked` won't narrow back to `char` without it. The Encoder
already translates both transparently (the cast handler folds a single-char-literal cast and is otherwise
transparent, so `(char)(intExpr)` stays Int — faithful while the value is in range, the documented
`char`-narrowing caveat for out-of-range arithmetic).

**Shipped tests (Phase 106, group `P106 char-seq`)**: a `fillX` fill proves every element is `'X'` (wrong-char
claim refutes); the functional `upper` proves the full element-wise ChangeCase spec (dropping the lowercase
guard from the spec refutes).

**Adjacent gaps surfaced, not in this slice** (each a clean follow-on, none blocking ChangeCase): a **void**
method carrying a loop skips ("no return value after loop") — return the array instead; **`old` on a param
array** is undeclared (only `this.`-field arrays snapshot), so in-place + `old`-relative specs need the
functional form for now.

---

## Phase 107 — ring buffer: a verified mutable data structure (class `@Invariant`)  *(shipped — no engine change)*

A bounded (non-wrapping) queue as a ring buffer — after Leino's Dafny tutorial, the Toccata/Why3
`ring_buffer` example — chosen to exercise **OO contract verification on mutable object state** rather than a
standalone algorithm. State: an array field `data` + head `m` + tail `n`. The type invariant
(`0 < data.length ∧ 0 ≤ m ≤ n ≤ data.length`) is a class `@Invariant`, and the spike confirmed the engine
both **assumes it on entry** (so `size() == n - m` proves `≥ 0`) and **checks it is preserved on exit** of
every method (an unguarded `bump()` that breaks `n ≤ data.length` refutes with "Cannot prove class
invariant"). `enqueue`/`dequeue` are specified directly over the array region with `old`-relative framing —
`enqueue` ensures `n == old.n + 1 ∧ data[old.n] == x ∧ ∀i<old.n. data[i] == old.data[i]`, and an over-strong
frame (claiming the *written* slot is unchanged) refutes.

**No new engine code** — it composes existing pieces that hadn't been combined into a data-structure proof:
object array-field + scalar/array `old` framing (Phase 11/13), and class-`@Invariant` assume-and-preserve
(Phase 45). Why3's **ghost `seq contents`** abstraction is *dropped* — we have no model fields (the same gap
as OpenJML `Clock`) — so the queue is specified over the concrete array region instead. This is the engine's
first verified *mutable data structure*, and it's squarely the shape groovy-contracts users actually write.

**Why the sibling Toccata/OpenJML examples stay out** (assessed, not ported): `TreeMax` needs a recursive
tree datatype + graph-reachability `mem` + structural-size termination — the object-graph
[non-goal](#non-goals); `balance` turns on a ghost weighing-*budget* (effectful counter through recursion)
and a no-cheating encapsulation property — ghost-effects / information-flow, not functional contracts;
`Clock` is about JML **model fields** themselves, which have no analogue here. `Duplets` (int array + tuples
+ an existential precondition driving a nested-loop witness search) is pure-value and in-kind tractable but a
genuine stretch — a candidate future slice, not done.

**Shipped tests (Phase 107, group `P107 ring-buffer`)**: `enqueue` (write + frame + invariant) and `dequeue`
(head + advance) verify; `size() ≥ 0` proves from the assumed invariant; an over-strong frame and an
invariant-breaking mutator both refute.

---

## Phase 108 — content-dependent array index bounds inside loops  *(shipped — bounds-discharge fix)*

A *data-dependent* index — `b[a[k]]`, where the index `a[k]` is itself an array read — is bounded not by
index arithmetic but by a **value-range quantifier** (`∀q. 0 ≤ a[q] < b.length`). The Phase-91b optimization
*stripped* all quantifier conjuncts from the assumptions when discharging an array-index bound (sound, and it
keeps Z3 out of the quantifier+NIA path for flat-index `a[i*m+j]` fills) — but that discarded the *one* fact
that bounds a content-dependent index, so gather/scatter/histogram loops failed in-loop while the identical
obligation discharged fine *outside* a loop (different code path, no strip). Fix: strip only when the index is
pure arithmetic — keep the quantifiers when the index AST contains a nested subscript (`indexReadsArrayContent`).
Surgical: arithmetic indices are unchanged (the flat-index NIA cases still strip), content-dependent indices
newly keep the value-range. **22-line `VerifyChecker` change.**

**Shipped tests (Phase 108, group `P108 content-index`)**: a gather read `b[a[k]]` and a histogram store
`count[a[k]] = count[a[k]] + 1` (content-dependent *write* index) verify in a loop; dropping the value-range
refutes with an out-of-bounds counterexample.

**Provenance — "try Duplets" (FoVeOOS'11 Challenge 3), assessed, *not* landed.** The example (find two
distinct duplicate pairs) drove this fix but is **not** itself in reach. Its natural nested-loop form is
blocked by the Phase-91 limit (an inner loop with an early `return`). A single-loop reformulation — track each
value's first-occurrence index in a `pos` array (values are in `[0,n)`) — got *past* the content-index bound
(this phase), then hit a **third** gap: an early-exit `return Tuple.tuple(pos[a[k]]-1, k)` reports
"early-exit postcondition outside fragment" (the in-body return building a tuple from content-indexed values).
And even past that, the *full* spec needs totality (a pigeonhole argument that a duplet exists) plus the
two-pass "second duplet has a different value" with the nullable `except` exclusion. The durable win of *this*
phase is the general content-index capability, which stands on its own (counting sort, histograms,
permutation-apply, gather/scatter). The two further gaps — **nested-loop inner `return`** and an
**early-exit postcondition over a tuple** — were closed in Phases 109 and 110, and the full Duplets challenge
(totality + two-pass) lands across Phases 111–113.

---

## Phase 109 — nested loop with an inner early `return`  *(shipped)*

Closes the first of the two Duplets follow-on gaps. Phase 91 summarises a nested inner loop for the outer
loop's VCs — havoc the variables it writes, then assume `inner_inv ∧ ¬inner_guard` — but `innerFrame` (the
write-set analysis) **bailed** the moment the inner body held a `return`, so the whole loop skipped loudly.
Two-part fix:

- **Write-set** (`LoopEncoder.innerFrame`): a `return` writes nothing to *outer* state — it transfers control
  out of the method. The only path on which the outer loop continues past the inner loop is the one where the
  inner loop completed *without* returning, so the summary is unaffected. Treat `return` as a no-op there.
- **Inner-exit postcondition** (`verifyNestedLoops`): the inner `return` is a real exit path whose `@Ensures`
  must be checked, or the fix would be unsound. Collect the inner loop's early exits (`partitionEarlyExits`)
  and discharge each with the inner loop's body-entry context (`inner_inv ∧ inner_guard`) — the *same*
  Phase-49b in-body early-exit treatment, applied to the inner site. Sound because `inner_inv` is established
  and preserved (proved just above), so it holds whenever the inner exit fires.

So a **2D witness search** that returns an index from the inner loop now verifies. The inner loop's own
preservation/progress already tolerated in-body returns (`symExecBodyWithExits` re-detects them); the gap was
only the outer summary's write-set bail and the missing exit-`@Ensures` check. **~10-line change** across the
two files; existing return-free nested loops (matrix fill, `count = n*n`) are untouched.

**Shipped tests (Phase 109, group `P109 nested-return`)**: a `firstDup` nested search returns a witness index
and verifies; a deliberately-false postcondition on the inner-return path (`result <= 0`, but the return
yields `j ≥ 1`) refutes — confirming the inner exit's `@Ensures` is genuinely checked, not skipped.

This still leaves the *second* Duplets gap — an **early-exit postcondition over a tuple** (the nested duplet
returns a `Tuple2` of two indices; `checkEarlyExit` binds a scalar `result`, not the factory slots
`result.v1`/`.v2`). So the natural nested duplet needs that follow-on too; this phase handles the scalar-return
witness-search shape, which is the common case.

---

## Phase 110 — tuple return on an early-exit path  *(shipped — lands the natural nested Duplets `duplet`)*

Closes the *second* Duplets follow-on. `checkEarlyExit` bound only a scalar `result` (`enc.bind('result',
translate(ex.result))`), so an early `return Tuple.tuple(i, j)` couldn't resolve its slot accessors
`result.v1`/`.v2` in the `@Ensures` — it reported "early-exit postcondition outside fragment". Fix: make the
early-exit binding **factory-aware**, reusing the exact `tryRecordFactoryAssign` / `tryRecordSetBinopAssign`
path `checkUse` already runs on the natural after-loop return — so a tuple / list-literal / map-literal return
on a prefix, in-body, or inner-loop exit records its slots (`result.v1`, `result.size()`, `result[k]` all
fold). **One-block change** in `checkEarlyExitPath`.

Combined with Phase 109 (nested inner `return`), this **lands the natural nested form of FoVeOOS *Duplets*
`duplet`** at *partial correctness*: a doubly-nested scan that returns `Tuple.tuple(i, j)` on `a[i] == a[j]`,
proving `result.v1 == -1 ∨ (0 ≤ result.v1 < result.v2 < a.length ∧ a[result.v1] == a[result.v2])` — the
witness-search shape the example exists to teach, in the spelling a developer would actually write.

**Shipped tests (Phase 110, group `P110 tuple-exit`)**: the nested `duplet` (tuple, content-indexed spec)
verifies; a wrong slot-order claim (`v1 > v2`) refutes (proving the slots are genuinely bound, not free); a
single-loop tuple early-exit verifies too (the fix isn't nested-specific).

**Duplets, end to end.** The four-phase arc (105 cast-fold motivation aside) — Phase 108 content-index bounds,
Phase 109 nested inner `return`, Phase 110 tuple early-exit — takes the example from *three* fragment gaps to
**`duplet` partial correctness proven in its natural nested form**. Totality follows in Phase 111.

---

## Phase 111 — Duplets totality (find-given-exists)  *(shipped — no engine change)*

Strengthens the Phase-110 partial-correctness `duplet` to **totality**: a *sentinel-free* postcondition
(`0 ≤ result.v1 < result.v2 < a.length ∧ a[result.v1] == a[result.v2]`) under an *existential* precondition
(`∃p,q. 0≤p<q<a.length ∧ a[p]==a[q]`, written `(0..<n).any { p -> (p+1..<n).any { q -> a[p]==a[q] } }`). The
verifier must now prove the search *returns a real duplet* — i.e. the sentinel fall-through is **infeasible**.
That rests on:

- nested **∀∀ "no-duplet-found-yet"** loop invariants — outer `∀p<i. ∀q∈(p,n). a[p]≠a[q]`, inner adds the
  current row `∀q∈(i,j). a[i]≠a[q]`. The outer invariant's preservation needs the inner loop's completion fact
  (`∀q>i. a[i]≠a[q]`, from the nested-loop summary `inner_inv ∧ ¬inner_guard`) to extend `p<i` to `p<i+1`;
- at loop exit (`i == a.length`) the outer invariant says **no duplet anywhere**, which contradicts the
  existential precondition — Z3 instantiates the universal at the existential's Skolem witness, so the use
  path is UNSAT and the sentinel return is vacuously fine (unreachable).

**No new engine code** — it rides the existing quantifier + nested-loop machinery once Phases 108–110 made the
duplet expressible; the nested `Forall.range`-in-`Forall.range` invariants and the existential `any`-in-`any`
precondition both translate and discharge as-is.

**Shipped tests (Phase 111, group `P111 Duplets-totality`)**: the totality `duplet` verifies; a **non-vacuity
control** that drops the existential precondition **refutes** (the no-duplet fall-through becomes reachable and
violates the sentinel-free postcondition) — proving the existential is load-bearing, not decoration.

**So `duplet` is now fully verified** — partial correctness *and* totality, in its natural nested form. What
remains for the *full* two-pair `duplets` is the two-pass "second duplet has a *different value*" — see
Phase 112.

---

## Phase 112 — Duplets: `dupletExcept` (exclusion-totality), and the inter-procedural-tuple boundary  *(partial — component shipped)*

The two-pass full `duplets` finds *two* duplicate pairs with **different values** by finding one duplet, then
finding another whose value differs from the first. Splitting it into `duplet(a)` (Phase 111) and
`dupletExcept(a, except)` sidesteps the nullable-`Integer` `except` (a plain `int` exclusion instead of
`null`-means-none).

**Shipped:** `dupletExcept` — the **second-pass search engine** — verifies at totality. It's Phase 111 plus an
`a[i] != except` conjunct threaded through the existential precondition, the nested ∀∀ "no *qualifying* duplet
found yet" invariant, and the exit guard. No engine change. (`P112 dupletExcept`: the totality search verifies;
the existential-dropped non-vacuity control refutes.)

**Deferred to Phase 113 — the composition `duplets`:** combining the two passes needs **inter-procedural tuple
results** (binding a local to a tuple-returning call, then using its slots), out of fragment at this point —
a tuple-typed local was minted with a *scalar* `int` handle, so the callee's slot-shaped `@Ensures` couldn't
bind and the body couldn't resolve `r.v1`. Being a multi-part, soundness-sensitive feature, it was taken as
its own slice (Phase 113) rather than half-implemented here. The one non-trivial *proof* step — discharging
the second call's existential precondition (a duplet with value ≠ the first exists) from the two-distinct-
duplets precondition — was sketched and proved tractable; the binding, not the reasoning, was the gate.

**Status:** `duplet` (both directions) + `dupletExcept` shipped here; full `duplets` lands in Phase 113.

---

## Phase 113 — inter-procedural tuple results (and the full two-pass `duplets`)  *(shipped)*

Closes the Phase-112 blocker, so the **full FoVeOOS Duplets challenge verifies**. The gap: binding a local to a
tuple-returning call — `Tuple2 r = duplet(a)` — and using its slots (`r.v1`) as an array index, a call
argument, and the return composition. Four touch points:

- **Type registry** (`collectTupleTypes` → `currentTupleTypes`): tuple-typed locals weren't tracked
  (`Tuple2` isn't `isNonIntScalar`), so the assignment fell through to the scalar-handle path.
- **Binding** (`assumeCalleeEnsures` gains `resultTupleName`): instead of binding `result` to a scalar term,
  register the local as a tuple (reusing the Phase-80 param-tuple machinery — `r.vN` → entity `r$vN`) and
  rename `result`→`r` in the callee's `@Ensures` (a fresh AST copy via `renameVariable`), so its slot
  constraints land on the local's slots.
- **All contexts** (`mkEncoder` merges `currentTupleTypes` into the tuple registry): `r.vN` must *translate*
  in every verification context — the body VC, an array-bounds check, a call-precondition discharge — each of
  which builds its own encoder.
- **Obligation replay** (`dischargeVfObligation`): the value-flow replay of `r = callee(...)` now asserts the
  callee's `@Ensures` too, so a downstream `a[r.vN]` bound (and the next call's precondition) sees the slot's
  range — without it `r$vN` was unconstrained and the bound refuted with `r$v1 = -1`.

With these, `duplets` composes `duplet(a)` then `dupletExcept(a, a[r1.v1])` and returns a `Tuple4` of the four
indices, proving the two pairs have **different values**. The cross-call reasoning Z3 needed — the second
call's existential precondition (a duplet with value ≠ the first) follows from the two-distinct-duplets
precondition — discharged as sketched (instantiate the negated goal at the precondition's two witnesses; one
must differ from the first value). Sound by construction: assuming a callee's `@Ensures` is the existing
Phase-7 inter-procedural rule (the callee's `@Requires` is discharged separately at the call site); the tuple
path only changes *how* `result` binds, not *that* the contract is the obligation.

**Broadly useful, not Duplets-specific** — any method returning a `TupleN` with a caller using its slots.

**Shipped tests (Phase 113, group `P113 interproc-tuple`)**: a minimal hoisted tuple slot used in the body
verifies; a wrong slot-value claim refutes (the slot is genuinely bound to the callee's value); the **full
two-pass `duplets`** composition verifies. **So the complete Duplets challenge — `duplet` (partial + total),
`dupletExcept`, and `duplets` — is fully verified.**

---

## Phase 114 — Groovy records  *(shipped — no engine change; capability confirmed + locked in)*

A Groovy `record` is a class with `final` component fields, so the Phase-45 object-field machinery already
handles it: a record parameter's components read in contracts and bodies (`p.x`), and a record may carry its
own `@Requires`/`@Ensures` over its components. No record-specific support was ever added — it falls out of the
class handling — but it was **untested**, so this phase adds a permanent group to confirm it's genuine and
guard against regression.

**Shipped tests (Phase 114, group `P114 records`)**: a record-param component read proves (wrong-component
claim refutes); a record with its own contract method (`Box(int lo, int hi).width()`) proves `result >= 0`
(strict `> 0` refutes, since `lo == hi` gives width 0). Record-specific surface — compact/canonical
constructors, deconstruction/pattern matching, generated `equals`/`toString` — is not exercised.

---

## Phase 115 — lock AST transforms & the monitor invariant  *(shipped — no engine change)*

The first concurrency-adjacent slice. Groovy's lock AST transforms — `@WithReadLock` / `@WithWriteLock` /
`@Synchronized` — turn out to be **transparent** to the verifier: `ContractExpansionTransform` snapshots the
clean body at `CONVERSION` (before the locks weave their wrapper in at `CANONICALIZATION`), so the method's
contract verifies through the lock as if it weren't there (confirmed: `@WithWriteLock`/`@Synchronized` mutators
verify their `@Ensures` + the class `@Invariant`; a wrong `@Ensures` still refutes, so the body is genuinely
modelled, not skipped). No engine change needed — the slice is the framing + tests.

That makes the class `@Invariant` a **lock/monitor invariant**: each critical section is verified to preserve
it — exactly Chalice/Viper's "acquire inhales the invariant, release exhales it", but sequential. **Honest
boundary:** we prove the per-critical-section obligation (the sequential half of a monitor proof); mutual
exclusion, race-freedom, deadlock-freedom are **not** proven — those need concurrent separation logic with
fractional permissions (Verus / Viper / VerCors), out of scope for an SMT sequential checker. So it's a
monitor-invariant proof, not a from-scratch thread-safety proof.

**Shipped tests (Phase 115, group `P115 monitor-invariant`)**: a lock-guarded `Account` (`@WithWriteLock`
deposit/withdraw, `@WithReadLock` read) proves it never overdraws (`balance >= 0`); a `@Synchronized` latch
proves `count >= 0`; dropping the `amount <= balance` guard from `withdraw` refutes (`Cannot prove class
invariant` — the critical section that breaks the lock invariant is caught); a wrong `@Ensures` refutes through
the lock (non-vacuity — the body is modelled).

**Upstream bug found and fixed (GROOVY-12084):** a `@Synchronized` method carrying `@Ensures`/`@Invariant` but
no `@Requires` crashed groovy-contracts (`SynchronizedStatement cannot be cast to BlockStatement` — the
contract-injection rewrite assumed a `BlockStatement` body; the `@Requires` path block-wraps first, which is
why it only bit without one). Fixed upstream and confirmed against refreshed deps; `P115` now includes a
regression guard (a `@Synchronized` mutator with no `@Requires` verifies), and the earlier precondition
work-around is no longer needed.

---

## Phase 116 — monoids/semigroups: checked *and* proven (equational combiner inlining)  *(shipped — engine change)*

Composes with Groovy 6's `groovy.typecheckers.CombinerChecker` (which checks a combiner's *shape* — that the
operation handed to `injectParallel`/`sumParallel` is associative, trusting the `@Associative`/`@Reducer`
annotation for a method reference and scanning for a non-associative operator in an inline closure) on **one
real `@TypeChecked(extensions = ['groovy.typecheckers.CombinerChecker', 'verification.VerifyChecker'])`**:
CombinerChecker checks the shape at the call site, groovy-verify proves the **semantics** — the combiner's
defining equation, the monoid laws, and that the sequential reduction *gives the right answer*. Most of this
already worked (a combiner's `@Ensures` proves; the associativity/identity laws prove; a *non*-associative
combiner like subtraction **refutes** its associativity law — the exact bug CombinerChecker forbids). The one
gap was the reduction *calling the combiner method*: `acc = Sum.add(acc, xs[i])` translated to nothing (a
cross-method call isn't a value), so `acc` was havoced and the `sum`/extremum aggregation pattern couldn't
fire — the loop timed out (sum) or lost its existential witness (max).

**Engine change — equational combiner inlining.** A same-unit method `f(a, b)` with **no `@Requires`** and an
`@Ensures({ result == E(a, b) })` is registered as a combiner; a call `f(x, y)` is then translated as
`E[a:=x, b:=y]` (the `@Ensures` right-hand side with formals bound to the actual argument terms). So
`acc = Sum.add(acc, xs[i])` becomes `acc + xs[i]`, `acc = Largest.max(acc, a[i])` becomes the ternary — and
the existing inline aggregation/extremum recognition fires. **Sound:** the combiner's `@Ensures` is verified
when the combiner is checked, and there's no `@Requires` to discharge. Restricted to a pure `E` (only the
formals, no calls / `old` / `result` / captured fields). ~90 lines (`Encoder` registry + `inlineCombiner`,
`VerifyChecker.collectCombiners`).

The honest boundary: the *parallel* recombination equalling the sequential fold is `injectParallel`'s own
contract (it requires an associative combiner — checked by CombinerChecker, proven here); we verify the
combiner is a correct monoid and the sequential reduction is right, which is what makes the parallel answer
right — the same "prove the local obligation, rely on the library's structural guarantee" shape as the
monitor invariant (Phase 115).

**Shipped tests (Phase 116, group `P116 monoid`)** — all under both checkers in one `@TypeChecked`: a full
`Sum` monoid (`@Reducer(zero='0') add`'s equation + identity + associativity + `reduce == xs.sum()` *via the
combiner*, with an `injectParallel(0, Sum.&add)` call site CombinerChecker certifies) and a `Largest` semigroup
(`@Associative max` + associativity + `reduce == a.max()` via the combiner, with a `sumParallel(Largest.&max)`
site) verify. CombinerChecker's channel is exercised three ways — a non-associative *inline* combiner
`injectParallel(0) { a, b -> a - b }`, and a seed contradicting the declared identity (`injectParallel(5,
Sum.&add)` vs `@Reducer(zero='0')`) — while a *falsely* `@Associative` `Minus.sub` is trusted by CombinerChecker
but groovy-verify **refutes** its associativity law, catching the bad annotation the shape checker cannot.
(`@Reducer(zero)` validates the seed but doesn't shorten the call — there is no seedless `injectParallel`.)

---

## Phase 117 — agents/actors: the monitor invariant via serialization  *(shipped — no engine change)*

Generalises the Phase-115 lock insight across concurrency *paradigms*. The lock trick is really "prove the
local obligation, assume the structural guarantee" — and an `Agent`/`Actor` is a monitor whose mutual exclusion
comes from processing **one message at a time** rather than from a lock. So the class `@Invariant` is again the
monitor invariant, each handler verified to preserve it, with **no lock annotation** — only the *assumed*
structural guarantee changes (mutual exclusion → serialization). No engine change: it's the existing
class-invariant machinery (Phase 45/107/115) plus the framing.

**Shipped tests (Phase 117, group `P117 agent-invariant`)**: a bounded `Buffer` (`@Invariant({ 0 ≤ count ≤
capacity })`, contracted `add`/`remove`, no lock) verifies its occupancy invariant; an unguarded `add`
refutes; and the Agent update-function model (`agent.send { inc(it) }`, a pure `state → state` update) proves
its update preserves the invariant. The honest boundary mirrors locks: we prove each handler maintains the
invariant; we *assume* the runtime serializes them (we don't verify the serialization itself).

This is the safety-invariant flavor under message passing. The other concurrency flavors followed in
Phases 118–119: **dataflow** (single-assignment ⟹ a determinacy/value proof, light modeling of
`DataflowVariable`/`<<`/`await`/`async`) and **channels** (FIFO delivery ⟹ a per-element transform proof, the
combiner trick).

---

## Phase 118 — dataflow: the determinacy half via single-assignment  *(shipped — light AST desugaring)*

The third concurrency flavor, and a different *assumed* guarantee. Locks assume mutual exclusion, agents/actors
assume serialization; a **dataflow** network assumes **single-assignment** — every `DataflowVariable` is bound
exactly once and a read blocks until that bind, so the network's *value* is independent of the schedule. We
prove the functional value (the determinacy half) and assume the single-assignment structure (we do **not**
prove deadlock-freedom or termination).

Engine change is a small source-level desugaring (`desugarDataflow` in `VerifyChecker`, applied in
`afterVisitMethod` and stashed via `putNodeMetaData(ORIGINAL_BODY_KEY, …)`): the network collapses into
straight-line **SSA**. `new DataflowVariable()` drops to a scalar decl, `x << v` becomes the single binding
`x = v`, `x.get()`/`await(x)` become `x`, and `async {}` blocks flatten inline — sound *because*
single-assignment makes ordering irrelevant. The SSA body then proves on the existing sequential machinery.

The one subtlety that cost a debugging pass: `rewriteDfExpr` must apply its `ExpressionTransformer` to the
**root** expression (`t.transform(e)`), not via `e.transformExpression(t)` — the latter only transforms the
*children*, so a top-level `return z.get()` slips through unrewritten while a nested `x.get()` inside a larger
expression gets caught. (`.val` is dropped: it's a dynamic-only property that stock STC rejects, so it's never
a valid typed program to model.)

**Shipped tests (Phase 118, group `P118 dataflow`)**: a three-variable network proving `result == a + b`, a
wrong claim (`result == a`) refuted with a counterexample, and a two-variable product.

---

## Phase 119 — channels: the per-element transform via FIFO  *(shipped — light AST desugaring)*

The fourth and final concurrency flavor, and the combiner trick (Phase 116) carried into streaming pipelines.
An `AsyncChannel`'s structural guarantee is **FIFO delivery**: the i-th value received is the i-th sent, run
through the pipeline's pure stages — so for a representative element the whole pipeline collapses to *function
composition*. We prove that per-element transform and assume FIFO ordering (we do **not** prove delivery or
termination).

Engine change is a second source-level desugaring (`desugarChannels` in `VerifyChecker`, applied in
`afterVisitMethod` alongside Phase 118's dataflow pass): `def src = AsyncChannel.create(n)` drops to a scalar,
`src.send(x)` is the single binding `src = x`, each `map { f }` stage **β-reduces** `f` over its upstream value,
`first()` is a read, and `close()` drops. The key wrinkle versus dataflow: a pipeline is *declared* before its
producer runs (`def out = src.map {…}; async { src.send(x) }`), so pipeline-derived vars are resolved **lazily**
— `def out = …` records the pipeline rather than reducing it eagerly, and the composition is expanded at the
`first()` receive site, by which point the flattened `src = x` has executed. (`map` closures are β-reduced via
an `ExpressionTransformer` substituting the closure parameter — explicit or implicit `it` — with the upstream
value; chained `.map` reduces inside-out because the object-expression is reduced first.) `filter` is out of
slice: modeling it as identity would be unsound, so channel examples stay `map`-only.

**Shipped tests (Phase 119, group `P119 channels`)**: a two-stage `map` pipeline proving `result == (x+1)*2`
(producer in a trailing `async {}`, exercising the lazy resolution), a wrong claim (`result == x+1`) refuted
with a counterexample, and a single-stage producer-first variant proving `result == x*3`. README "Channels"
subsection added — and the four concurrency examples (locks, agents/actors, dataflow, channels) are now grouped
under a new **Concurrency "lite" Examples** section, framed by a structural-guarantee/local-obligation table.

This completes the concurrency arc: locks → mutual exclusion, agents/actors → serialization, dataflow →
single-assignment, channels → FIFO delivery. In every case the *local* obligation is sequential and provable;
only the *assumed* structural half changes.

---

## Phase 120 — behavioral subtyping (Liskov substitution)  *(shipped — a new *kind* of proof)*

The first check that relates *two contracts* rather than verifying one against a body. When a method overrides a
contracted parent method and **redeclares** its own contract, the engine proves the override is substitutable:
the precondition must be **weakened** (`pre_parent ⟹ pre_child` — the child accepts every call the parent did)
and the postcondition **strengthened** (`(pre_parent ∧ post_child) ⟹ post_parent` — the child promises at least
as much). Both are pure SMT implication checks over a shared parameter/result namespace (the parent's contract
is re-aligned to the child's formal names by position), run in `afterVisitMethod` with no body involved; a
satisfiable negation is a concrete substitutability counterexample.

~110 lines (`verifyBehavioralSubtyping` / `overriddenSuperMethod` / `alignParentParams` / `checkLspImplication`
in `VerifyChecker`, `Reporter.formatLspViolation`). Fires only when the child *redeclares* a clause — an omitted
one is inherited verbatim, hence trivially compatible. Skips silently if either contract falls outside the
encoder fragment (can't judge soundly). **Shipped tests (group `P-lsp`)**: a strengthened precondition (`x >= 10`
over `x >= 0`) refutes with witness `f(0)`; a precondition *added* over an unconstrained parent refutes; a
weakened postcondition (`result >= 0` over `result >= 5`) refutes; weakening the precondition and strengthening
the postcondition both verify clean.

The remaining override slice (not pursued here): an **uncontracted** override is still not re-verified against
the inherited contract — groovy-verify checks a method only against the clause it declares.

---

## Phase 121 — traits  *(shipped — interface-walk + machinery skip)*

Traits work along the `implements` axis, mirroring inheritance one axis over. Two changes:

1. **Trait class `@Invariant` enforced on implementers.** `walkClassInvariants` now walks `interfaces` (a trait
   is an interface), so a trait's `@Invariant` is conjoined into every implementing class's effective invariant
   and proved at each of its own methods' exits. A trait property is woven onto the implementer as a field, so
   an implementing method that breaks the trait invariant refutes — and a method gets full functional
   verification over the woven trait field. (Dedupe by source text guards the diamond case; the internal
   `<Trait>__<field>` backing name is suppressed from counterexamples in favour of the source-named property.)

2. **Trait machinery skipped quietly.** A trait's *default* method is woven — after the CONVERSION clean-body
   snapshot — into a synthetic static helper on a `…$Trait$Helper` class (a `$self` receiver) plus a delegating
   bridge on each implementer. Before this slice those leaked a phantom `$self != null` obligation and a
   `try/catch`-body "skipped" *error*, so **any** contracted trait failed to compile under the extension.
   `isTraitMachineryMethod` now recognises and skips them (`$Trait$Helper` owner, `$self` first param, or a
   synthetic bridge whose source is a trait), so trait code compiles cleanly.

**Shipped tests (group `P-trait`)**: a trait `@Invariant` broken by an implementing `dec()` refutes; a guarded
`dec()` preserves it; an implementing method proves a functional `@Ensures` over the trait field.

---

## Phase 122 — trait default-method verification  *(shipped — pre-weave-body recovery)*

Closes the Phase-121 boundary: a trait's *concrete default method* is now verified, not just skipped. The blocker
was that the implementing class's woven method delegates to a synthetic helper, and the trait method itself is
abstract by type-check time — but a probe found the CONVERSION snapshot (`ORIGINAL_BODY_KEY`) is still attached
to the trait method node, already in field-accessor form:
`((Counter$Trait$FieldHelper) $self).Counter__count$set( (… $get() == 9) ? 0 : (… $get() + 1) )`.

So in `afterVisitClass(C)`, for each trait `C` implements, each default method with a snapshot is recovered and
**desugared** (`desugarTraitBody`): the woven accessors `((FieldHelper) $self).Trait__field$get()` / `$set(v)`
rewrite back to plain `field` reads / `field = v` writes (dropping the receiver casts and the `Trait__` backing
prefix), yielding exactly the body the same logic would have as a class method. That body is verified through a
synthetic `MethodNode` rooted on `C` — so it sees `C`'s fields and `C`'s effective invariant (which already
includes the trait's, via Phase 121). Two wrinkles found by probe, both fixed: the woven argument list is a bare
`TupleExpression` (not the `ArgumentListExpression` the matchers first assumed), and the synthetic node needs a
source position or its class-invariant refutation is silently swallowed by STC (the Phase-94 dropped-anchor
issue). `~120` lines, no new SMT.

**Shipped tests (group `P-trait`)**: a trait default method's `@Ensures` proves (`nonNeg` ⟹ `result >= 0`) and a
false one refutes; the **wrap-around counter** — a trait owning `count`, a wrapping `inc`, `getCount`, and the
`0..9` invariant, with an implementing class adding a wrapping `dec` — proves both `inc` and `dec` keep the
counter in range; a non-wrapping trait `inc` (`count = count + 1`) refutes at `count == 9` (previously it passed
silently — a real soundness gap closed). The remaining override slice is unchanged: an *uncontracted* override
isn't re-verified against the inherited contract.

---

## Phase 123 — typed local arrays carry their component sort  *(shipped — one-line fix, found via FizzBuzz)*

`collectListElementTypes` registered the element sort of non-Int **parameter** and **field** arrays (so a
`String[]` param's stores/reads use the String sort), but its body scan for typed **locals** only handled `List`
declarations — not arrays. So `String[] a = new String[n]` defaulted to an Int-element array, and a String store
`a[0] = "x"` crashed Z3 with *"domain sort String and parameter sort Int do not match"*. The local-declaration
scan now handles `t.isArray()` the same way params/fields already did. Surfaced building a Dafny-style
element-wise array-fill (FizzBuzz): an `int[]` version already verified, but the String-valued one hit this.

**Shipped tests (group `P-fizzbuzz`)**: the FizzBuzz array-fill (a pure `spec(n)` function, an imperative loop
filling `r[i] = spec(i + 1)`, postconditions `result.length == upTo` and `∀k. result[k] == spec(k + 1)`, and a
`@Decreases`) proves over a `String[]`; the off-by-one `spec(i + 2)` refutes (Dafny's "if you wrote i+2 it
errors"); a minimal `String[]` local-store regression. The spec uses real **emoji** literals (`🥤`/`🐝`/`🥤🐝`).

**Upstream bug surfaced and fixed — GROOVY-12085.** Astral-plane characters (emoji) in a *contract literal*
initially broke ContractExpansionTransform's capture: power-assert's `SourceText` slices the source line with
`String.substring` (UTF-16 indices) using the AST's column numbers, which are **code-point**-based (ANTLR4
`CodePointCharStream` via `CharStreams.fromReader`; `getCharPositionInLine()` counts code points). A confirmed
probe — `r = (n ? '🥤🐝' : 'z')` parses to `lastColumnNumber == 21` (20 code points + 1) where the UTF-16 end is
23, so the slice dropped the trailing `')` and the contract failed to reparse. Not a groovy-verify bug; fixed in
core Groovy (`SourceText` now maps code-point columns to char offsets) and confirmed by `--refresh-dependencies`.

---

## Phase 124 — `int → String` conversions in the spec (the FizzBuzz *number* default)  *(shipped)*

To output the number for non-spec/buzz slots, the spec's default branch must convert `int → String`. `String.-
valueOf(int)` and `Integer.toString(int)` (static) already lowered to Z3's `str.from_int` (Phase 47e), but two
gaps blocked the idiomatic full example, both found by probe:

1. **Combiner inlining rejected the conversion.** `isPureOver` (the gate deciding whether a helper's
   `@Ensures({ result == E })` registers as an equational combiner) failed on *any* method call — so a `spec`
   whose `E` contained `String.valueOf(n)` never registered, so `spec(k + 1)` never inlined into the loop
   invariant (`tr` → null → "invariant outside fragment"). The identical ITE written inline verified, isolating
   the combiner path. Fix: `isPureOver` now allows the recognised deterministic conversions
   (`String.valueOf(x)` / `Integer.toString(x)` / `x.toString()`, checking only the converted value is pure).
2. **`n.toString()` (instance form) wasn't modeled, and spuriously NPE'd.** The encoder only handled the static
   `Integer.toString(n)`; the idiomatic `n.toString()` (0-arg, int receiver) fell through, and the obligation
   collector added a `n != null` deref on the autoboxed primitive — a false positive (an `int` can't be null).
   Fix: the encoder lowers an Int-sorted `x.toString()` via the same `str.from_int` (gated by a new
   `SmtBackend.isInt`), and the deref collector skips a **primitive-typed** receiver entirely.

The proof needs no digit semantics — the conversion just has to be a deterministic `Int → String` function, so
body and spec share one `str.from_int(k + 1)` term and the every-quantifier cancels structurally. **Shipped
tests (group `P-fizzbuzz`)**: the full pretty FizzBuzz with the **number** default (`n.toString()`) proves
length + element-wise + termination; the same via `String.valueOf`; the off-by-one and a *wrong-number*
(`(n+1).toString()`) both refute (the number is checked, not just the emoji); and a bare `n.toString()` proves
with no spurious null obligation. `'' + n` stays out of the fragment (the `+` operator's string/int mixing is a
separate, larger slice).

---

## Phase 125 — render Int array-*element* counterexamples (slice a)  *(shipped — scoped by what's sound)*

A counterexample showed scalars and the failing-call repro but never an array's element value, so an
element-wise refutation left "which slot, holding what?" to the reader. The model **already** pins Int array
elements (`name[k]` keys in `Z3Backend`); `shown()` just suppressed every `]`-ending key. Probing the obvious
"unsuppress everything" found it isn't cleanly valuable — three distinct cases:

- **Parameter / field arrays** — the model value is the actual input/entry state. Rendering it (`xs[1] = 8`
  next to a failed `xs[1] == 7`) is sound and makes the refutation concrete. *Shipped.*
- **Local / loop arrays** — a loop-preservation VC lets Z3 pick an arbitrary *entry* array, so its element
  value is pre-state garbage (`a[0] = 4` for a body that stores `a[0] = 1`). Rendering it would **mislead**, so
  these stay suppressed (`shown()` now gates `name[k]` on the base being a parameter or field).
- **Local *return* arrays** — not pinned in the model walk at all, so nothing to show.

So slice (a) lands the sound, non-misleading part: parameter/field Int element values. **Shipped test (group
`P-arrayelem`)**: a `@Ensures({ xs[1] == 7 })` over an `int[]` param refutes with `xs[0] = 8, xs[1] = 8`.

The case that surfaces the *interesting* value — a local loop array's post-store element at the failing
quantifier index (the FizzBuzz `spec(i + 2)` case) — is slice (b), shipped next.

---

## Phase 126 — surface the offending array element (slice b)  *(shipped — post-store eval + bounded enumeration)*

For an element-wise refutation, name the slot that's wrong and what the spec wanted there:
`r[0] = "2" — the spec requires "1"`. Two design choices sidestep what made this look hard in Phase 125:

- **Post-store handle, not a declared array.** The element value that matters is the array *after* the body's
  stores. Rather than registering a new handle, the surfacing runs *inside* the check method (`checkPreservation`
  / `checkUse` / `checkPath`) right after `s.check()`, where the encoder `enc` still holds the post-body
  bindings — so `enc.arrayFor(arr)` is already the post-store array, and the model is freshly available.
- **Bounded enumeration, not a Skolem witness.** Instead of extracting Z3's internal existential witness `k`,
  enumerate `k ∈ [0, size)` (the array size is pinned in the counterexample, and counterexamples are minimal),
  evaluate the post-store `arr[k]` and the per-element spec `E[p := k]` in the live model, and report the first
  mismatch. No witness extraction needed.

Mechanics: `SmtBackend` retains the SAT model (`lastModel`) and adds `evalDisplay(handle)` (Int → number,
`Seq`/String → quoted text); `CheckResult` gains a `notes` channel that `Reporter.appendModel` prints on its own
lines; `appendOffendingElements` parses each `(range).every { p -> arr[p] == E }` invariant conjunct and fills
the note. Best-effort throughout (any failure leaves the diagnostic unchanged); scoped to the `arr[p] == E`
shape.

A wrinkle the *emoji* surfaced: Z3's `mkString` round-trips a supplementary character as a
`[code-point, low-surrogate]` pair, and `getString()` returns it as literal `\u{…}` escapes — so a wrong
FizzBuzz slot printed `\u{1f964}\u{dd64}…` instead of `🥤🐝`. The verification is sound (the mangling is
identical on both sides of every comparison); only the *display* was wrong. `evalDisplay` now decodes the
escapes and drops the artifact lone surrogates, recovering the real text.

**Shipped tests**: the FizzBuzz value off-by-one (`spec(i + 2)`) asserts `r[0] = "2" — the spec requires "1"`,
and the other-direction `spec(i)` asserts `r[0] = "🥤🐝" — the spec requires "1"` (slot 0 gets `spec(0)`, which
is FizzBuzz — 0 divides everything — exercising the emoji decode); group `P-fizzbuzz`. An `int[]` fill asserts
`a[0] = 1 — the spec requires 0` (group `P-arrayelem`).

---

## Phase 127 — snapshot the index when a store's RHS pre-increments the index var  *(shipped — `a[i] = ++i`)*

A subscript-store whose RHS increments the very variable used in the LHS index — `a[i] = ++i`, or the
`dst[i] = src[++i]` shape — used to skip loudly: the inc/dec hoist refuses to lift `++i` above the statement
because doing so would make the LHS index `a[i]` read the *new* value (the wrong slot), so `++i` is no longer a
safe first occurrence. But Java/Groovy evaluate the LHS index *before* the RHS, so the intended store is
`a[old] = old+1` — perfectly expressible, just not by hoisting.

`expandArrayStoreSnapshot` handles it directly: when the LHS is `arr[idx]`, `idx` itself has no inc/dec, the RHS
*does* increment a var that `idx` reads, it snapshots the index into a fresh `$snapN` local *before* the
increment fires, then rewrites to `[$snapN = idx; arr[$snapN] = value]` and recursively expands the (now safe)
remainder. So `a[i] = ++i` becomes `$snap = i; i = i + 1; a[$snap] = i` — `a[old] = old+1`, matching the
language's left-to-right evaluation. The `$snap` temps are suppressed from counterexample display (`shown()`).

**Shipped tests** (group `P expr inc/dec`): `a[i] = ++i` and `a[i] = i++` both prove their post-state, a wrong
claim about `a[i] = ++i` refutes, and `dst[i] = src[++i]` — which previously skipped — now snapshots and verifies
(`dst[3] == src[4] == 99`). Honest scope note: the *String*-valued analogue `r[i] = spec(++i)` (FizzBuzz with a
combiner-inlined `String` spec) now encodes correctly but the solver times out on the `Seq`/String element
reasoning, so it isn't a passing test; the README's FizzBuzz uses a `0`-based loop to sidestep it.

---

## Phase 128 — string concatenation as an algebraic law (associative, not commutative)  *(shipped — example)*

No new engine code — this exercises the existing `Seq` lowering of `String` `+` to show the verifier reasons
over *arbitrary* strings, not just concrete literals. Two postconditions written purely over parameters (empty
body — the property *is* the spec):

- `@Ensures({ (a + b) + c == a + (b + c) })` **proves** — associativity holds for all strings.
- `@Ensures({ a + b == b + a })` **refutes** — concat isn't commutative; the diagnostic names a minimal witness
  `commutative("A", "B")` (`"AB" ≠ "BA"`).

This is the algebraic counterpart to the FizzBuzz *element-wise* string example: there the obligation is
per-index over an `every`-quantified array; here it's a closed law over uninterpreted-length sequences. A
`boolean`-returning phrasing (body is the comparison, `@Ensures({ result == true })`) verifies identically.
**Shipped tests**: group `P-strcat` (4 cases — both laws × both phrasings); README "String concatenation"
example is the verbatim void/over-params pair.

---

## Phase 129 — route `+` by operand *sort*, not static type (string concat no longer crashes the compile)  *(shipped — graceful degradation)*

A string accumulator folded in a loop (`acc = glue(acc, x)`, or `acc = acc + x`) could throw out of the encoder
and **crash the whole compile** — `ClassCastException: SeqExpr cannot be cast to ArithExpr` from
`Encoder.inlineCombiner → Z3Backend.plus`, or `Z3Exception: Sorts Int and String are incompatible` from `mkEq`.
That violates the project's *loud-unsoundness* tenet: everything outside the fragment must skip with a diagnostic,
never crash.

Root cause: the `String` `+` → `stringConcat` route is gated by the **static** `isStringReceiver`, which inspects
the operand *expressions* and only recognises String literals / String-typed names in `scalarTypes`. A combiner's
defining `a + b` inlined at a fold site (Phase 116) is translated with the formals bound to seq *handles* whose
types are invisible to that static check, so it slipped past and hit the integer `plus`. The same blind spot let a
String-returning call modelled as a generic Int result handle reach `mkEq` against a String.

Fix: decide by the translated operand **sort** (the authoritative signal we already hold), via a new
`SmtBackend.isSeq(handle)`. In `Encoder.translateBinary`, right after both operands are translated:
`+` on two sequences → `stringConcat` (the genuine concat the inline intended); a lone sequence operand against a
non-sequence → return null (**loud skip**). Two sequences under `==`/`!=` still flow to the sort-polymorphic
`eq`/`ne` below (this is how the Phase-128 string laws run, unchanged).

Net effect — string concatenation now **degrades gracefully** instead of crashing: combiner inlining over String
params/locals *proves* in expression/postcondition position; a String-returning combiner call in *return* position
skips loudly (the body-replay's `assumeCalleeEnsures` mints a generic Int result handle for the String-returning
callee, which the sort guard then declines — no crash); and a string fold in a loop refutes/skips cleanly. (Making
the *return*-position and loop-fold cases prove would need a sort-aware `assumeCalleeEnsures` and seq-carrying loop
invariants — the `Seq`-theory-in-loops boundary noted in Phases 124–127, deliberately not chased here.)

**Shipped tests**: group `P-seqconcat` (4 cases — straight-line concat proves, combiner inline in postcondition
proves, return-position combiner call skips loudly, while-loop fold refutes cleanly). Reported by a user
(`groovy-fizzbuzz` repo) who hit the crash building a parallel emoji-FizzBuzz join.

---

## Phase 130 — derive the monoid laws from `@Reducer`/`@Associative` (the annotation proves itself)  *(shipped)*

`@Reducer`/`@Associative` *assert* that a combiner is a monoid/semigroup but check nothing — their own javadoc:
*"this annotation asserts the laws; it [checks nothing]."* Until now the user spelled the laws out as extra lemma
methods (`@Ensures({ op(op(a,b),c) == op(a,op(b,c)) })`, `@Ensures({ op(a,zero) == a … })`) for groovy-verify to
discharge. This phase reads the annotation directly and synthesises those obligations, so the lemmas are no longer
needed — the annotation proves itself. This is the natural other half of the Phase-116/CombinerChecker split:
CombinerChecker trusts the annotation's *shape*, groovy-verify now proves its *semantics*.

`verifyReducerLaws` fires per method in `afterVisitMethod`. For an `@Reducer`/`@Associative` combiner that is the
Phase-116 equational shape (binary `T×T→T`, no `@Requires`, `@Ensures({ result == E })`, `E` pure over the two
formals), it synthesises a void lemma method per law whose `@Ensures` *calls the combiner* —
`op(op(a,b),c) == op(a,op(b,c))` for associativity (both annotations), and `op(a,Z) == a && op(Z,a) == a` for
identity (`@Reducer` with a declared `zero`, parsed from the annotation member) — then runs it through the normal
`before/afterVisitMethod` path (the same trick `verifyTraitDefaultMethods` uses). The Phase-116 inliner unfolds the
`op(...)` calls back to `E`, so each law reduces to the closed goal the user used to write by hand. Proves
silently; refutes with a tailored `Reporter.formatReducerLawFailure` — `Cannot prove @Reducer associativity for
combiner sub` / `… identity …` — anchored on the combiner's real position. Sound: the combiner's own `@Ensures` is
verified where it is declared, and there is no `@Requires` to discharge. When the combiner is non-equational /
impure, the annotation asserts laws we can't model, so it skips *loudly* (a postcondition-skipped diagnostic)
rather than vouching silently.

A latent bug surfaced and was fixed en route: combiner inlining bound a formal to its actual-argument handle via
`translateWith` (which writes `env`), but a **String**/Enum-typed name resolves through `varForOfSort`→`sortedEnv`,
so the binding was silently dropped whenever a combiner formal's name collided with a surrounding String variable
(e.g. inlining `op(a,b)` inside a method that also has a param `a`). `varForOfSort` now honours the `env` binding
first, exactly as the Int-path `varForRaw` already did — fixing the auto-derived identity (whose synthesised params
reuse the formals' names) and any real user code with the same collision.

**Shipped tests**: group `P-reducer` (string-concat monoid and int-sum monoid auto-prove assoc + identity;
`@Associative` on subtraction refutes associativity; a wrong `zero` refutes identity) and a `P-seqconcat`
regression for the colliding-name inline fix. README `CombinerChecker`/`Sum` example updated to drop the
spelled-out `associative` lemma and show the annotation alone carrying the proof.

---

## Phase 131 — prove `@NonNull` returns (nullity value-flow; complementary to NullChecker)  *(shipped — return form)*

The next "annotation asserts, we prove" target after `@Reducer` was `@NonNull` (the NullChecker family). It split
into two forms, and surfaced a real foundational gap.

**Foundation — nullity *value-flow*.** groovy-verify could only ever *assume* non-nullness (a `@Requires({ x !=
null })` discharges a later `x.foo()` NPE obligation); it could not *prove* it, because the nullity oracle
(`Encoder.nullEnv`, a Bool per name) was never tied to a value's provenance. So even `@Ensures({ result != null })`
with `return "hi"` *refuted* — the `result?null` flag was free. Fixed by `Encoder.nullityOfExpr(e)` (the nullity a
value *implies*: `null`/non-null literals, `new`, collection/GString literals, and string concat are statically
known; a bare variable ties to its own oracle) plus `bindNullity`, called at the return binding in `checkPath`. Now
`return "x"` / `return new T()` / `return x + y` / `return x` (for a `@Requires`-non-null `x`) all establish
non-nullness; an unconstrained `return x` refutes with `fails on: foo(null)`.

**Return form (shipped).** A `@NonNull` (reference) return is conjoined an implicit `result != null` postcondition
in `verifyPostcondition` (`hasNonNullReturn`), riding the normal machinery. Proves silently; refutes with the
counterexample. Genuinely complementary to NullChecker, which is *flow*-level: it stays silent on a returned
nullable param that groovy-verify's *value*-level reasoning refutes.

**Double-reporting — a non-issue (no coordination code).** Tested both checkers together: they partition cleanly.
On a nullable-param return NullChecker is silent and only groovy-verify fires; on an explicit `return null`
NullChecker reports "Cannot return null from @NonNull method" and groovy-verify *skips* (`return null` is outside
its fragment). No overlap, so the "coordinate reporting" worry needed nothing.

**Field form (deferred to Phase 132).** A `@NonNull` *field* → invariant `field != null` was prototyped but
**reverted here**: it rested on a separate pre-existing gap — constructor/method field-writes propagated an int
*value* to the field oracle but not *nullity*, so even an *explicit* `@Invariant({ name != null })` with
`C(String n){ name = n }` (`@Requires n != null`) refuted (`fails on: <init>("")`). Shipping the implicit field
invariant on top of that would *false-positive* on correct code, so it waited on a "field-write nullity
propagation" slice — **Phase 132**.

**Shipped tests**: group `P-nonnull` (explicit and implicit `result != null` prove from literal/concat/known-param;
refute on a nullable param; compose with an explicit `@Ensures`; and a both-checkers case showing the
complementary catch with no double-report).

---

## Phase 132 — field-write nullity propagation (unblocks the `@NonNull` field form)  *(shipped)*

Phase 131 flowed nullity onto `result` at a return; this extends the same value-flow to **field/local writes**, so a
class invariant can finally be *established* and *preserved* over a reference field's nullity — which had been a
silent gap (an int-valued invariant established in a constructor, but a nullity one never did).

In `checkPath`'s scalar-assignment replay, a write `name = expr` to a reference-typed name now propagates nullity:
the known nullity of `expr` (`Encoder.nullityOfExpr`) binds directly, an unknown RHS **havocs** to a fresh free
flag (sound — a reassignment never retains a stale non-null fact), and the formerly out-of-fragment `name = null`
is handled specially (value havoc'd, nullity pinned to *definitely null*) so nulling a field **refutes
preservation** instead of skipping. With that, an *explicit* `@Invariant({ name != null })` with
`C(String n){ name = n }` (`@Requires n != null`) now **establishes** (was `fails on: <init>("")`), an unguarded
constructor refutes, and a method that nulls the field refutes preservation.

On that foundation the **`@NonNull` field form** (reverted in Phase 131) ships: a `@NonNull` reference field
contributes an implicit `field != null` to the class's invariant set (`addNonNullFieldInvariants`, woven into
`walkClassInvariants`), so it rides the full establish/preserve machinery — and cross-class reasoning may now
*assume* a `@NonNull` field is non-null too. Complementary to NullChecker exactly as the return form is:
groovy-verify proves the object-invariant lifecycle (every constructor establishes it, every method preserves it)
that a flow checker doesn't frame.

**Shipped tests**: group `NNFIELD` — explicit `@Invariant({ name != null })` establishes via a guarded ctor /
refutes unguarded / refutes when a method nulls the field; and the `@NonNull` field form proving and refuting the
same three ways.

---

## Phase 133 — uninterpreted functions: `f.apply(x)` as a higher-order foundation  *(shipped — Phase A of the `@Monadic` derivation)*

The `@Monadic` monad-law derivation (scoped as Phase A→D) needs reasoning over *arbitrary* functions — its laws
quantify over the `Function`s passed to `bind`/`map`. This phase lands **Phase A**, the reusable foundation: a
`java.util.function.Function` parameter's `f.apply(x)` is modelled as an **uninterpreted function** over an
uninterpreted value sort. We assert nothing about what `f` computes — only functional congruence (equal arguments
→ equal results), which is exactly a UF symbol; sound by construction.

Mechanics: a new backend primitive `SmtBackend.applyUF(name, args, rangeSort)` (the value-sorted generalisation
of the Int-only `uninterpretedFunc`, declaring the `FuncDecl` lazily from the args' sorts). In
`Encoder.translateMethodCall`, `recv.apply(x)` on a **`VariableExpression` receiver** translates to
`applyUF('apply$' + recv, [translateInSort(x, ObjectSort)], ObjectSort)` — restricted to a named receiver so the
key denotes a stable function (a computed receiver stays unmodelled). No global `sortFor` change; the argument is
translated in a dedicated value sort, keeping the blast radius to the `apply` shape itself.

**Shipped tests** (group `P-hof`) pin the exact UF soundness profile: `f(a) == f(a)` proves (congruence),
`f(a) == f(b)` refutes (not forced equal), `a==b ⟹ f(a)==f(b)` proves (the premise connects), and the control
`a==b ⟹ f(a)==f(c)` refutes (no spurious equality).

**Next (not yet built)**: Phase B (wrapper-carrier content/`unit` model), Phase C (the three identity laws),
Phase D (closures → defined functions, for associativity/functor-composition). See the `@Monadic` scope.

---

## Phase 134 — wrapper-carrier datatype model  *(shipped — Phase B of the `@Monadic` derivation)*

A single-value `@Monadic` carrier (Identity/Box/`Res`-shaped) is modelled as a **one-constructor Z3 datatype**:
`Res ≅ mk$Res(content$Res: V)`. The two unit/content round-trips — `content(unit(x)) == x` and
`unit(content(m)) == m` — then hold by *datatype theory*, for free, with no hand-written axioms and no
quantifier-trigger fragility (the reason datatypes beat the uninterpreted-sort-plus-axioms encoding the scope
floated).

Mechanics: `SmtBackend.wrapperSort`/`wrapperUnit`/`wrapperContent` (Z3 `mkDatatypeSort` + constructor/selector).
`Encoder.wrapperContentField(cn)` recognises a carrier — `@Monadic`-annotated, exactly one non-static *final*
field; `sortFor` maps it to the datatype sort, `new Res(a)` to the constructor, and `m.content` (variable *or*
freshly-constructed receiver) to the selector. The resolved carrier is threaded in via a new `carrierTypes` map
(parallel to `combiners`), because a re-parsed contract's `new Res(a)` carries an unresolved type — recovered by
simple name.

A dead end worth recording: making `java.lang.Object` a global value sort (so an `Object` field/param shares the
`f.apply` value sort) **breaks `def`/`var`/untyped params** — Groovy represents both `Object x` and untyped `def x`
as `java.lang.Object`, so they're indistinguishable by type, and 6 inference tests regressed. So the carrier's
content keeps its field's natural sort here; unifying the apply/content value sort is deferred to Phase C, which
will need it only inside the laws (where the carrier context disambiguates).

**Shipped tests** (group `P-carrier`): `new Res(m.v) == m` and `new Res(m.v).v == m.v` prove by datatype theory;
the control `m == n` over two distinct carriers refutes (not vacuous).

**Next**: Phase C — synthesize the three identity laws (à la Phase 130) and discharge them over the Phase-A
`apply` + Phase-B carrier, unifying the value sort; Phase D — closures as defined functions (the stretch).

---

## Phase 135 — the Tier-1 monad/functor laws (left, right & functor identity)  *(shipped — Phase C of the `@Monadic` derivation)*

Where Phases A and B finally combine: **all three Tier-1 identity laws** are **proven** for an Identity-shaped
`@Monadic` carrier — left identity `unit(a).chain(f) == f.apply(a)`, right identity `m.chain(unit) == m`, and
functor identity `m.transform(id) == m` — over the carrier datatype (Phase B), the uninterpreted `apply` (Phase A),
and a model of `bind`/`map`.

Four pieces made it compose:
- **Value-sort unification.** A carrier's `Object` content now shares the `f.apply` value sort (`contentSortFor`),
  so `content(m)` and `f`'s argument are the same sort. (A bug this surfaced: `translateInSort` mis-read a content
  read `m.v` as an *enum constant* under a non-Int sort — fixed by recognising carrier content reads first.)
- **Function return types.** A `Function<A, R>` parameter's `f.apply(x)` now ranges over `sortFor(R)`
  (`collectFunctionReturnTypes`), so a *bind* function (`Function<Object, Res>`) applies into the **carrier** — the
  law's two sides (`…chain(f)` and `f.apply(a)`) then share one UF.
- **Sound bind/map modelling.** `m.bind(f)`/`m.map(p)` are modelled by their *definitions* —
  `f.apply(content(m))` / `unit(p.apply(content(m)))` — but only after **verifying** (not assuming) the carrier's
  bind/map *bodies* are the Identity shape (`(C) f.apply(field)` / `new C(f.apply(field))`), read from the clean
  pre-contract snapshot so a `@Requires` guard doesn't hide it.
- **Applying a function argument** (`applyFunction`): a *named* function becomes its UF symbol (left identity); a
  single-parameter *closure literal* is **beta-reduced** (`translateWith` binds the param). That's exactly how the
  `unit` (`{ x -> new C(x) }`) and `identity` (`{ x -> x }`) functions of right/functor identity reach the carrier —
  both reduce to `unit(content(m))`, which the datatype round-trip equates to `m`.

**Shipped tests** (group `P-monadlaw`): left, right, and functor identity all prove; two controls refute —
`unit(a).chain(f) == f.apply(b)` (applications not forced equal) and `m.transform(id) == n` (distinct carriers not
collapsed).

**Deferred** (honest scope): **associativity** needs the *general* constructed closure `{ x -> f(x).chain(g) }`
(Phase D — a closure whose body itself calls bind, beyond the unit/identity beta-reduction here); method-reference
unit (`Res::new`) isn't recognised yet (closure form only). Carriers remain restricted to single-value immutable
wrappers (Maybe/Either/`Stream` out, as scoped). **Phase 136 adds the auto-synthesis.**

---

## Phase 136 — `@Monadic` auto-synthesis: the annotation proves itself  *(shipped — completes Phase C)*

The thin Phase-130-style layer on top of the Tier-1 law engine: a `@Monadic` carrier's three identity laws are now
**derived from the annotation and discharged with no hand-written lemmas** — the same "the annotation proves
itself" story `@Reducer` got, for monads.

`verifyMonadicLaws(ClassNode)` fires per class in `afterVisitClass` (the per-class hook, vs `@Reducer`'s
per-method). It reads `@Monadic`'s `bind`/`map` members (structural defaults `flatMap`/`map`), takes the
constructor as `unit`, and synthesises a void lemma per law via the `@ContractSource` trick (`runMonadicLaw`):
`new C(a).bind(f) == f.apply(a)` (left), `m.bind(x -> new C(x)) == m` (right), `m.map(x -> x) == m` (functor) — the
bind-function param typed `Function<Object, C>` so `f.apply` ranges over the carrier. Each rides the normal
machinery and is discharged by Phases A–C; a refutation reports as `Cannot prove @Monadic <law> for carrier <C>`
(`Reporter.formatMonadicLawFailure`).

Crucially it is **gated on the modellable shape** (`Encoder.isIdentityWrapperCarrier`: single-value wrapper whose
bind *and* map bodies are the verified Identity shapes). Any other `@Monadic` carrier — a multi-case
Maybe/Either, an effectful `Stream`, or simply one whose bind/map we can't model — gets **no synthesis, no false
vouch, and no noise**, exactly as scoped. (This gating is also what keeps the synthesis from polluting carriers
that opt into `@Monadic` for the shape but aren't the Identity wrapper.)

**Shipped tests** (group `P-monadauto`): a `@Monadic` carrier with **no lemma methods** has its three identity
laws auto-prove (clean compile); a carrier outside the modellable shape compiles clean (left to the annotation).
The hand-written `P-monadlaw` lemmas keep working alongside the synthesis.

**Still deferred**: associativity (Phase D's general closure — **now shipped, Phase 137**), method-reference unit,
and non-wrapper carriers.

---

## Phase 137 — associativity (Phase D): the full monad law set  *(shipped — completes the `@Monadic` arc)*

The last and hardest law: `m.chain(f).chain(g) == m.chain(x -> f.apply(x).chain(g))`. Two things make it harder
than the identity laws — the right-hand side is a **closure whose body itself binds** (`f.apply(x).chain(g)`), and
both sides **nest** bind over non-variable receivers (`m.chain(f).chain(g)`, `f.apply(x).chain(g)`).

The closure was already handled (Phase C's `applyFunction` beta-reduces any single-parameter closure). The only
missing piece was teaching `carrierTypeOf` to resolve the **nested receivers**: a bind-function application
`f.apply(x)` (a `Function` declared to return the carrier → returns the carrier) and a chained `recv.bind/map(…)`
(returns `recv`'s carrier, resolved recursively). With those, both sides reduce — by datatype + UF reasoning — to
the *same* term `applyG(content(applyF(content(m))))`, so associativity proves; a swapped `m.chain(g).chain(f)`
refutes (bind order is not commutative).

`verifyMonadicLaws` now synthesises associativity too, so a bare `@Monadic` carrier auto-proves the **complete
law set** — left/right/functor identity *and* associativity — with no hand-written lemmas. This brings `@Monadic`
to full parity with `@Reducer`: the annotation proves itself.

**Shipped tests**: `P-monadlaw` adds associativity (proves) and the bind-order control (refutes); `P-monadauto`
now auto-proves all four laws from the annotation alone.

**Remaining scope boundaries** (unchanged): single-value immutable wrappers only (multi-case Maybe/Either,
effectful `Stream` out); method-reference unit (`Res::new`) — closure form only.

---

## Phase 138 — multi-case datatype backend (M-A + M-B)  *(shipped — foundation of the `Maybe`/`Either` extension)*

The backend foundation of the multi-case extension, whose acceptance test is the four-checker example: our own
`Maybe` proving lawful under Vavr semantics and **refuting functor composition** under Optional (null-collapsing)
semantics, compiled under NullChecker + MonadicChecker + PurityChecker + VerifyChecker.

**M-A — N-constructor datatypes.** Generalises the single-constructor wrapper (Phase B) to an **N-constructor
algebraic datatype** — the shape a two-case carrier `Some(v) | None` needs. New `SmtSession` primitives
(`datatypeSort`/`datatypeConstruct`/`datatypeSelect`/`datatypeRecognize`, backed by Z3's `mkDatatypeSort` with
per-constructor selectors and `is$Ctor` recognizers; nullary constructors like `None` supported). Z3's datatype
theory supplies the case-analysis theorems for free — no axioms, no triggers.

**M-B — the `null` element.** `nullValue(sort)` mints a distinguished `null$` per value sort: an ordinary value
(so a Vavr-style `Some(null)` is a real, distinct carrier) that a function can map *to*, and the one an
Optional-style `map` collapses on. `x == nullValue(sort)` is exactly the collapse predicate.

Pure backend, gated by **direct** tests (`DatatypeBackendTest`, the first non-harness unit tests) rather than
source-compilation probes, since the encoder doesn't recognise multi-case carriers until M-C: (1) a `Maybe`
datatype satisfies `content(Some(v)) == v`, `is$Some(Some(v))`, `is$None(None)`, `Some(v) != None` by
construction; (2) the null-collapse seed — *when `g(x)` is null*, Vavr-`map` (`Some(g(x))`) and Optional-`map`
(`None`) **diverge** (`Some(null) != None`), the exact point at which Optional's functor law breaks.

**Next**: M-C (recognise a multi-case `@Monadic` carrier from source); M-D (case-split bind/map — where functor
composition *proves* for Vavr-style and *refutes* for Optional-style, the core result); M-E (synthesis + the
functor-composition law + the four-checker example).

---

## Phase 139 — recognise a two-case carrier from source (M-C)  *(shipped)*

Leaves the backend and enters the encoder: a tightly-scoped two-case `@Monadic` carrier — `@Monadic`, exactly two
non-static fields (a `boolean` discriminant + a content field), a static 1-arg `some` factory and a static 0-arg
`none` factory — is recognised (`Encoder.multiCaseInfo`) and modelled as the M-A two-constructor datatype.
`sortFor` maps it to `Some(value) | None`; `some(v)`/`none()` factory calls translate to the constructors;
`m.value` to the `Some` selector. `carrierTypeOf` resolves a factory-call receiver (so `some(x).value` works), and
`isCarrier` (single *or* two-case) threads carriers into `scalarTypes`/`carrierTypes`.

**Gate** (group `P-maybe`): a real `Maybe` source class proves `some(m.value).value == m.value` and
`some(m.value) != none()` by datatype theory — carrier-rooted so no bare-`Object` param re-introduces the
value-sort split.

Detail of note: the `@Monadic.unit` member is only on mavenLocal (not the ASF snapshot the build uses), so the
some-factory is recognised by the **structural default name `some`**, not `unit=` — which is fine, and keeps the
example buildable against the public snapshot.

**Next**: M-D — case-split `flatMap`/`map` bodies (`present ? … : this`), where the value-sort `null$` (M-B) drives
the Vavr-proves / Optional-refutes verdict on functor composition; then M-E.

---

## Phase 140 — case-split bind/map: the Vavr-proves / Optional-refutes verdict (M-D)  *(shipped — the core result)*

The payoff. A two-case carrier's `flatMap`/`map` bodies (`present ? someCase : this`) are recognised
(`caseSplitTrueExpr` + shape matchers, reading the clean snapshot) and modelled as `ite(is$Some(m), someCase, m)`.
`flatMap`'s some-case is `f.apply(content(m))` (the same for any lawful Maybe); `map`'s some-case is **the
discriminator** — *Vavr* wraps in `Some(g(content))`, *Optional* collapses a null result
`g(content)==null$ ? None : Some(g(content))`. Soundness gated on `isCanonicalWiring` (`some` constructs the
discriminant `true`, `none` `false`, so `present(m) ⟺ is$Some(m)`).

The result, on real `Maybe` source classes (group `P-maybe`):
- **functor composition PROVES for Vavr-style** and **REFUTES for Optional-style** — the witness being a function
  that returns null, exactly Optional's broken-functor folklore turned into a counterexample.
- left identity + associativity **prove** for the two-case carrier (the monad laws hold for both, since `flatMap`
  doesn't collapse — only `map` does).

Two bugs surfaced and fixed along the way: (1) resolved method bodies use `StaticMethodCallExpression`
(`Maybe.some(…)`) where re-parsed contracts use `MethodCallExpression` — the body matchers now read either; (2) an
`Object`-returning function's `apply` range was the `Int` default (`sortFor(Object)`), mismatching the value sort —
a new `functionRange` helper maps `Object`→the value sort and carriers→their datatype, fixing both the apply path
and `applyFunction` (and `carrierTypeOf` now accepts a function returning *any* carrier, not just single-field
wrappers, so the associativity closure `{x -> f.apply(x).flatMap(g)}` resolves).

**Next**: M-E — generalise `verifyMonadicLaws` to two-case carriers (+ the functor-composition law) and assemble
the four-checker example (Optional almost-monad, Vavr lawful reference, our two-variant `Maybe`) under NullChecker +
MonadicChecker + PurityChecker + VerifyChecker.

---

## Phase 141 — `@Monadic` auto-synthesis for two-case carriers (M-E)  *(shipped — the verdict is now annotation-driven)*

`verifyMonadicLaws` now covers **both** modellable shapes — the single-value Identity wrapper (Phase 136) and the
two-case carrier (`Encoder.isModellableTwoCaseCarrier`) — and synthesises **five** laws (the four identity/assoc
laws plus **functor composition**, the discriminator). `unit(arg)` is parameterised: `new C(arg)` for a wrapper,
`some(arg)` for a two-case carrier. So `@Monadic` alone now carries the verdict for a `Maybe`:

- a **Vavr-style** `Maybe` (no hand-written lemmas) **auto-proves all five laws** — clean compile;
- an **Optional-style** `Maybe` **auto-refutes a functor law** — `Cannot prove @Monadic functor …`, flagging that
  the null-collapsing `map` is not a lawful functor.

A collision fixed en route: a two-case carrier's `@NonNull` content is *conditional* (`present ⟹ value != null`;
`None` legitimately holds null), so the Phase-132 blanket `value != null` field invariant is **skipped for carrier
classes** (it would be false for `None` and mis-translate the case-split bodies). The carrier owns its content
nullity.

**Shipped tests** (group `P-maybe`): Vavr-style all-laws-auto-prove; Optional-style auto-refutes a functor law.

**Honest remaining scope (M-E part 2 / the headline example):**
- **The faithful Optional verdict.** With our unconstrained model, Optional refutes functor *identity* first
  (because we permit `Some(null)`). Optional's real contract is `@NonNull` content, under which identity *holds*
  and *composition* is the sole break. The fix is a **per-param** ground assumption `is$Some(m) ⟹ content(m) !=
  null$` (a *universal* axiom over-constrains — it forces the collapse's `Some(p(c))` some-branch term to be
  non-null even when unselected, wrongly proving composition). That per-param plumbing is the next slice.
- **The four-checker example** itself (NullChecker × MonadicChecker × PurityChecker × VerifyChecker, with a
  comprehension and the `@Pure`/`@Nullable`/`@NonNull` annotations) is integration/packaging on top — the engine
  capability (prove-Vavr / refute-Optional via auto-synthesis) is done.

---

## Non-goals

Things deliberately not pursued, because they don't pay back:

- **Soundness as a hard property.** This is *loud unsoundness*: everything
  outside the fragment emits a "skipped: outside fragment" diagnostic, which is
  honest. Chasing actual soundness would mean rejecting any program that touches
  anything outside the fragment — which is most of them.
- **Orthogonal properties owned by sibling checkers.** Nullness (flow + `@Nullable`/`@NonNull`),
  regular-expression validity, `printf`/`String.format` argument matching, and `@Pure`/side-effect
  compliance are each covered by a dedicated `groovy-typecheckers` extension (`NullChecker`,
  `RegexChecker`, `FormatStringChecker`, `PurityChecker`/`ModifiesChecker`). They ride the same
  `@TypeChecked(extensions = …)` SPI and compose with this one, so groovy-verify stays focused on
  *functional* (contract + arithmetic + array/quantifier) verification rather than reimplementing
  them. Two relate directly: `NullChecker` is the annotation-driven specialist where our nullity
  oracle is a by-product (see the README's "Relationship to Groovy's other checkers"), and
  `PurityChecker`/`ModifiesChecker` can verify the purity our pure-function evaluation (Phase 8a) and
  `@Modifies` framing (Phase 13) assume.
- **Concurrency soundness.** No race detection, no interleaving or deadlock reasoning. The concurrency
  examples (Phases 115–119) prove a *sequential* local obligation and **assume** the structural guarantee
  (mutual exclusion / serialization / single-assignment / FIFO delivery); they don't verify that guarantee.
  Proving thread safety itself is a different tool.
- **Inheritance & traits — *supported* (Phases 15a, 120, 121, 122); one override slice remains.** A subclass is
  verified along the `extends` axis (conjoined class `@Invariant`s up the superclass chain; `super.m(…)` assumes
  the parent's `@Ensures` / discharges its `@Requires`; group `P-inheritance`), an override that redeclares its
  contract is proved a **behavioral subtype** (Phase 120, LSP), and **traits** work along the `implements` axis:
  a trait `@Invariant` is enforced on implementers (Phase 121) and a trait's contracted *default methods* are
  verified by recovering their pre-weave snapshot and rewriting the woven field accessors (Phase 122). The one
  open slice: an **uncontracted** override is not re-verified against the inherited contract — the verifier
  checks a method only against the clause it declares; groovy-contracts still enforces the inherited one at
  runtime. (A behavioral-subtyping check across the *trait*/`implements` axis, not just `extends`, is the natural
  extension of Phase 120 if it's ever wanted.)
- **Heap / aliasing — *partially revisited* (Phase 89, above; slices 1–2 shipped — reference identity + identity-keyed field reads & writes; the `old`-relative `transfer` is a dual-tenet boundary, not pursued).**
  The fragment models collection state as value-semantics — every `@Modifies` havoc is per-name, and `old`
  snapshots are independent copies. The *general* problem — reachability through object graphs, "everything
  reachable from `x` is unchanged" — would need a separation logic or a points-to analysis layered above SMT,
  whose engineering would dwarf every shipped phase combined; that stays a non-goal, owned by sister tools
  (Viper, Verus' Linear-Permissions story). But the *flat-field* part — two object references that may alias,
  field read/write, reference equality — is a tractable, easy-to-bound slice (Phase 89): model each field as
  one array keyed by object identity, so aliasing is just `a === b`. It unlocks two-object mutators and honest
  framing under sharing, and closes a latent unsoundness in the per-name field model — without touching
  object-graph *shape*, which is the part that doesn't pay back.
- **Floating point — *partially revisited* (Phase 73).** A faithful straight-line `double`/`float`
  sub-fragment now ships on Z3's IEEE-754 theory (bit-exact: NaN, ±∞, RNE rounding) — the useful core
  being **no-NaN / finiteness / bounds / exact-comparison** proofs, plus `Math.sqrt`/`Math.abs`. What
  stays out: FP *loops* (accumulated rounding error), the other transcendentals (`sin`/`cos`/`exp`/`log`),
  and tight relative-error bounds.
  Z3 bit-blasts FP, so it's the slow end and timeout-gated — fine for small straight-line code.
- **Generated proof certificates.** Out of scope.
- **Interactive tactics / proof terms.** The Coq/Lean/F\* style where the user
  drives the proof with `intro`/`split`/`qed` and builds an explicit proof term.
  This is the opposite of a push-button compile-time checker, and adopting it
  would make this a proof assistant rather than a better Groovy type-checker. The
  *bounded* borrows — instantiation hints and structured `assert … by`
  decomposition — live in [Phase 8](#phase-8--beyond-smt-proof-by-computation-and-proof-hints);
  the full tactic engine does not.
- **IDE squiggles.** Diagnostics go through `addStaticTypeError`, which IDEs
  surface via their Gradle integration. Going further — inline counterexample
  popups, fix suggestions — is downstream of this work, not part of it.

---

## Cross-cutting risks worth noting up front

- **Compilation slowdown.** Z3 calls take 10–100 ms each. A large module with
  seconds to a compile. The in-process VC cache is shipped (see
  [Phase 34](#phase-34--vc-cache--shipped)) and rebated ~18 % when measured (at the
  Phase-34 suite size); a `-PverifyEnabled=true`-style "verify only" configuration and a
  persistent disk cache keyed on class-file digests remain as further levers.
- **`@CompileStatic` incompatibility.** The checker is a type-checking
  extension; code authored under `@CompileStatic` needs the checker to either
  work as an AST transformation instead, or run before `@CompileStatic` makes
  its static decisions. Substantial design work; deferred.
- **Producer/consumer rebuild discipline.** The contracts are stock
  `groovy.contracts` annotations; the only thing this library adds at
  producer-compile-time is the `@ContractSource` that captures verbatim contract
  text into bytecode. That carrier matters in exactly one situation: a consumer
  statically verifying a *call* to a `@Requires`-annotated method in **another
  module**. For that to work, the producer must have been compiled with
  `groovy-verify` on its classpath; otherwise those call sites degrade to
  "skipped". This does **not** apply to `@Ensures`/`@Invariant`/`@Decreases` or
  the implicit checks — they are verified in-unit, where the checker is already
  running. And groovy-contracts' *runtime* checks are orthogonal: a producer
  built without this library still enforces its contracts at runtime; it merely
  forgoes the consumer-side compile-time proof.
- **Z3 model expressiveness.** Counterexamples show concrete integer values,
  which is great for `isqrt(-1)`. Once arrays are in scope (Phase 6), showing
  "the array such that ¬P holds" gets visually awkward — Z3's array models look
  like `(store (store (as-array k!0) 0 -1) 1 0)`. A pretty-printer for array
  models is small but worth budgeting.

---

## Bitwise / shift operators (`& | ^ << >>`)  *(shipped)*

Closes the integer-bitwise gap left open since Phase 44. A **hybrid** lowering keyed on the operator:

- **Shifts by a non-negative literal** stay in **unbounded Int arithmetic** — `x << k` ⟶ `x * 2^k`,
  `x >> k` ⟶ `⌊x / 2^k⌋` (Z3's flooring `intDiv`, so the arithmetic right shift is faithful for negative
  `x` too). This matches how `*` / `intdiv` are modelled (unbounded by default, overflow opt-in via
  `@CheckOverflow`), keeps the common power-of-two idioms quantifier-free, and lets `(x << 1) == x * 2`
  prove. The shift count uses the source literal; `k > 31` falls through to the BV path (which masks).
- **Bitwise `& | ^` and variable shifts** have no arithmetic form, so they lower to **Z3's bit-vector
  theory at Java's 32-bit width**: `Encoder.translateBitwise` calls new backend `bvAnd`/`bvOr`/`bvXor`/
  `bvShl`/`bvShr`, each `int → (_ int2bv 32) → BV op → (bv2int … signed)`. Faithful Java two's-complement
  semantics — wraparound, sign extension, shift-count masked to 5 bits, `bvShr` = arithmetic (sign-filling)
  `>>`. Because `int2bv` reduces its argument mod 2^32, the op is sound even for an unbounded operand (it
  sees the same low 32 bits Java's `int` would). Non-Int operands (e.g. a set `a & b` reaching the binary
  translator) throw on the sort mismatch and skip loudly.

So `6 & 3 == 2`, `5 ^ 3 == 6`, `a ^ a == 0`, `a & a == a`, `a | 0 == a`, and the BV-specific `a & 1 ∈ {0,1}`
(low bit) all prove; `1 << 4 == 16` and `x >> 1 == x.intdiv(2)` (for `x ≥ 0`) prove via the arithmetic path.
**Prove-friendly, refute-hostile** (like the recurrence helpers): a wrong *concrete* value refutes crisply
(Z3 folds the BV to a constant — `6 & 3 == 3` ⟶ "Cannot prove"), but a false *symbolic* claim
(`a & b == a`) bit-blasts the negation and soft-fails as a loud "could not decide" within the 2s budget —
sound (rejected, never a false pass), just no counterexample. **Still out:** `~` (bitwise NOT), `>>>`
(unsigned/logical right shift), and shift-overflow obligations under `@CheckOverflow` (a shift's synthesised
`*` isn't an AST `MULTIPLY` site, so the overflow collector doesn't see it). Locked by the `bitwise` tests.

---

## Definition of done, per increment

An increment is done when:

1. The motivating example compiles cleanly under the checker.
2. *Some* deliberately-broken mutation of it fails to compile, with a diagnostic
   that points at the right source location and includes a counterexample with
   the right values.
3. *Another* mutation that is incompletely specified produces a "could not
   decide", not a silent pass.
4. The README's capability table grows by N rows, and the self-test harness
   (`./gradlew verify`) gains good/bad cases for it.
5. Solver wall-clock per site stays under ~200 ms on a current laptop.

Anything else — broader coverage, more examples, better messages — is polish
that does not gate the next increment.

