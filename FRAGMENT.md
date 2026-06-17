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

# The fragment

The complete, itemised description of what groovy-verify can and cannot model. For the high-level
summary and positioning, see [README.md](README.md#the-fragment); for the increment history,
[ROADMAP.md](ROADMAP.md).

Verification is sound *within* a deliberately **modest** fragment and **loudly
unsound outside it**: anything the encoder cannot model emits a "skipped"
warning rather than passing silently. It is modest by *intent*, not by size — the
bullets below were each chosen because they line up with proofs people actually
write (bounds, aggregation, sortedness, state machines, recurrences), not to chase
a coverage metric. In expressions the fragment is:

- integer `+`, `-`, `*` (variable products dispatch to Z3's NIA solver under a per-VC timeout, with
  closed subterms folded first; Phase 48), and Groovy-faithful `.intdiv`/`%`/`.mod` (Phase 50); the
  `/` operator is `BigDecimal` division, modelled with Z3's exact **Real** sort (Phase 61) so
  `5 / 2 == 2.5` and `BigDecimal` contracts prove (int operands coerced; only `BigDecimal` is
  exact-Real — `double`/`float` take the IEEE-754 FP path, below); divide-by-zero and
  `.mod`-non-positive obligations fire; `**` lowers to an axiomatised `pow$` (Phase 93) — a literal
  exponent folds to a value (`(2 ** 3).intValue() == 8` proves) and the doubling recurrence
  `2 ** (n+1) == 2 * (2 ** n)` proves for *symbolic* `n`, though a false symbolic-exponent value claim
  is refute-hostile (soft-fails to "could not decide", like the `Fib`/`Gcd` recurrences);
- bitwise / shift operators `& | ^ << >>` (Phase: bitwise) — shifts by a non-negative literal stay in
  unbounded Int arithmetic (`x << k` is `x * 2^k`, `x >> k` is `⌊x / 2^k⌋`), while `& | ^` and variable
  shifts lower to Z3's **bit-vector theory at Java's 32-bit width** (faithful two's-complement; bit-blasted,
  so timeout-gated and refute-hostile on symbolic claims); `~` / `>>>` stay out;
- straight-line `double`/`float` on Z3's IEEE-754 **FP theory** (Phase 73) — bit-exact (NaN, ±∞, RNE),
  with `Math.sqrt`/`Math.abs`; `0.1d + 0.2d != 0.3d` and no-NaN/finiteness prove, FP loops/transcendentals
  skip;
- `xs.max()` / `xs.min()` as the witnessed-extremum spec — `r` bounds every element and is achieved by one
  of them, so `result == a.max()` means what you'd write by hand — over Int (Phase 60), `BigDecimal`/Real
  (Phase 76) **and** `double` lists/arrays (Phase 77, guarded all-non-NaN since FP isn't totally ordered);
  `double[]` / `List<Double>` element predicates ride the same FP theory (a hand-written extremum *loop*
  stays Int/`BigDecimal` only — FP comparisons are bit-blasted, so a quantified FP loop invariant doesn't close);
- aggregation specs carried by a loop invariant: `xs.sum()` and the `inject(1){ a, x -> a * x }` product fold
  (Phases 51/52) over Int and `String` (concatenation on the `str.++` monoid), and `List<BigDecimal>` decimal
  sums with N-account *conservation* (`bal.sum() == old.bal.sum()`; Phases 68–70); the recurrence spec helpers
  `Fib.of(i)` / `Trib.of(i)` / `Gcd.of(a, b)` / `Lcm.of(a, b)` lower to axiomatised primitives (Phases 55/63/87);
- `String` on Z3's native theory of strings (Phase 47): predicates (`startsWith` / `endsWith` / `contains` /
  `isEmpty`), `length` / `size` / `charAt` / `substring` / `indexOf`, composition (`+` / `concat` / `replace` /
  regex `matches`) and GString interpolation, plus `Integer.toString` / `parseInt` conversion and
  the uninterpreted (literal-pinned / weak-axiom) ops `toUpperCase` / `toLowerCase` / `replaceAll` /
  `reverse` (Phase 47i — `"abc".reverse() == "cba"` and literal involution fold; symbolic algebra stays out);
  plus **read-only per-character loops** — a quantified loop invariant over `s.charAt(i)` (the string analogue
  of the array ∀-element proofs), with the char literal spelled `('a' as char)` (Phase 105). *Building* a
  string char-by-char times out on the seq theory, so a constructed buffer goes through `char[]` (an
  Int-element array) instead — e.g. OpenJML `ChangeCase` (Phase 106);
- array construction: a fixed-arity literal `new int[]{a, b}` (the array dual of a list literal — folds
  `result[k]` / `.length` / component-wise `==`) and a sized allocation `new int[n]` (a fresh, Java-zero-filled
  array: `sizeOf == n`, non-null, const-0 contents, so an unwritten element reads `0` and a body store
  bounds-checks); an `int[]`-typed return accepts a coerced list literal `[a, b]` or `new int[]{a, b}` (Phase 78);
- structured returns and products: a list-literal return binds `result` for constant-index `result[k]`
  (Phase 78); `Tuple` / `TupleN` fixed-arity typed products with `.vN` slot access, tuple parameters and
  component-wise `==` (Phases 79–82) — including a tuple returned from an **early-exit** path (`return
  Tuple.tuple(i, j)` mid-loop; Phase 110) and a tuple-returning call bound to a **local** whose slots are then
  used in the body, as an index / call argument / return (`Tuple2 r = f(a); … a[r.v1] …`; the
  **inter-procedural** case, Phase 113); and Groovy's map-as-named-tuple (`return [sum: s, …]`, `result.sum`;
  Phases 83/84) — generic-typed component accessors keep their declared type in the contract closure
  (GROOVY-12071), so *arithmetic* and *ordering* on a slot / map value / generic-list element type-check with
  no cast;
- infinite-stream `every` / `any` over `Stream.iterate(seed, f)` with a required `.limit(n)` / `.take(n)`: a
  literal limit *unrolls*, a symbolic limit proves the property of *every* element by induction (base +
  preservation); an unbounded terminal `every` skips loudly (Phase 75);
- range membership — `(a..b).containsWithinBounds(v)` as a pure bounds check over all four range forms
  (Phase 74), and the `in` operator (and `.contains`) over an **integer** range `i in lo..hi` and a
  **single-character `String`** range `c in 'a'..'z'` (Phases 99 / 99b), the spelling a `switch`/`case` range
  label desugars to;
- `switch` *expressions* — the arrow form `switch (x) { case 1 -> …; default -> … }` with simple `int`/`String`
  literal (and integer-range) labels folds to an `ite`-chain; the statement form and pattern/guarded cases
  stay out (Phase 102);
- comparisons (including the spaceship `<=>`, Phase 58), the boolean connectives `&&`/`||`/`!` and logical
  implication `==>` / `.implies()` (Phase 57), and the conditional `?:` — all short-circuit-aware, so a guard's
  left operand protects accesses in its right (`i > 0 && a[i - 1] < a[i]`) and a `?:` branch is checked under
  its condition;
- the size / nullity / membership oracles from the table above
  (`xs.size()`, `x == null`, `xs.contains(y)`, `x.equals(y)`, `isEmpty()`);
- array/list contents under Z3's array theory (`a[i]` reads, `a[i] = v` updates) with
  bounded **universal** *and* **existential** quantifiers — `Forall.range` / `(lo..<hi).every{…}` /
  `xs.indices.every{…}` / `xs.every{ it… }` and the existential `(lo..<hi).any{…}` / `xs.any{ it… }` — which
  **nest** (a `∀∀` "nothing-found-yet" invariant whose negation at loop exit contradicts an `∃∃` precondition
  is how a search is proven *total*, Phase 111); a **content-dependent index** `a[b[k]]` (gather / scatter /
  histogram, where the index is itself an array read) bounds against the value-range invariant inside a loop,
  not just outside it (Phase 108);
- finite `Set<Integer>` membership (`x in s`, `s.contains(x)`), mutation (`s.add(x)` /
  `s.remove(x)`, threaded through the body) and cardinality (`s.size()`) — a set is a
  characteristic array, and `size()` carries a per-mutation update law (`add` of an absent
  element raises it by one), which drives a set-valued `@Decreases` measure (`n - s.size()`,
  the DFS-shaped termination argument); subset (`s.containsAll(t)`) and equality (`s.equals(t)`)
  are in for enum-element sets and for Int-element sets under `Sets.boundedBy(t, n)`; the full
  **set algebra** — union (`a + b` / `a | b`), intersection (`a.intersect(b)` / `a & b`), difference
  (`a - b`) and symmetric difference (`a ^ b`) — is in both *inline* (`x in (a op b)`, `containsAll` on a
  binop receiver) **and *materialised*** (`Set<X> u = a op b` mints `u` as a first-class set with the
  membership iff axiom), for enum-element sets (finite domain) and Int-element sets (`Sets.boundedBy` bound);
- finite `Map<Integer,Integer>` — value lookup (`m[k]`, `m.get(k)`), key membership (`k in m`,
  `m.containsKey(k)`), mutation (`m.put(k,v)` / `m[k] = v`) and size (`m.size()`): a map is a
  value array plus a key-set, so a put both stores the value and adds the key (with the same
  cardinality law), and `m.size()` likewise drives a recursive measure over the key domain;
  `m.containsValue(v)` is in for enum-keyed maps (finite disjunction over key constants);
  **`Map<K, Set<V>>` nesting is in for reads** (`m[k].contains(x)`, `m[k].containsAll(s)`,
  `x in m[k]`) via a nested array sort `Array<K, Array<V, Int>>`; `keySet`/`values` projections
  and nested-set mutation remain outside;
- list element nullability: `xs[i].method()` / `xs.get(i).method()` is an implicit NPE obligation
  against a per-element nullity oracle, discharged by `@Requires({ xs[i] != null })` or an
  `if` guard;
- immutable container factories — `List.of(args)` / `Set.of(args)` / `Map.of(k,v,…)` and Groovy
  literals `[a, b, c]` / `[k: v]` (and `as Set` casts) peephole-fold to ground SMT terms on
  `.size()`, `.contains` / `containsKey` / `containsValue` / `in`, and `.get(literal_i)` —
  and the same folds lift across a local binding (`xs = List.of(…); xs.size()`), with the
  factory's nullity and size pinned on the assignment so implicit checks pass too;
- fuel-bounded inlining of contract-free pure functions (a closed call like
  `pow2(10)` is evaluated to a literal, a symbolic one unfolded);
- higher-order functions and algebraic carriers, for *law* proofs: a `java.util.function.Function`'s
  `f.apply(x)` is an uninterpreted function (functional congruence only), and a `@Monadic` carrier — a
  single-value immutable wrapper *or* a two-case `Some(v) | None` — is modelled as a Z3 datatype, so the
  monad / functor laws (left/right identity, associativity, functor identity/composition) derive from the
  annotation alone (Phases 133–141); the combiner analogue inlines an `@Reducer`/`@Associative` method as
  its `@Ensures` equation at call sites and derives the monoid laws (Phase 130) — both worked through in
  [Relationship to Groovy's other checkers](README.md#relationship-to-groovys-other-checkers);
- scalar instance-field reads (`this.count` / bare `count`) in contracts and bodies.

The unit of verification is a **method** (static or instance) carrying contracts — the enclosing definition is
*context*, not itself a proof target. The engine models a **class** (instance fields, SSA-tracked across a
mutator's pre/post state, and a class `@Invariant` assumed-on-entry / checked-preserved-on-exit), an **enum**
(a finite uninterpreted sort with a known value-count, for membership / pigeonhole / cardinality), and a
**record** (its components are final fields, so they read like any class field, and a record may carry its own
contracts) — but it does *not* verify the definition itself: the canonical constructor, deconstruction /
pattern matching, and generated `equals`/`toString`/`hashCode` aren't modelled, and an `enum` or `record` is
understood only through the fields and finite domain its methods actually touch.

Verification also follows the **type hierarchy**: a subclass method is proved against its ancestors' conjoined
class `@Invariant`s, a `super.m(…)` call composes with the parent's contract, an override that redeclares its
contract is checked for **behavioral subtyping** (Liskov — precondition weakened, postcondition strengthened),
and a **trait**'s `@Invariant` and contracted *default methods* are verified on every implementer — worked
through in [Inheritance, traits & behavioral subtyping](README.md#inheritance-traits--behavioral-subtyping).
Likewise an **`interface`** method's `@Requires` / `@Ensures` is inherited by every implementer (Phase 123 — the
contract-inheritance walk traverses implemented interfaces, not just the superclass), so an interface-declared
precondition guards the implementer's body and an interface-declared postcondition is checked against it. Honest
boundaries: each class needs its own `@TypeChecked` (it isn't inherited); a method is verified only against the
contract it *declares* — an inherited `@Ensures` isn't re-checked against an *uncontracted* override
(groovy-contracts still enforces it at runtime); and when a method inherits a contract from *both* a superclass
and an implemented interface, the nearer superclass declaration is used (the two aren't conjoined).

For method bodies: straight-line code, `if`/`else`, locals and instance fields (re-assignable,
tracked in SSA so a mutator's pre/post state differ), compound assignment (`+= -= *= /= %=`) and pre/post
`++`/`--` both as statements and **in expression position** (`x = i++` / `x = ++i` / `a[i++] = v` /
`x = a[i++]` — the side-effecting inc/dec is hoisted to its old/new value plus the increment, so the array-fill
loop `while (i < n) a[i++] = 0` verifies and an out-of-bounds `a[i++]` refutes; Phases 85/86), multiple
assignment — both the declaration `def (a, b) = [1, 2]` and the bare parallel **swap** `(a, b) = [b, a]`
(the right-hand side is snapshotted before any target is written; Phases 79 / 90), and an
annotated loop — `while`, `do … while` (Phase 88), a classic
`for (init; cond; update)`, or `for (x in xs)` over a named collection, all desugaring to the same machinery
(Phases 59 & 63; the for-in's index is synthesised and hidden, the loop variable keeps its name; `.each` stays
outside the fragment and skips loudly), **optionally with a second loop nested inside it** (Phase 91, two
levels, scalar accumulators or array-filling inner bodies — and the inner loop may **`return` a witness** on a
match, so a doubly-nested search verifies, Phase 109 — see below). A `do … while` is `B; while (G) B` — its body runs once
unconditionally, so the invariant is checked *after* that first iteration, not at entry (modelling it as a
plain `while` was silently unsound — a false invariant established pre-body could prove a wrong spec). Across method boundaries: a callee's `@Ensures` is assumed at its call site — including a **tuple-returning**
call bound to a local, whose slots then carry the callee's postcondition into the caller's body
(`Tuple2 r = f(a); … r.v1 …`; Phase 113) — a method-level
`@Decreases` lets the method's own `@Ensures` be assumed at a recursive call (proof by induction — and a
`void` lemma proven once then applied by calling it), and `@Modifies` frames what a call may change so the
caller havocs only those locations while `old.x` snapshots pre-state field and array contents. A class-level
`@Invariant` on a mutable object is **assumed on entry and checked preserved on exit** of every method, so a
data structure verifies as a unit — a mutator that breaks it refutes (Phases 45 / 107, the ring buffer). When the
solver returns *UNKNOWN* on a
postcondition (a quantifier/recurrence-axiom timeout), a bounded property-based pass runs the
executable contract over a small grid of integer inputs and reports any concrete failing input as a
best-effort `fails on:` repro (Phase 62). See `Encoder` and the roadmap for the exact boundaries.
