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
  closed subterms folded first; Phase 48 — and **`BigInteger`**, Groovy's arbitrary-precision integer, flows in
  this same unbounded Int sort, the *most* faithful integer type since Z3's `Int` has no width or overflow, modulo
  a literal wider than 64 bits which skips loudly; Phase 124), and Groovy-faithful `.intdiv`/`%`/`.mod` (Phase 50); the
  `/` operator is `BigDecimal` division, modelled with Z3's exact **Real** sort (Phase 61) **only when the divisor
  terminates** — a constant whose unscaled integer has just the prime factors 2 and 5 (`/2`, `/1000`, `/0.25`), so
  `5 / 2 == 2.5` and a `metres / 1000` unit conversion prove exactly; a non-terminating divisor (`/3`, `/7`, a
  symbolic one) **skips loudly**, since Groovy rounds it and an exact-Real model would prove runtime-false facts
  (Phase 143). Int operands are coerced; only `BigDecimal` is exact-Real — `double`/`float` take the IEEE-754 FP
  path, below; divide-by-zero and
  `.mod`-non-positive obligations fire; `**` lowers to an axiomatised `pow$` (Phase 93) — a literal
  exponent folds to a value (`(2 ** 3).intValue() == 8` proves) and the doubling recurrence
  `2 ** (n+1) == 2 * (2 ** n)` proves for *symbolic* `n`, though a false symbolic-exponent value claim
  is refute-hostile (soft-fails to "could not decide", like the `Fib`/`Gcd` recurrences);
- bitwise / shift operators `& | ^ << >> >>>` and complement `~` (Phase: bitwise; Phase 125 for `~` / `>>>`) —
  shifts by a non-negative literal stay in unbounded Int arithmetic (`x << k` is `x * 2^k`, `x >> k` is
  `⌊x / 2^k⌋`), while `& | ^` and variable shifts lower to Z3's **bit-vector theory at Java's 32-bit width**
  (faithful two's-complement; bit-blasted, so timeout-gated and refute-hostile on symbolic claims). `~x` is the
  exact Int identity `-x - 1` (no bit-vector, not refute-hostile); the logical / unsigned `>>>` always goes
  through the 32-bit bit-vector — its zero-fill result depends on the sign pattern, so unlike `<<` / `>>` it has
  no unbounded-Int form even for a literal count, but `x >>> 1 >= 0` still *proves* (bit-vectors are complete);
- straight-line `double`/`float` on Z3's IEEE-754 **FP theory** (Phase 73) — bit-exact (NaN, ±∞, RNE),
  with `Math.sqrt`/`Math.abs`; `0.1d + 0.2d != 0.3d` and no-NaN/finiteness prove, FP loops/transcendentals
  skip;
- `xs.max()` / `xs.min()` as the witnessed-extremum spec — `r` bounds every element and is achieved by one
  of them, so `result == a.max()` means what you'd write by hand — over Int (Phase 60), `BigDecimal`/Real
  (Phase 76) **and** `double` lists/arrays (Phase 77, guarded all-non-NaN since FP isn't totally ordered); a
  body `a.max()`/`a.min()` carries an implicit **non-empty obligation** (`[].max()` throws
  `UnsupportedOperationException`, the same `0 < size` shape as `first()`/`pop()`), so it's refused unless the
  receiver is provably non-empty — *in the body; the same call inside a contract isn't yet well-definedness-checked*;
  `double[]` / `List<Double>` element predicates ride the same FP theory (a hand-written extremum *loop*
  stays Int/`BigDecimal` only — FP comparisons are bit-blasted, so a quantified FP loop invariant doesn't close);
- aggregation specs carried by a loop invariant: `xs.sum()` and the `inject(1){ a, x -> a * x }` product fold
  (Phases 51/52) over Int and `String` (concatenation on the `str.++` monoid), and `List<BigDecimal>` decimal
  sums with N-account *conservation* (`bal.sum() == old.bal.sum()`; Phases 68–70) — with Groovy's duck-typed
  empty-fold honoured: a numeric **array**'s `[].sum()` is `0`, but a **List**/sublist's `[].sum()` is *`null`*
  (the no-arg fold has no zero element, the way `['', 1, 2, 3].sum() == '123'`), so a bare `a[0..<k].sum()` over a
  possibly-empty sublist is modelled as unconstrained at empty and a spec like `int == a[0..<k].sum()` *refuses*
  to prove at the empty edge — the seeded `a[0..<k].sum(0)`, a guaranteed-non-empty range, or the int[]-returning
  `Arrays.copyOf(a, len).sum()` (a fresh array, so empty is 0) are the empty-safe forms; the recurrence spec helpers
  `Fib.of(i)` / `Trib.of(i)` / `Gcd.of(a, b)` / `Lcm.of(a, b)` lower to axiomatised primitives (Phases 55/63/87);
- `String` on Z3's native theory of strings (Phase 47): predicates (`startsWith` / `endsWith` / `contains` /
  `isEmpty`), `length` / `size` / `charAt` / `substring` / `indexOf`, composition (`+` / `concat` /
  regex `matches`) and GString interpolation, plus `Integer.toString` / `parseInt` conversion. The
  string-*rewriting* ops are uninterpreted (literal-pinned / weak-axiom) — `toUpperCase` / `toLowerCase` /
  `reverse` (Phase 47i — `"abc".reverse() == "cba"` and literal involution fold; symbolic algebra
  stays out). The three substitution methods (Phase 47b/47f) are sound by construction: an **all-constant**
  call folds through the *real* JDK method, so `"hello".replace("l","P") == "hePPo"` (replace-*all*) and
  `"hello".replaceAll("[aeiou]","X") == "hXllX"` (the regex resolved exactly). A **symbolic** receiver keeps
  only the facts the string theory can prove soundly: `replace` (literal replace-all) carries the weak axioms
  *absent ⇒ no-op* and *equal-length ⇒ length-preserving*; `replaceFirst` with a **plain-literal** regex
  lowers to Z3's first-occurrence `str.replace`; `replaceAll` with a plain-literal regex keeps the same weak
  axioms. A *real* regex (metacharacters) over a symbolic receiver **skips loudly** rather than be mis-modelled
  as a literal substring;
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
- a **range as a list** — a constant integer range `lo..hi` (`..` inclusive / `..<` exclusive) assigned to a
  local is modelled element-for-element (`r[k]` reads `lo + k`, size pinned), and it honours Groovy's
  **immutability**: a bare range is read-only, so an element write `(4..8)[2] = -1` is *refused* (it throws
  `UnsupportedOperationException` at runtime), while the mutable copies `[*lo..hi]` (spread) and
  `(lo..hi).toList()` bind the same contents into a writable array, so a store threads through and the
  other elements keep their range values — and a whole-list `result == [a, b, c]` against a list literal folds
  to size-equality ∧ element-wise equality (so the returned mutated copy compares against the literal);
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
contracts) — but it does *not* in general verify the definition itself: deconstruction / pattern matching and
generated `equals`/`toString`/`hashCode` aren't modelled, and an `enum` or `record` is understood only through
the fields and finite domain its methods actually touch. A **record's canonical constructor is the exception** —
it is modelled as a one-constructor Z3 datatype, so it **round-trips**: a single-component record (Phase 133)
gives `new R(v).f == v`, and a **multi-component** record (Phase 142, ≥2 final fields — the `TupleN` analogue)
gives `new R(a, b).f`, both by datatype theory; a wrong component refutes. A `result`-typed `new R(…)` with a
contract over `.f` verifies — including through **carrier-typed locals** and the **`+` / `*` operators** when the
record carries an instance `plus` / `multiply` with an `@Ensures` and no `@Requires` (`a + b` is routed to
`a.plus(b)` and discharged via the cross-class instance contract; `*` may return a *different* record type, the
type-changing `Length × Length → Area`). The fullest form is one **dimension-carrying** record —
`Quantity(value, l, m, t)` — whose `multiply` scales the value and composes the `(L, M, T)` exponent vector
(`Quantity(2,[1,0,0]) × Quantity(3,[1,0,0]) == Quantity(6,[2,0,0])`), the whole dimensional algebra in a single
type. A **guarded** operator routes soundly too (Phase 142b): the precondition hook fires for `a + b` and checks
`plus`'s `@Requires` at the site, so a `Quantity` `plus` guarded `@Requires({ l == o.l && … })` makes `a + b`
require matching dimensions — same-dimension addition verifies, a Length-plus-Mass refutes — completing the
algebra (`×`/`/` compose exponents, `+`/`−` require them equal). In-record **conversion/scale** is in too: a
`Length.km(v)` factory scales to SI and the read-out divides back when the divisor terminates (Phases 142c/143).
That precondition-check at the `a + b` site **replays the straight-line prefix**, and the replay now models a
carrier-returning contracted call — a factory like `Quantity.km(1)`, or a routed operator — as a fresh
carrier-sorted handle constrained by the callee's `@Ensures`, rather than havocing it to an `Int` (which crashed a
later same-sort equality). So **factory-built operands feed a guarded operator**: `Quantity.km(1) + Quantity.mile(1)`
proves `2609.344` in metres, the dimension guard firing across the factory boundary (Phase 144). A carrier-returning
call is also a value **in expression position** (Phase 145), so the whole thing collapses to a single fluent
**chain** — `Quantity.km(1).plus(Quantity.mile(1))`, receiver and argument both factory calls — modelled by one
recursive primitive (`carrierValueOf`, minting a fresh carrier handle constrained by the callee's `@Ensures`) wired
into the assume side, the precondition discharge (so the guarded `.plus` stays sound), and the return path. A
**read-out in the same expression** works too (Phase 146): a component read on a chain result —
`Quantity.km(1).plus(Quantity.mile(1)).value` (the bespoke `.to(METRE).getValue()`) — hoists each maximal carrier
call to a temp local so the `.value` becomes an ordinary component read, proving `2609.344` as a `BigDecimal` with
no intermediate locals (composes with decimal arithmetic and a local-RHS read-out). **Units-as-data** composes from
these with no new support (Phase 147): a `Unit(scale, l, m, t)` is itself a record value, `Quantity.of(v, unit)` a
factory reading the unit's fields off the carrier-typed formal, and a metric prefix a `Unit → Unit` factory — so the
literal JSR 385 shape `Quantity.of(1, Unit.kilo(Unit.metre())).plus(Quantity.of(1, Unit.mile())).value == 2609.344`
verifies (a read-out in a *non-SI* named unit divides by a symbolic scale and skips). The `1.km + 1.mile` **DSL**
verifies too, *experimentally* (Phase 148): registered Groovy extension methods build JSR 385 quantities, and the
C₁ reader's curated by-name recogniser was extended to the unit-suffix sugar (`m`/`km`/`mile`/`kg`), the `+`/`-`
operators, and `*` (`multiply`) — soundly tracking the unit, so `(1.km + 1.mile).value == 2609.344` *refutes* (it is
`2.609344` in km), and `(1.km * 1.km).value == 1_000_000` *refutes* (it is one km², value `1`, not the metre² number
— an area the erased `Quantity<?>` can't police). Quantity-to-quantity `==` is in too (Phase 151): a dimension
table (`[L,M,T]` exponent vectors) joins the magnitude layer, so the literal `@Ensures({ result == 1.km })` verifies
soundly — *different* dimensions are never equal (`1.m == 1.kg` throws at runtime; folded to `false`), *equal*
dimensions compare magnitude — and the area-vs-length `Quantity squareKm() { 1.km * 1.km }` refutes on dimension.
**Division and locals** (Phase 152): `/` subtracts the dimension exponents (Length−Time = Speed) and divides
magnitudes, quantity-typed locals are aliased to their RHS, and `s` (seconds) joins the vocabulary — so
`def s = 1.s; def d = 1.m; return d / s` with `@Ensures({ result == 1.m / 1.s })` verifies; a `quantity/quantity` is
a Quantity op (no divide-by-zero obligation), and a non-terminating divisor (`1.m / 3.s`) skips (exact-Real soundness).
A coherent-derived-unit suffix `mps` (Speed, scale 1) lets a contract name a speed directly — `@Ensures({ result ==
1.mps })` over `d / s` verifies — the statically-checkable form, since `1.m/s` referencing the body local is rejected
by `@TypeChecked` first (the contract closure is checked in signature scope, not body scope — upstream, not a verifier gap).
It needs the extension module on the classpath, so it lives in the standalone `examples-dsl` subproject. Still out: a
parameter quantity (unknown unit/dimension), deconstruction / pattern-matching, and generated `equals`/`hashCode`.

Verification also follows the **type hierarchy**: a subclass method is proved against its ancestors' conjoined
class `@Invariant`s, a `super.m(…)` call composes with the parent's contract, an override that redeclares its
contract is checked for **behavioral subtyping** (Liskov — precondition weakened, postcondition strengthened),
and a **trait**'s `@Invariant` and contracted *default methods* are verified on every implementer — worked
through in [Inheritance, traits & behavioral subtyping](examples/miscellaneous.md#inheritance-traits--behavioral-subtyping).
Likewise an **`interface`** method's `@Requires` / `@Ensures` is inherited by every implementer (Phase 123 — the
contract-inheritance walk traverses implemented interfaces, not just the superclass), so an interface-declared
precondition guards the implementer's body and an interface-declared postcondition is checked against it. Honest
boundaries: each class needs its own `@TypeChecked` (it isn't inherited); a method is verified only against the
contract it *declares* — an inherited `@Ensures` isn't re-checked against an *uncontracted* override
(groovy-contracts still enforces it at runtime); and when a method inherits a contract from *both* a superclass
and an implemented interface, the nearer superclass declaration is used (the two aren't conjoined).

Beyond `@Requires`, a method-entry precondition can also come from a **Jakarta / `javax.validation` constraint** on
a parameter or field — `@Positive` / `@PositiveOrZero` / `@Negative` / `@NegativeOrZero` / `@Min(n)` / `@Max(n)` on
`int` / `long`, and `@Size(min, max)` / `@NotEmpty` on an array / `List` / `String` — read as the obvious bound and
assumed like a precondition (matched by fully-qualified name, so no dependency on the validation API; `@NotEmpty`
also implies non-null, `@Size` does not; a contradictory pair is flagged vacuous). So an annotation written for
runtime validation also discharges the compile-time obligation (Phase 128). *Out of this slice:* `Set`/`Map`
`@Size`, `@DecimalMin`/`@DecimalMax`, and call-site enforcement of the constraint (it's assumed, like `@NonNull`).

In the same vein, a **`@NonNull`-style annotation** (the NullChecker / Checker Framework / JSR-305 vocabulary —
`@NonNull` / `@NotNull` / `@Nonnull`, matched by *simple* name) on a reference parameter or field is read as a
`!= null` precondition, assumed in the body the same way `@Requires({ x != null })` would be — so `@NonNull String s`
discharges `s.length()` and `@NonNull Function g` discharges `g.apply(x)`, with NullChecker still enforcing it at
call sites (Phase 129). It does not replace `@Requires`, which additionally emits a GContracts *runtime* check.

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
