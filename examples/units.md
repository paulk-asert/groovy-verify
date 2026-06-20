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

# Units of measurement

The Mars Climate Orbiter was lost in 1999 to a units mismatch: one team worked in metric, the other in
US-customary, and the boundary between them carried bare numbers. groovy-verify catches that class of bug at
**compile time**, three ways — two over the JSR 385 (`javax.measure`) API people already use, and one over a
self-contained type you define yourself with nothing but a `record` and a contract. The same physical fact —
*1 km + 1 mile = 2609.344 m* — runs through all three, proved further and further from scratch.

We borrow and expand the `@Label` information-flow idea from [Smith](smith.md), but over a **free abelian group**
(`×` adds exponents) rather than a **join-semilattice**. What does that mean? We propagate a *dimension label*
through the program, check it at a forbidden point, and refute on a dimensional mismatch. Where the security lattice
only tracks merge-and-rise — taint that spreads and never cancels — the dimension group also encodes how dimensions
transform and cancel: `Area / Area` is a scalar, `Volume / Area` is a `Length`.

## Dimensions over JSR 385 — the unchecked `as Quantity<K>` cast

JSR 385 carries a quantity's *kind* in a **phantom** type parameter — `Quantity<Length>`, `Quantity<Mass>`,
`Quantity<Speed>` — so Groovy's static checker already rejects `mass.add(length)` outright. The gap is `multiply` / `divide`, where the
result kind depends on the operands: `Quantity<Length> × Quantity<Length>` is a `Quantity<Area>`, but
`Quantity<Length> × Quantity<Area>` is a `Quantity<Volume>`. The interface has only **one** method to express all of
these — erased to `Quantity<?> multiply(Quantity<?>)` — so the compiler can't give it a kind-specific return type,
and real code *casts* the result to the kind it expects. That cast is **unchecked**: name the wrong kind and nothing
complains.

groovy-verify checks it — with a small reader **dedicated to this API**, not inference from arbitrary code. It
carries a curated table mapping each JSR 385 kind to its `[Length, Mass, Time]` exponent vector — `Length` is
`(1,0,0)`, `Time` is `(0,0,1)`, `Speed` is `(1,0,-1)` — plus the rule that `×` adds those vectors and `/` subtracts
them. It recognizes the `javax.measure.Quantity` / `javax.measure.quantity.*` types by name (a dozen common kinds;
anything outside the table skips rather than guess), computes the result's vector, and compares it to the cast's
target kind:

<!-- doclint:case p131-dimensions/length-time-as-quantity-speed-verifies -->
```groovy
@Requires({ q != null && t != null })
static Quantity<Speed> v(Quantity<Length> q, Quantity<Time> t) {
    q.divide(t) as Quantity<Speed>
}
```

`length / time` is `(1,0,0) − (0,0,1) = (1,0,-1)`, which **is** `Speed`, so the cast verifies. Swap `divide` for
`multiply` and the result is `(1,0,1)` — not `Speed` — and the cast **refutes** with `Dimensional mismatch`, the
bug the generics cannot see; cast `length × length` to `Volume` and it refutes too (it is `Area`). It's pure
compile-time vector arithmetic — no SMT, just a table lookup and an add.

## Scale over JSR 385 — the *deeper* Mars bug

Dimensions alone miss the actual Mars failure: the two systems used quantities of the **same dimension** at
**different scales** — one metric, one US-customary. groovy-verify recovers a quantity's SI magnitude from how it
was built (`getQuantity`, metric prefixes, `add` / `to`), so a `getValue()` read *in a named unit* is checked
exactly — even across the metric/imperial boundary that sank the orbiter:

<!-- doclint:case p132-unit-scale/kilometre-plus-mile-in-metres-is-exact -->
```groovy
@Ensures({ result == 2609.344 })
static BigDecimal total() {
    Quantities.getQuantity(1, KILO(METRE)).add(Quantities.getQuantity(1, USCustomary.MILE)).to(METRE).getValue() as BigDecimal
}
```

`1 km + 1 mile`, normalized to metres, is exactly `2609.344` — proved over exact `BigDecimal` (rational)
arithmetic, not floating point. Read the *same* sum back in **kilometres** and claim the metre number and it
**refutes**: that is the scale bug — same dimension, wrong unit — caught. Units resolve by simple name from a
curated base-unit + metric-prefix table (`tech.units.indriya` supplies `Quantities` / `Units` / `MetricPrefix`;
`systems.uom.common.USCustomary` supplies `MILE`). Those scales are *trusted constants* — the engine asserts
them rather than running the conversion — so `UnitScaleTest` pins each one against the reference implementation
(the international mile is `1609.344 m`, not the US-survey `1609.347…`), failing loudly if a library ever
redefines a unit out from under the table.

## The same sum, as a DSL — experimental

The JSR 385 calls above are explicit on purpose. But a handful of registered Groovy **extension methods** —
`getKm(Number)`, `getMile(Number)`, … — turn `1.km` into that same `getQuantity(1, KILO(METRE))`, so the whole
scale check reads as the blog-style DSL. groovy-verify proves it just the same: an *experimental* reader recognises
the curated sugar by name (`m`, `km`, `mile`, `kg`), the same trusted-constant posture as the unit table above.

<!-- doclint:ignore experimental DSL — verified in the examples-dsl subproject, which registers the extension module; not an inline CASES snippet -->
```groovy
@Ensures({ result == 2609.344 })
static BigDecimal total() {
    (1000.m + 1.mile).value as BigDecimal
}
```

`1 km + 1 mile`, worked in metres, is exactly `2609.344` — in the prettiest possible surface syntax. And it stays
honest about the unit, which is the whole point: `(1.km + 1.mile)` is a quantity *in kilometres*, so its `.value` is
`2.609344` — claim the metre number `2609.344` there and it **refutes**, the Mars bug caught *inside* the DSL.
(Dimension is still the type system's job: `1.km + 1.kg` does not compile at all.)

Multiplication makes a subtler trap, one the type system genuinely *cannot* catch. `1.km * 1.km` is an **area** —
one square kilometre — but type erasure leaves `Quantity<?>` with a single `multiply`, so the compiler sees nothing
wrong in treating that area as if it were a length. Its `.value` is `1` (one km²); reach for the metre² magnitude
`1_000_000` and the verifier **refutes** it on the scale layer — a *value* error inside a perfectly typed program:

<!-- doclint:ignore experimental DSL — verified in the examples-dsl subproject, which registers the extension module; not an inline CASES snippet -->
```groovy
@Ensures({ result == 1_000_000 })   // refutes — (1.km * 1.km) is 1 km², its .value is 1, not the metre² number
static BigDecimal squareKm() {
    (1.km * 1.km).value as BigDecimal
}
```

You don't even need the `.value` detour: the verifier now compares **two quantities directly**, consulting *both*
the dimension and the magnitude. So the contract can be written in the most natural form — and the wrong one still
refutes, now on the **dimension**:

<!-- doclint:ignore experimental DSL — verified in the examples-dsl subproject, which registers the extension module; not an inline CASES snippet -->
```groovy
@Ensures({ result == 1.km })        // refutes — result is an area (km²), 1.km is a length; different dimensions
static Quantity squareKm() {
    1.km * 1.km
}
```

`result == 1.km` is sound because the comparison checks the **dimension first** (a compile-time exponent vector):
two quantities of different dimension are never equal — `1.m == 1.kg` *throws* at runtime — so the area-vs-length
mismatch refutes without ever looking at the value. Only when dimensions *agree* does the magnitude settle it:
`@Ensures({ result == 1.km })` over a body of `1000.m` **verifies** (same Length, both 1000 m), while `2000.m`
refutes. This is the layer the scale reader alone couldn't give — comparing `1.m` and `1.kg` on magnitude alone
would wrongly call them equal (both have SI magnitude 1).

Note the difference from `1.kg`: that one is a *dimension* mismatch the JSR 385 generics reject before the verifier
runs; the area-vs-length case above type-checks cleanly (erasure hides it) and is caught only by the verifier
tracking the dimension itself.

Division closes the loop — it's the operator that makes a **speed**. With a `getS` (seconds) suffix and a
`div(Quantity<Length>, Quantity<Time>) → Quantity<Speed>` extension, you can write the computation over named
locals, and the verifier follows the unit through them:

<!-- doclint:ignore experimental DSL — verified in the examples-dsl subproject, which registers the extension module; not an inline CASES snippet -->
```groovy
@Ensures({ result == 1.m / 1.s })   // verifies — 1 m over 1 s is 1 m/s; the dimension is Length−Time = Speed
static Quantity speed() {
    def s = 1.s
    def d = 1.m
    return d / s
}
```

The `/` subtracts the dimension exponents (`[1,0,0] − [0,0,1] = [1,0,-1]`, i.e. Speed) and divides the magnitudes;
the locals `d` and `s` are tracked back to `1.m` and `1.s`. Claim a wrong speed (`2.m / 1.s`) and it refutes on the
**magnitude**; claim the result is a plain length (`@Ensures({ result == 1.m })`) and it refutes on the
**dimension** — the `Quantity<Speed>` cast inside `div` the erased generics never re-check. One honest boundary: a
non-terminating divisor like `1.m / 3.s` (SI magnitude ⅓, which the runtime *rounds*) **skips** rather than risk an
exact-arithmetic proof the runtime wouldn't honour.

Because it needs the extension module on the classpath, this lives in its own
[`examples-dsl`](../examples-dsl) subproject — verified there. The vocabulary is a
deliberately tiny experiment; the larger point is that the JSR 385 reader is *itself* a curated recogniser, and a
future groovy-verify could let users register readers for their own.

## A bespoke units type — from a wrapped number to JSR 385's own sentence

If you don't want a units library at all, you can roll your own type — and groovy-verify reaches inside it. It
models a record's constructor and field reads as ordinary values, so it reasons about a wrapped quantity directly,
and — as we build up — about a *dimension* you encode right in the record. We'll start with the simplest form: a
single wrapped value, with `a + b` routed to the record's own `plus`. Even that verifies exactly:

<!-- doclint:case p133-record-ctor/pretty-units-operator-verifies -->
```groovy
record Length(BigDecimal metres) {
    @Ensures({ result.metres == metres + o.metres })
    Length plus(Length o) { new Length(metres + o.metres) }
}
```

<!-- doclint:case p133-record-ctor/pretty-units-operator-verifies -->
```groovy
@Ensures({ result.metres == 2609.344 })
static Length sum() {
    Length a = new Length(1000.0)
    Length b = new Length(1609.344)
    Length s = a + b
    s
}
```

A kilometre plus a mile, both in metres, is exactly `2609.344` — operator and all. Claim `2600.0` and it
**refutes**. But be clear what this proves: the **value**. A `Length` is a `BigDecimal` in a wrapper, and the only
thing stopping you adding a `Length` to a `Mass` is Groovy's static `plus(Length)` signature, not the checker —
there is no *dimension* and no *scale* inside the record. So let's put them there.

### Dimension as data

Collapse every unit into **one** type that carries a value *and* its dimension vector `(L, M, T)`. Multiplication
scales the value and **composes the exponents**:

<!-- doclint:case p142-multi-record/dimension-carrying-quantity-value-and-exponents-compose -->
```groovy
record Quantity(BigDecimal value, int l, int m, int t) {
    @Ensures({ result.value == value * o.value && result.l == l + o.l && result.m == m + o.m && result.t == t + o.t })
    Quantity multiply(Quantity o) { new Quantity(value * o.value, l + o.l, m + o.m, t + o.t) }
}
```

<!-- doclint:case p142-multi-record/dimension-carrying-quantity-value-and-exponents-compose -->
```groovy
@Ensures({ result.value == 6.0 && result.l == 2 && result.m == 0 && result.t == 0 })
static Quantity area() {
    Quantity a = new Quantity(2.0, 1, 0, 0)
    Quantity b = new Quantity(3.0, 1, 0, 0)
    Quantity s = a * b
    s
}
```

`Length(2 m, [1,0,0]) × Length(3 m, [1,0,0])` is `Area(6 m², [2,0,0])` — value and exponent vector both checked, a
wrong exponent refuting. `/` subtracts exponents the same way, and a `multiply` may even return a *different* record
(`Length × Length → Area`) when a named result type reads better. **Addition** is where the dimension earns its
keep: it may only combine *matching* dimensions, so `plus` carries a guard `@Requires({ l == o.l && … })` checked at
the `a + b` site — same-dimension `a + b` verifies, but add a Length `[1,0,0]` to a Mass `[0,1,0]` and the guard
fails, so `a + b` **refutes**. That is the units bug the *type* system can't catch (every quantity is one `Quantity`
type), and it completes the algebra from a plain record: `×`/`/` compose exponents, `+`/`−` require them equal, a
derived unit needs no new type, all machine-checked.

### JSR 385's sentence, on your own type

Give that same `Quantity` named-unit factories and the guarded `plus`, and the `1 km + 1 mile` computation runs on
it — no library:

<!-- doclint:case p144-carrier-replay/factory-operands-feed-a-guarded-operator -->
```groovy
record Quantity(BigDecimal value, int l, int m, int t) {
    @Ensures({ result.value == v * 1000.0 && result.l == 1 && result.m == 0 && result.t == 0 })
    static Quantity km(BigDecimal v) { new Quantity(v * 1000.0, 1, 0, 0) }
    @Ensures({ result.value == v * 1609.344 && result.l == 1 && result.m == 0 && result.t == 0 })
    static Quantity mile(BigDecimal v) { new Quantity(v * 1609.344, 1, 0, 0) }
    @Requires({ l == o.l && m == o.m && t == o.t })
    @Ensures({ result.value == value + o.value })
    Quantity plus(Quantity o) { new Quantity(value + o.value, l, m, t) }
}
```

A carrier-returning call is itself a value, so the factories, the guarded add, and a read-out of the result fold
into a **single fluent expression** — the very shape JSR 385 uses — with the SI magnitude read straight off the end:

<!-- doclint:case p146-chain-read-out/chain-read-out-value-verifies -->
```groovy
@Ensures({ result == 2609.344 })
static BigDecimal total() {
    Quantity.km(1.0).plus(Quantity.mile(1.0)).value
}
```

`1 km + 1 mile`, read back in metres, is exactly `2609.344` as a `BigDecimal` — no intermediate locals, a wrong
magnitude refuting, and the dimension guard still biting (a length plus a mass refutes at `.plus`, because the
factory's result is modelled right where the guard is checked). Reading the SI magnitude is exact — it is just the
stored value; reading back into a *named* unit divides by that unit's factor, which stays exact only when it
terminates (a power of ten), and skips otherwise, since Groovy rounds a non-terminating quotient.

### Units as data, too

The one thing the JSR 385 version has that the above leaves implicit is the **unit itself as a value**. Make it a
second record carrying a scale and a dimension; then `getQuantity(v, unit)` is just a factory that reads the unit's fields, and a
metric prefix is a `Unit → Unit` factory — so `KILO(METRE)` is an ordinary nested call:

<!-- doclint:case p147-units-as-data/full-jsr-385-shaped-expression -->
```groovy
record Unit(BigDecimal scale, int l, int m, int t) {
    @Ensures({ result.scale == 1.0 && result.l == 1 && result.m == 0 && result.t == 0 })
    static Unit metre() { new Unit(1.0, 1, 0, 0) }
    @Ensures({ result.scale == 1609.344 && result.l == 1 && result.m == 0 && result.t == 0 })
    static Unit mile() { new Unit(1609.344, 1, 0, 0) }
    @Ensures({ result.scale == u.scale * 1000.0 && result.l == u.l && result.m == u.m && result.t == u.t })
    static Unit kilo(Unit u) { new Unit(u.scale * 1000.0, u.l, u.m, u.t) }
}
```

<!-- doclint:case p147-units-as-data/full-jsr-385-shaped-expression -->
```groovy
@Ensures({ result.value == v * u.scale && result.l == u.l && result.m == u.m && result.t == u.t })
static Quantity of(BigDecimal v, Unit u) { new Quantity(v * u.scale, u.l, u.m, u.t) }
```

With that, the bespoke type expresses JSR 385's own sentence — `getQuantity`, a prefixed unit, `add`, a read-out —
verified end to end:

<!-- doclint:case p147-units-as-data/full-jsr-385-shaped-expression -->
```groovy
@Ensures({ result == 2609.344 })
static BigDecimal total() {
    Quantity.of(1.0, Unit.kilo(Unit.metre())).plus(Quantity.of(1.0, Unit.mile())).value
}
```

This is the bespoke twin of the JSR 385 sentence
`getQuantity(1, KILO(METRE)).add(getQuantity(1, USCustomary.MILE)).to(METRE).getValue()` — over a type *you* defined,
with **no units library and no special engine support**: it falls straight out
of the multi-component record, carrier-typed factory arguments, and the read-out. (Reading back out in a *non-SI*
named unit divides by a now-*symbolic* scale, so that direction skips — like any non-terminating divisor; the SI
`.value` read is exact.)

## What is proven, and what isn't

- **Exact, not floating-point** — magnitudes are exact `BigDecimal` / rationals, so `2609.344` means `2609.344`.
- **Each is a real proof — of a *different* thing** — a wrong **dimension** refutes (at the JSR 385 cast, or as an
  explicit exponent vector in a bespoke `Quantity`), a wrong **scale** refutes (the value, over JSR 385), a wrong
  **value/total** refutes (the bespoke operator and read-out); none passes by being un-modelled. And once the unit
  itself is *data*, that bespoke record expresses JSR 385's own `getQuantity(…).add(…).getValue()` sentence over a
  type you defined.
- **Same reasoning, different carrier** — the label lives somewhere different each time: an `@Label` annotation in
  Smith's information flow, a *phantom* `Quantity<K>` type parameter over JSR 385 (compile-time only — erased at
  runtime, so the verifier recovers it from the declared types), and a plain `(l, m, t)` record field in the bespoke
  type (you write the exponents; the verifier reads them as data). The "propagate a label, check it at a forbidden
  point" shape never changes — only where the label is stored does.
- **Honest skips** — affine units (°C / °F carry an *offset*, not a pure scale), a read-out by a *non-terminating*
  divisor (Groovy rounds it — unsound to model exactly), and any unit or kind outside the curated tables, all skip
  loudly rather than guess.

The full capability rows are in **[CAPABILITIES.md](../CAPABILITIES.md)** (Phases 131–133, 142, 142b, 142c,
143–147).
