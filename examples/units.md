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
self-contained type you define yourself with nothing but a `record` and a contract.

These are the second face of the `@Label` information-flow lattice from [Smith](smith.md): the same shape —
*propagate a label through the program, check it at a forbidden point* — but over a **free abelian group** (`×`
adds exponents) rather than a join-semilattice.

## Dimensions over JSR 385 — the unchecked `as Quantity<K>` cast

JSR 385 carries a quantity's *kind* in its generic type — `Quantity<Length>`, `Quantity<Speed>` — and Groovy's
static checker already rejects `mass.add(length)`. But `multiply` / `divide` return `Quantity<?>`, the result-kind
the type system **can't** infer, so real code *casts* the result — and that cast is unchecked. groovy-verify
computes the result's dimension as a `[Length, Mass, Time]` exponent vector and checks the cast:

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
compile-time vector arithmetic — no SMT — over the `javax.measure.Quantity` / `javax.measure.quantity.*` types.

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

## A bespoke units type — a record, a contract, and `+`

When you do not want a units library at all, a units type is just a **record plus a contract** — no JSR 385, no
extension modules, no `use()` categories (which `@TypeChecked` rejects outright). groovy-verify models a
single-component record's constructor as a value, so `new Length(v).metres` round-trips, and routes `a + b` to
the record's own `plus`:

<!-- doclint:case p133-record-ctor/pretty-units-operator-verifies -->
```groovy
record Length(BigDecimal metres) {
    @Ensures({ result.metres == metres + o.metres })
    Length plus(Length o) { new Length(metres + o.metres) }
}
```

`+` dispatches to `plus`, whose `@Ensures` is resolved on the *receiver's* type and assumed at the call — so the
pretty form verifies exactly:

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

A kilometre plus a mile, both in metres, is exactly `2609.344` — operators and all, verified. Claim `2600.0` and
it **refutes**. A **guarded** operator routes too and stays sound: the precondition hook fires for `a + b`, checks
`plus`'s `@Requires` at the site (a violated guard refutes), and only then is the `@Ensures` assumed — which is
exactly what makes the dimension-checked addition below work.

Be clear about what `plus` proves, though: the **value**. A `Length` is a `BigDecimal` in a wrapper — the
verifier checks the magnitude arithmetic, and the only thing stopping you adding a `Length` to a `Mass` is
Groovy's static `plus(Length)` signature, not the checker. There is no *dimension* and no *scale* inside the
record — those are the JSR 385 sections above.

It does go beyond a named number in one real way, though: a **type-changing** operator works. Give `Length` a
`multiply` that returns a *different* record type (`record Area(BigDecimal squareMetres) {}`) and `*` routes to it
— the actual dimensional algebra, `Length × Length → Area`, with the area's value proved:

<!-- doclint:case p133-record-ctor/type-changing-operator-length-length-area -->
```groovy
record Length(BigDecimal metres) {
    @Ensures({ result.squareMetres == metres * o.metres })
    Area multiply(Length o) { new Area(metres * o.metres) }
}
```

<!-- doclint:case p133-record-ctor/type-changing-operator-length-length-area -->
```groovy
@Ensures({ result.squareMetres == 6.0 })
static Area area() {
    Length a = new Length(2.0)
    Length b = new Length(3.0)
    Area s = a * b
    s
}
```

`2 m × 3 m == 6 m²`, verified — and a wrong area refutes. So far each unit has been its own record. The fullest
form collapses them all into **one** type: a record carrying a value *and its dimension vector* `(L, M, T)`, where
`×` scales the value and **composes the exponents**:

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

`Length(2 m, [1,0,0]) × Length(3 m, [1,0,0])` is `Area(6 m², [2,0,0])` — the dimension *composes* under `×`, value
and exponent vector both checked, a wrong exponent refuting. `/` subtracts exponents the same way. **Addition**
completes the algebra, and it's where the dimension check earns its keep: `+` may only combine *matching*
dimensions, so guard `plus` and the guard is checked at the `a + b` site:

<!-- doclint:case p142-multi-record/dimensional-addition-same-dimension-verifies -->
```groovy
record Quantity(BigDecimal value, int l, int m, int t) {
    @Requires({ l == o.l && m == o.m && t == o.t })
    @Ensures({ result.value == value + o.value && result.l == l })
    Quantity plus(Quantity o) { new Quantity(value + o.value, l, m, t) }
}
```

Same-dimension `a + b` verifies; add a Length `[1,0,0]` to a Mass `[0,1,0]` and the guard `l == o.l` fails, so
`a + b` **refutes** — the units bug the *type* system can't catch, since every quantity is one `Quantity` type.
That's the full Dafny dimension-ADT algebra reached from the bespoke-record side: `×`/`/` compose exponents,
`+`/`−` require them equal, a derived unit needs no new type, and the whole thing is machine-checked.

**Conversion** works on the construct-to-SI side: a `Length.km(v)` factory scales a value into metres
(`new Length(v * 1000)`), and at the use site the converted value is verified — `Length.km(2).metres == 2000`, a
wrong value refuting — with two constructions of the same physical length comparing **equal**
(`Length.km(1) == new Length(1000)`, by datatype equality). The *read-out* direction (divide back into a unit,
`metres / 1000`) now verifies too — `BigDecimal` division is modelled exactly **when the divisor terminates** (a
power of ten, or any product of 2s and 5s), which covers metric read-outs; a *non-terminating* divisor (`/3`,
`/60`, a mile) still skips loudly, because Groovy rounds it and exact rational division would be unsound. (A
record's own conversion methods are verified only if the record itself carries `@TypeChecked`; at the *use* site
they hold.)

Factories and the guarded operator **compose**: build each operand with a named-unit factory and add them, and
the whole `1 km + 1 mile` runs on the bespoke type — the same physical computation as the JSR 385 version in §2,
with no library at all:

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

<!-- doclint:case p144-carrier-replay/factory-operands-feed-a-guarded-operator -->
```groovy
@Ensures({ result.value == 2609.344 })
static Quantity total() {
    Quantity a = Quantity.km(1.0)
    Quantity b = Quantity.mile(1.0)
    Quantity s = a + b
    s
}
```

`Quantity.km(1) + Quantity.mile(1)`, in metres, is exactly `2609.344` — named-unit factories and a guarded
operator, all checked. The dimension guard still fires across the factory boundary: build a length and a mass and
the `l == o.l` precondition **refutes** at `a + b`. (This works because a factory call's result is modelled where
the operator's precondition is checked, rather than treated as an opaque value — so the operands keep their real
`Quantity` identity through the check.)

And the operands need not be locals: a carrier-returning call is a value in expression position, so the whole
thing collapses to a **single fluent chain** — the receiver *and* the argument are factory calls, the shape JSR 385
itself uses:

<!-- doclint:case p145-carrier-chain/single-expression-chain-verifies -->
```groovy
@Ensures({ result.value == 2609.344 })
static Quantity total() {
    Quantity.km(1.0).plus(Quantity.mile(1.0))
}
```

Each nested call is modelled into a fresh `Quantity` constrained by its `@Ensures`, so `result.value` is exactly
`2609.344` — a wrong total refutes the postcondition, and the guarded `.plus` still discharges over the real
argument: chain a length and a mass and the `l == o.l` precondition **refutes**.

And the read-out joins the chain: a component read on the result reads the SI magnitude straight off it — the
terminal step of the JSR 385 shape (`…​.to(METRE).getValue()`), here a bare `.value`:

<!-- doclint:case p146-chain-read-out/chain-read-out-value-verifies -->
```groovy
@Ensures({ result == 2609.344 })
static BigDecimal total() {
    Quantity.km(1.0).plus(Quantity.mile(1.0)).value
}
```

The whole `1 km + 1 mile`, read back in metres, is exactly `2609.344` as a `BigDecimal` — no intermediate locals,
a wrong magnitude refuting. (Each maximal carrier call is hoisted to a temporary so the `.value` read becomes an
ordinary component read; it composes with further decimal arithmetic and works as a local RHS too.)

The last step to JSR 385's *literal* shape is to make a **unit itself a value**: a second record carrying a scale
and a dimension. Then `getQuantity(v, unit)` is just a factory that reads the unit's fields, and a metric prefix is
a `Unit → Unit` factory — so `KILO(METRE)` is an ordinary nested call:

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
and it verifies end to end:

<!-- doclint:case p147-units-as-data/full-jsr-385-shaped-expression -->
```groovy
@Ensures({ result == 2609.344 })
static BigDecimal total() {
    Quantity.of(1.0, Unit.kilo(Unit.metre())).plus(Quantity.of(1.0, Unit.mile())).value
}
```

This is the bespoke twin of `getQuantity(1, KILO(METRE)).add(getQuantity(1, USCustomary.MILE)).to(METRE).getValue()`
from §2 — but over a type *you* defined, with **no units library and no new engine support**: it falls straight
out of the multi-component record, carrier-typed factory arguments, and the read-out. A wrong total refutes; and
the dimension guard still bites — build one quantity in `metre` and another in `gram` and the `l == o.l`
precondition **refutes**. (Reading back out in a *non-SI* named unit divides by the unit's scale, which is now a
*symbolic* value rather than a literal — so that direction skips, like any non-terminating divisor; the SI `.value`
read above is exact.)

## What is proven, and what isn't

- **Exact, not floating-point** — magnitudes are exact `BigDecimal` / rationals, so `2609.344` means `2609.344`.
- **Each is a real proof — of a *different* thing** — a wrong **dimension** refutes (§1, at the cast; or §3, as an
  explicit exponent vector in a `Quantity` record), a wrong **scale** refutes (§2, the value over JSR 385), a
  wrong **value/total** refutes (§3, the operator); none passes by being un-modelled. The JSR 385 layers read the
  dimension from the *type*; the bespoke record reasons about whatever you make *data* — a bare `Length` is just a
  value (its `no Length + Mass` safety is Groovy's static types), while a `Quantity(value, L, M, T)` carries and
  composes its dimension explicitly.
- **Honest skips** — affine units (°C / °F carry an *offset*, not a pure scale), a read-out by a *non-terminating*
  divisor (Groovy rounds it — unsound to model exactly), and any unit or kind outside the curated tables, all skip
  loudly rather than guess.

The full capability rows are in **[CAPABILITIES.md](../CAPABILITIES.md)** (Phases 131–133, 142, 142b, 142c,
143–147).
