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
it **refutes**. This is sound *by restriction*: the rewrite of `a + b` → `a.plus(b)` fires only when `plus` has no
`@Requires` (the operator site is a `BinaryExpression`, so the precondition hook can't check a guard there), so a
guarded operator stays a loud skip rather than an unchecked assumption.

## What is proven, and what isn't

- **Exact, not floating-point** — magnitudes are exact `BigDecimal` / rationals, so `2609.344` means `2609.344`.
- **The cast / the value / the operator are real proofs** — a wrong dimension, a wrong scale, or a wrong total
  each refutes; nothing passes by being un-modelled.
- **Honest skips** — `Length × Length` (Area needs a multi-component record), a `@Requires`-guarded operator,
  affine units (°C / °F carry an *offset*, not a pure scale), and any unit or kind outside the curated tables all
  skip loudly rather than guess.

The full capability rows are in **[CAPABILITIES.md](../CAPABILITIES.md)** (Phases 131–133).
