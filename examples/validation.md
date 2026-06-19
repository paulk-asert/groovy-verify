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

# Bean Validation constraints — preconditions you already wrote

A `jakarta.validation` (or legacy `javax.validation`) constraint on a parameter is read as a method-entry
**precondition** — the same posture as `@Requires`: assumed in the body, the caller's obligation. So an annotation
you wrote for *runtime* validation also discharges a *compile-time* obligation, for free. The engine matches these
by fully-qualified name and carries no dependency on the validation API.

## Numeric constraints

`@Positive` gives `x > 0`, so the modulus divisor is non-zero and the implicit divide-by-zero obligation discharges:

<!-- doclint:case jakarta-validation/positive-divisor-verifies -->
```groovy
class C { static int f(@Positive int x) { 100 % x } }
```

Drop the `@Positive` and the same body refutes with `fails on: f(0)`. `@Min(n)` / `@Max(n)` / `@Negative` /
`@PositiveOrZero` / `@NegativeOrZero` map the same way — to the obvious bound on an `int` / `long`.

The fact isn't only good for *safety*; it can discharge an explicit **postcondition** too. A `@PositiveOrZero`
input proves a `result >= 0` `@Ensures` on the way out — the validation annotation taking part in functional
verification, not just guarding it:

<!-- doclint:case jakarta-validation/positiveorzero-entails-non-negative-result -->
```groovy
class C { @Ensures({ result >= 0 }) static int f(@PositiveOrZero int n) { n } }
```

And the engine stays honest about degenerate specs: contradictory constraints (`@Positive @Negative`) are flagged
as a **vacuous precondition**, not silently passed — and under `VERIFY_EXPLAIN`, a proof that leaned on a constraint
prints `also leaned on: @Positive x`.

## Size constraints

A `@Size` / `@NotEmpty` on a collection, array, or `String` is read as a *length* fact, so an index into it is in
bounds — a `@NotEmpty List` discharges `xs[0]`:

<!-- doclint:case jakarta-validation/notempty-list-index-verifies -->
```groovy
class C { static int h(@NotEmpty List<Integer> xs) { xs[0] } }
```

The same holds for a `@Size(min = 1) int[]` (its `a[0]`) and a `@NotEmpty String` (its `s.charAt(0)`); drop the
annotation and the index refutes with `IndexOutOfBoundsException`. (`@NotNull` is read by the null layer rather than
here.)
