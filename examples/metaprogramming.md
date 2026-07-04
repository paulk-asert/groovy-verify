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

# Runtime metaprogramming, statically proved

Groovy's `ExpandoMetaClass` can reshape a type at runtime — add a property, teach an operator a new
argument type. Such code is ordinarily outside the verifier's world *twice over*: `@TypeChecked` rejects
the unresolved references before the encoder ever sees them. These examples (from the
[FizzBuzz with Groovy and emojis](https://groovy.apache.org/blog/fizzbuzz-with-groovy-and-emojis) blog
post's "Metaprogramming, handle with care" section) show the **metaprogramming pack** restoring a slim,
principled slice: when the registration is *statically visible in the same class*, it is really a pure
function definition in disguise — so it can be both type-checked and proved.

Worth pausing on the mechanism, because Groovy's type checking is extensible in **two directions** and
both are on show here. An STC extension can *strengthen* checking — groovy-verify itself is exactly that,
a type-checking extension that piles proof obligations on top of the type system. And it can *selectively
relax* checking — type what looks like uncheckable dynamic code, when there is evidence to type it from.
The pack does both at once: it blesses the metaclass references (relaxation, from the registered
closure's own signature) and then holds the result to a full functional specification (strengthening).

## Operators are methods too

The blog teaches `Integer` a `multiply(String)`, so `(it % 3) * '🥤'` yields the emoji exactly when the
remainder is zero. The registered closure is visible in the class, so the verifier inlines it at each
use site (`delegate` ↦ the receiver, `s` ↦ the argument) and proves the **exact** four-way specification:

<!-- doclint:case p209-metaprogramming/metaclass-multiply-emoji-selection-proves -->
```groovy
class C {
    static {
        Integer.metaClass.multiply = { String s -> delegate == 0 ? s : '' }
    }
    @Ensures({ result == (n % 15 == 0 ? '🥤🐝' : n % 3 == 0 ? '🥤' : n % 5 == 0 ? '🐝' : '') })
    static String fizzbuzz(int n) { (n % 3) * '🥤' + (n % 5) * '🐝' }
}
```

The class wrapper above is the corpus spelling; in a **script** the registration is simply a
top-level statement (it lands in the script's dynamic `run()`, and only the method carries
`@TypeChecked`) — no `static { }` block needed, exactly as the blog post writes it. Both forms are
pinned. Swap the two emojis in the `@Ensures` and it refutes (`counterexample: n = 5`). The natural
`n % 15 == 0` spelling proves at the default solver budget — the divisibility equivalence
`15∣n ⟺ 3∣n ∧ 5∣n` was a recorded timeout when first probed, resolved by later encoder work.

## Every Integer answers for itself

The property form adds `getFizzBuzz` to `Integer`, so `15.fizzBuzz == '🥤🐝'` and `7.fizzBuzz == 7` —
note the last arm returns the *number itself*, not a String. The verifier models that mixed arm as an
**opaque** per-receiver value (a sound over-approximation), so the specification is scoped to the String
branches by a precondition:

<!-- doclint:case p209-metaprogramming/metaclass-getter-the-numbers-answer-for-themselves -->
```groovy
class C {
    static {
        Integer.metaClass.getFizzBuzz = { ->
            (delegate % 15 == 0) ? '🥤🐝' :
            (delegate % 3  == 0) ? '🥤'   :
            (delegate % 5  == 0) ? '🐝'   : delegate
        }
    }
    @Requires({ n % 3 == 0 || n % 5 == 0 })
    @Ensures({ result == (n % 15 == 0 ? '🥤🐝' : n % 3 == 0 ? '🥤' : '🐝') })
    static String fizz(int n) { n.fizzBuzz as String }
}
```

The opacity is load-bearing, not decorative: widen the precondition to admit `n == 1` (the bare-`delegate`
arm) and any claim about the result **refuses to prove** — the verifier will not invent facts about the
branch it models opaquely.

## The gate stays shut

Everything above rests on a visible registration. Without one, the dynamic reference is exactly what
`@TypeChecked` always said it was — a compile error:

<!-- doclint:case p209-metaprogramming/unregistered-dynamic-property-stays-a-compile-error -->
```groovy
class C {
    static Object fizz(int n) { n.fizzBuzz }
}
```

The same holds when the registration lives in a *different* class (the v1 same-class visibility rule):
blessing is per-evidence, not per-runtime-possibility. Runtime-conditional registrations, categories,
`methodMissing`, and non-`Integer` receivers all remain outside — loudly.

The blog's third variant (`'🥤' * n` — plain string-repeat arithmetic, no metaprogramming at all) is also
not attempted: string repetition by a symbolic count and the `^` xor idiom are outside the modelled
fragment today.
