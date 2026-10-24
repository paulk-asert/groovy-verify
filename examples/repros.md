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

# Failing calls you can run — and what it means when there isn't one

A refutation ends with the call that breaks the claim: `fails on: f(3)`. That line is meant to be **run** — paste it
into a test, or set `VERIFY_REFUTATION=junit` (or `assert`, `spock`) and the diagnostic renders the test for you. So
it has to be a call that really fails, not just values the solver liked.

Often the solver's values aren't a run at all. A loop's checks start from *any* state its invariant allows; a catch
from any state the try block may have left; an unmodelled value is whatever the solver picked. Calls built from those
states were frequently ones that pass. So when the state isn't one a run reaches, the verifier looks for one that is —
a run from entry, along the program's first iterations and real ways in — and shows its call. When none fails, it
shows **no call**, and says why. That note is usually the most useful line in the diagnostic: it tells you what to
fix.

The cases below come in pairs: a real bug, whose call fails, beside its twin, whose call would have passed.

## After a loop: a weak invariant, or a real bug

The postcondition after a loop is checked from any state that satisfies the invariant and the negated guard. Here
the invariant `s <= i` is true but too weak to give `result == n`:

<!-- doclint:case p385-post-loop-call/a-weak-invariant-s-refutation-shows-no-call -->
```groovy
class A {
    @Requires({ n >= 0 })
    @Ensures({ result == n })
    static int f(int n) {
        int s = 0
        int i = 0
        @Invariant({ 0 <= i && i <= n && s <= i })
        @Decreases({ n - i })
        while (i < n) {
            s = s + 1
            i = i + 1
        }
        return s
    }
}
```

Every run returns `n`, so there is no failing call to show — and the note says what to do instead:

<!-- doclint:diagnostic p385-post-loop-call/a-weak-invariant-s-refutation-shows-no-call -->
```
[Static type checking] - Cannot prove postcondition of f holds on this return path … no failing call: the failure
is in a state the loop's invariant allows when it exits, not one reached from entry, and no run of its first eight
iterations gets there (the invariant may be too weak for the postcondition)
```

Strengthen it to `s == i` and the proof goes through. Break the body instead — skip an increment at `i == 2` — and
the same invariant is now a real bug, with a run that shows it:

<!-- doclint:case p385-post-loop-call/a-real-bug-keeps-a-call-that-fails -->
```groovy
while (i < n) {
    if (i != 2) s = s + 1
    i = i + 1
}
```

<!-- doclint:diagnostic p385-post-loop-call/a-real-bug-keeps-a-call-that-fails -->
```
[Static type checking] - Cannot prove postcondition of f holds on this return path … fails on: f(3)
```

`f(3)` returns 2. Before, both versions showed `fails on: f(0)` — a call that returns 0, as it should.

## An invariant that isn't preserved — or isn't inductive

Preservation is checked from any state the invariant allows at an iteration's start. An invariant can hold on every
run and still not be *inductive*: `x <= 10` here is true for all `n <= 3`, but one more pass from `x == 10` breaks it.

<!-- doclint:case p392-preservation-witness/a-true-invariant-that-isn-t-inductive-no-call -->
```groovy
class A {
    @Requires({ n >= 0 && n <= 3 })
    static int f(int n) {
        int x = 0
        int i = 0
        @Invariant({ 0 <= i && i <= n && x <= 10 })
        @Decreases({ n - i })
        while (i < n) {
            x = x + 1
            i = i + 1
        }
        return x
    }
}
```

<!-- doclint:diagnostic p392-preservation-witness/a-true-invariant-that-isn-t-inductive-no-call -->
```
[Static type checking] - Cannot prove loop invariant is preserved by the loop body in f … no failing call: the
invariant is broken from a state it allows at an iteration's start, not one reached from entry, and no run of the
loop's first eight iterations breaks it (it may hold on every run without being inductive: strengthen it)
```

The fix is to say what the loop actually keeps — `x == i`. Where the invariant really is broken, the call is the first
run that breaks it, not the first input the solver tries:

<!-- doclint:case p392-preservation-witness/a-broken-invariant-the-first-run-that-breaks-it -->
```groovy
@Invariant({ 0 <= i && i <= n && s <= 2 })
@Decreases({ n - i })
while (i < n) {
    s = s + 1
    i = i + 1
}
```

<!-- doclint:diagnostic p392-preservation-witness/a-broken-invariant-the-first-run-that-breaks-it -->
```
[Static type checking] - Cannot prove loop invariant is preserved by the loop body in f … fails on: f(3)
```

`f(1)` would pass — `s` is only 1 — and was what used to be shown. The third iteration takes `s` to 3.

## A nested loop's entry

A nested loop's invariant must hold each time the inner loop starts, which is checked from any state the *outer*
loop's invariant allows. Here the outer invariant says nothing about `s`, so the check can't rule out `s == 4` at the
inner entry — but with `n <= 1`, no run gets there:

<!-- doclint:case p397-deep-nesting/two-levels-a-nested-entry-no-run-breaks-shows-no-call -->
```groovy
class A {
    @Requires({ n >= 0 && n <= 1 })
    static int f(int n) {
        int s = 0
        int i = 0
        @Invariant({ 0 <= i && i <= n })
        @Decreases({ n - i })
        while (i < n) {
            int k = 0
            @Invariant({ 0 <= k && k <= n && s <= 3 })
            @Decreases({ n - k })
            while (k < n) {
                s = s + 1
                k = k + 1
            }
            i = i + 1
        }
        return s
    }
}
```

<!-- doclint:diagnostic p397-deep-nesting/two-levels-a-nested-entry-no-run-breaks-shows-no-call -->
```
[Static type checking] - Cannot prove loop invariant holds on entry in f … no failing call: the inner loop's entry is
checked in a state the outer loop's invariant allows, not one reached from entry, and no run of the first iterations
breaks the inner invariant there (the outer invariant may be too weak to establish it)
```

The outer loop needs to carry what the inner one assumes — here, a bound on `s` in terms of `i`. Without the `n <= 1`
bound, and three loops deep, the same shape is a real bug, and the run that reaches it is found through every
enclosing loop:

<!-- doclint:case p397-deep-nesting/an-innermost-invariant-s-entry-broken-by-a-real-run -->
```groovy
while (j < n) {
    int k = 0
    @Invariant({ 0 <= k && k <= n && s <= 3 })
    @Decreases({ n - k })
    while (k < n) {
        s = s + 1
        k = k + 1
    }
    j = j + 1
}
```

<!-- doclint:diagnostic p397-deep-nesting/an-innermost-invariant-s-entry-broken-by-a-real-run -->
```
[Static type checking] - Cannot prove loop invariant holds on entry in f … fails on: f(4)
```

With `n == 4`, the first middle iteration's inner loop leaves `s == 4` for the second's entry.

## Inside a catch

A catch is entered by a throw, so its failing call has to throw first. Here the catch runs only when `d == 0`, and
then fails only when `n == 0` too:

<!-- doclint:case p387-catch-witness/a-division-in-the-try-throws-into-the-catch -->
```groovy
class A {
    static int f(int n, int d) {
        try {
            return 10.intdiv(d)
        } catch (ArithmeticException e) {
            return 10.intdiv(n)
        }
    }
}
```

<!-- doclint:diagnostic p387-catch-witness/a-division-in-the-try-throws-into-the-catch -->
```
[Static type checking] - Possible ArithmeticException: Division by zero … fails on: f(0, 0)
```

A postcondition on a path through a catch works the same way. Each return gets its own run — the try's (a negative
divisor returns a negative quotient) and the catch's (the divisor that throws):

<!-- doclint:case p387-catch-witness/a-postcondition-on-the-catch-s-return-a-call-that-throws-there -->
```groovy
class A {
    @Ensures({ result >= 0 })
    static int f(int d) {
        try {
            return 10.intdiv(d)
        } catch (ArithmeticException e) {
            return -1
        }
    }
}
```

<!-- doclint:diagnostic p387-catch-witness/a-postcondition-on-the-catch-s-return-a-call-that-throws-there -->
```
[Static type checking] - Cannot prove postcondition of f holds on this return path … fails on: f(-5) … Cannot prove
postcondition of f holds on this return path … fails on: f(0)
```

The catch's report used to show `fails on: f(-2147483648)` — `10.intdiv(-2147483648)` is 0, which doesn't throw, and
returns 0.

## A value the verifier doesn't model

Sometimes the claim rests on a value the verifier can't compute — here, the size of a decimal range's list. The
claim isn't proved, and the solver's guess at the size (`2`) is no run's, so no call is shown:

<!-- doclint:case p386-fresh-collection/a-failure-resting-on-an-unmodelled-local-shows-no-call -->
```groovy
class A {
    static void f() {
        List r = (4.5..6.5).toList()
        assert r.size() == 3
    }
}
```

<!-- doclint:diagnostic p386-fresh-collection/a-failure-resting-on-an-unmodelled-local-shows-no-call -->
```
[Static type checking] - Assertion may not hold: (r.size() == 3) … no failing call: the failure rests on r, a value
the verifier doesn't model (an unmodelled call or expression), so no run is known to reach it
```

Here the assert is in fact true — `(4.5..6.5).toList()` is `[4.5, 5.5, 6.5]` — and the note is the hint that the
verifier, not the code, ran out of road.

## Reading the notes

| The note says | What it means | What to do |
|---|---|---|
| the loop's invariant allows when it exits … may be too weak for the postcondition | no run reaches the bad exit state | strengthen the invariant (say what the loop keeps) |
| broken from a state it allows at an iteration's start … without being inductive | the invariant holds on every run but isn't inductive | strengthen it, or check the iterations past the first eight |
| the inner loop's entry … the outer invariant may be too weak | the outer loop doesn't carry what the inner one assumes | add the fact to the outer invariant |
| in a catch, in a state the try block may leave | no throw that enters the catch is followed exactly | expected for a try with a call; refactor if the catch matters |
| rests on … a value the verifier doesn't model | the claim depends on something outside the fragment | bind it to a modelled form, or accept the warning |
| what a statement writes inside it | a nested write, a finally or a fall-through was havocked | split the statement if the call matters |

The search is bounded: a run whose failure needs more than eight iterations of a loop, or many iterations of an outer
one, is outside it, and its call is withheld rather than found. A withheld call never means the check passed — the
warning stands; only the call is missing.
