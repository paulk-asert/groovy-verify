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

# LemmaScript examples

[LemmaScript](https://lemmascript.org/) is TypeScript with contracts written in `//@` comments. The code stays
ordinary TypeScript, and `lsc check` proves the contracts by translating them to Dafny (and, for some examples,
Lean). Its pitch is close to this project's: the specification is the part a person reviews, and an agent may
write the implementation, because the build rejects one that doesn't meet it.

This page ports the examples from LemmaScript's front page and from its
[examples folder](https://github.com/midspiral/LemmaScript/tree/main/examples), structure for structure. Each
Groovy block is linked to a test case that runs on every build. The TypeScript originals are shown for comparison
and are © their authors, used under LemmaScript's MIT licence.

## Reading LemmaScript as Groovy

| LemmaScript | Groovy |
|---|---|
| `//@ contract Finds target in a sorted array…` | a groovydoc comment, `/** Finds target in a sorted array… */` |
| `//@ requires`, `//@ ensures` | `@Requires({ … })`, `@Ensures({ … })` |
| `//@ invariant`, `//@ decreases` (inside the loop) | `@Invariant({ … })`, `@Decreases({ … })` on the loop |
| `\result` | `result` |
| `forall(k, 0 <= k && k < n ==> P)` | `(0..<n).every { P }` |
| `exists(k, 0 <= k && k < n && P)` | `(0..<n).any { P }` |
| `==>` | `==>` |
| `sorted(arr)` | `arr.isSorted()` |
| `//@ type i nat` | `0 <= i` in an invariant |
| `break` plus `//@ done_with` | `break` (the exit condition needs no annotation) |

LemmaScript's `//@ contract` line is a plain-English statement of intent that sits beside the formal contract, so a
reviewer can check one against the other. Groovy doesn't have an annotation for that yet, so the ports carry the
same sentence as a groovydoc comment.

Two differences come from the languages rather than the tools. A TypeScript `number[]` or `string` parameter
can't be `null`, but a Groovy reference can, so the ports that dereference a reference parameter state
`!= null` in their precondition. And LemmaScript's `number` is a mathematical integer in its Dafny model, while
Groovy's `int` is 32 bits. The proofs here use mathematical integers too unless a method opts into
`@CheckOverflow`, which the [zigzag](#zigzag-encoding) example uses to find what the unbounded model can't see.

## The front page

### Binary search

The front page's example splits the work in two: the specification is what you review, and the implementation is
what the agent writes.

```ts
//@ contract Finds target in a sorted array, or reports -1.
//@ requires sorted(arr)
//@ ensures  \result >= -1 && \result < arr.length
//@ ensures  \result >= 0 ==> arr[\result] === target
//@ ensures  \result === -1 ==> forall(k, 0 <= k && k < arr.length ==> arr[k] !== target)
```

The Groovy keeps LemmaScript's invariants, including the inclusive `hi`, and its `break`. LemmaScript also states
the exit condition with `//@ done_with`. groovy-verify needs no counterpart: it checks the code after the loop
from every way out, the normal exit (the invariant plus the negated guard) and the state at each `break`. The
iteration that breaks doesn't have to shrink `[lo, hi]` or re-establish the invariant:

<!-- doclint:case lemmascript-port/binarysearch -->
```groovy
/** Finds target in a sorted array, or reports -1. */
@Requires({ arr.isSorted() })
@Ensures({ result >= -1 && result < arr.length })
@Ensures({ result >= 0 ==> arr[result] == target })
@Ensures({ result == -1 ==> (0..<arr.length).every { arr[it] != target } })
static int binarySearch(int[] arr, int target) {
    int lo = 0
    int hi = arr.length - 1
    int result = -1
    @Invariant({ 0 <= lo && lo <= arr.length && -1 <= hi && hi < arr.length })
    @Invariant({ (0..<lo).every { arr[it] != target } })
    @Invariant({ (hi + 1..<arr.length).every { arr[it] != target } })
    @Invariant({ result == -1 || (result >= 0 && result < arr.length && arr[result] == target) })
    @Decreases({ hi - lo + 1 })
    while (lo <= hi) {
        int mid = lo + (hi - lo).intdiv(2)
        if (arr[mid] == target) { result = mid; break }
        else if (arr[mid] < target) lo = mid + 1
        else hi = mid - 1
    }
    return result
}
```

Remove `arr.isSorted()` and the proof fails where it should: the invariant that nothing left of `lo` matches is
no longer preserved when the search narrows.

### Pruning a sliding window

```ts
//@ contract Keeps only the requests still inside the sliding time window.
export function pruneWindow(log: number[], now: number, W: number): number[] {
  //@ requires forall(k, 0 <= k && k < log.length ==> log[k] <= now)
  //@ decreases log.length
  //@ ensures \result.length <= log.length
  //@ ensures forall(k, 0 <= k && k < \result.length ==> now - W < \result[k] && \result[k] <= now)
  if (log.length === 0) {
    return [];
  }
  const rest = pruneWindow(log.slice(1), now, W);
  if (log[0] > now - W) {
    return [log[0], ...rest];
  }
  return rest;
}
```

This one only partly ports. Recursing over `log.drop(1)` and rebuilding with `[log[0]] + rest` is outside the
verifier's fragment, and so is the idiomatic `log.findAll { it > now - w }`. As a loop that appends with `add`,
the size bound proves:

<!-- doclint:case lemmascript-port/prunewindow-size-bound -->
```groovy
/** Keeps only the requests still inside the sliding time window. */
@Requires({ log != null })
@Ensures({ result.size() <= log.size() })
static List<Integer> pruneWindow(List<Integer> log, int now, int w) {
    List<Integer> out = []
    int i = 0
    @Invariant({ 0 <= i && i <= log.size() && out.size() <= i })
    @Decreases({ log.size() - i })
    while (i < log.size()) {
        if (log[i] > now - w) out.add(log[i])
        i = i + 1
    }
    return out
}
```

The second postcondition, that every kept entry is inside the window, needs facts about the elements `add`
appended, and list-building loops only track the size today.

### Splitting money

The front page's second story is an agent's first attempt at splitting a total across weights: it floors each
share, so `allocate(10, [1, 1, 1])` returns `[3, 3, 3]` and a cent vanishes. The fix hands the leftover back out.

```ts
//@ ensures sum(\result) === total  // must sum to the whole
function allocate(total, weights) {
  const W = sum(weights);
  const result = weights.map(w => Math.floor(total * w / W));
  let left = total - sum(result);  // the leftover, lost to flooring
  for (let k = 0; left > 0; k++, left--)
    result[k] += 1;           // hand them back out
  return result;
}
```

This is beyond the verifier today, in both directions. Each share is `total * w / W`, a product of two
variables divided by a third, and the solver times out on that nonlinear arithmetic. It can't refute the first
attempt any more than it can prove the fix. The fix also needs a lemma that the leftover is smaller than the
number of weights, so that `result[k]` stays in bounds.

## From the examples folder

### Clamp

<!-- doclint:case lemmascript-port/clamp -->
```groovy
/** Clamps x into the closed range [lo, hi]. */
@Requires({ lo <= hi })
@Ensures({ result >= lo && result <= hi })
static int clamp(int x, int lo, int hi) {
    int result = x
    if (result < lo) result = lo
    if (result > hi) result = hi
    return result
}
```

### Linear search

Also verbatim, `break` and all. The `result` set just before the `break` is what the code after the loop
returns:

<!-- doclint:case lemmascript-port/linearsearch -->
```groovy
/** Returns the first index of target, or -1 when it is absent. */
@Ensures({ result >= -1 && result < arr.length })
@Ensures({ result >= 0 ==> arr[result] == target })
@Ensures({ result == -1 ==> (0..<arr.length).every { arr[it] != target } })
static int linearSearch(int[] arr, int target) {
    int i = 0
    int result = -1
    @Invariant({ 0 <= i && i <= arr.length })
    @Invariant({ (0..<i).every { arr[it] != target } })
    @Invariant({ result == -1 || (result >= 0 && result < arr.length && arr[result] == target) })
    @Decreases({ arr.length - i })
    while (i < arr.length) {
        if (arr[i] == target) { result = i; break }
        i = i + 1
    }
    return result
}
```

### Largest element

LemmaScript's `forall` and `exists` pair becomes `.every` and `.any`:

<!-- doclint:case lemmascript-port/maxelement -->
```groovy
/** Returns the largest element of a non-empty array. */
@Requires({ arr.length > 0 })
@Ensures({ (0..<arr.length).every { arr[it] <= result } })
@Ensures({ (0..<arr.length).any { arr[it] == result } })
static int maxElement(int[] arr) {
    int max = arr[0]
    int i = 1
    @Invariant({ 1 <= i && i <= arr.length })
    @Invariant({ (0..<i).every { arr[it] <= max } })
    @Invariant({ (0..<i).any { arr[it] == max } })
    @Decreases({ arr.length - i })
    while (i < arr.length) {
        if (arr[i] > max) max = arr[i]
        i = i + 1
    }
    return max
}
```

### Is it sorted?

A boolean result specified in both directions, its flag set just before the `break`:

<!-- doclint:case lemmascript-port/issorted -->
```groovy
/** Reports whether a non-empty array is in ascending order. */
@Requires({ arr.length > 0 })
@Ensures({ result ==> (0..<arr.length - 1).every { arr[it] <= arr[it + 1] } })
@Ensures({ !result ==> (0..<arr.length - 1).any { arr[it] > arr[it + 1] } })
static boolean isSorted(int[] arr) {
    boolean result = true
    int i = 0
    @Invariant({ 0 <= i && i < arr.length })
    @Invariant({ result ==> (0..<i).every { arr[it] <= arr[it + 1] } })
    @Invariant({ !result ==> (0..<arr.length - 1).any { arr[it] > arr[it + 1] } })
    @Decreases({ arr.length - i })
    while (i + 1 < arr.length) {
        if (arr[i] > arr[i + 1]) { result = false; break }
        i = i + 1
    }
    return result
}
```

### Sum

LemmaScript defines a recursive `sumTo(arr, i)` helper for its invariant. Groovy's own range sum
`arr[0..<i].sum()` already means that:

<!-- doclint:case lemmascript-port/arraysum -->
```groovy
/** Sums the elements of a non-empty array. */
@Requires({ arr.length > 0 })
@Ensures({ result == arr.sum() })
static int arraySum(int[] arr) {
    int sum = 0
    int i = 0
    @Invariant({ 0 <= i && i <= arr.length })
    @Invariant({ i == 0 ? sum == 0 : sum == arr[0..<i].sum() })
    @Decreases({ arr.length - i })
    while (i < arr.length) { sum = sum + arr[i]; i = i + 1 }
    return sum
}
```

### Swap

TypeScript's `let result = arr` aliases the input, so LemmaScript's postcondition reads the original values
implicitly. Groovy's `old` names the state on entry explicitly:

<!-- doclint:case lemmascript-port/swap -->
```groovy
/** Swaps two elements of an array in place. */
@Requires({ 0 <= i && i < arr.length && 0 <= j && j < arr.length })
@Ensures({ result.length == arr.length && result[i] == old.arr[j] && result[j] == old.arr[i] })
static int[] swap(int[] arr, int i, int j) {
    int tmp = arr[i]
    arr[i] = arr[j]
    arr[j] = tmp
    return arr
}
```

### leftPad

LemmaScript's version of the original npm left-pad, which its comments trace back to the 2014 source:

```ts
function leftPad(str: string, len: number, ch: string): string {
  //@ type len nat
  //@ type i nat
  //@ requires ch.length === 1
  //@ ensures str.length >= len ==> \result === str
  //@ ensures str.length < len ==> \result.length === len
  let result = str;
  len = len - str.length;
  let i = 0;
  while (i < len) {
    //@ invariant result.length === str.length + i
    //@ invariant i >= 0
    //@ invariant len > 0 ==> i <= len
    //@ invariant len <= 0 ==> result === str
    //@ decreases len - i
    result = ch + result;
    i = i + 1;
  }
  return result;
}
```

The Groovy names the shortfall `n` rather than reusing the parameter, because a contract reads a parameter's
current value. Its invariants are exactly the original's. `n` never changes inside the loop, so its value from
before the loop, `len - str.length()`, holds throughout without being restated, as it does in Dafny.

<!-- doclint:case lemmascript-port/leftpad -->
```groovy
/** Pads str on the left with ch until it is len characters long. */
@Requires({ str != null && ch != null && ch.length() == 1 && len >= 0 })
@Ensures({ str.length() >= len ==> result == str })
@Ensures({ str.length() < len ==> result.length() == len })
static String leftPad(String str, int len, String ch) {
    String result = str
    int n = len - str.length()
    int i = 0
    @Invariant({ result.length() == str.length() + i && i >= 0 })
    @Invariant({ n > 0 ==> i <= n })
    @Invariant({ n <= 0 ==> result == str })
    @Decreases({ n - i })
    while (i < n) { result = ch + result; i = i + 1 }
    return result
}
```

### Duplicates

LemmaScript's `containsDuplicate` remembers seen values in a `Set`. This port is the nested-loop form. Its outer
invariant says no pair starting before `i` is a duplicate, and its inner invariant says `nums[i]` differs from
everything checked so far:

<!-- doclint:case lemmascript-port/containsduplicate -->
```groovy
/** Reports whether any value occurs twice. */
@Ensures({ !result ==> (0..<nums.length).every { int a -> (a + 1..<nums.length).every { int b -> nums[a] != nums[b] } } })
static boolean containsDuplicate(int[] nums) {
    int i = 0
    @Invariant({ 0 <= i && i <= nums.length })
    @Invariant({ (0..<i).every { int a -> (a + 1..<nums.length).every { int b -> nums[a] != nums[b] } } })
    @Decreases({ nums.length - i })
    while (i < nums.length) {
        int j = i + 1
        @Invariant({ 0 <= i && i < j && j <= nums.length })
        @Invariant({ (i + 1..<j).every { int b -> nums[i] != nums[b] } })
        @Decreases({ nums.length - j })
        while (j < nums.length) {
            if (nums[i] == nums[j]) return true
            j = j + 1
        }
        i = i + 1
    }
    return false
}
```

### Zigzag encoding

Protocol Buffers' trick for storing signed integers as small unsigned numbers folds the number line onto the
non-negatives: 0, -1, 1, -2, 2… become 0, 1, 2, 3, 4…. LemmaScript proves the round-trip laws both ways:

```ts
function encode(n: number): number {
  //@ verify
  //@ ensures \result >= 0
  return n >= 0 ? 2 * n : -2 * n - 1;
}

function decode(z: number): number {
  //@ verify
  //@ requires z >= 0
  return z % 2 === 0 ? Math.floor(z / 2) : -Math.floor((z + 1) / 2);
}
```

Dafny sees through a function's body at a call site, so LemmaScript's `decode` needs no postcondition.
groovy-verify reasons about a call through the callee's contract, so `decode` states what it computes: the
integer whose code is `z`. With that, the round trips are the same one-liners:

<!-- doclint:case lemmascript-port/zigzag-round-trips -->
```groovy
/** Folds a signed integer onto a non-negative zigzag code. */
@Ensures({ result >= 0 && result == (n >= 0 ? 2 * n : -2 * n - 1) })
static int encode(int n) { n >= 0 ? 2 * n : -2 * n - 1 }

/** Unfolds a zigzag code back to its signed integer: the integer whose code it is. */
@Requires({ z >= 0 })
@Ensures({ z == (result >= 0 ? 2 * result : -2 * result - 1) })
static int decode(int z) { z % 2 == 0 ? z.intdiv(2) : -(z + 1).intdiv(2) }

/** Decoding an encoded integer recovers it. */
@Ensures({ result == n })
static int roundTrip(int n) { decode(encode(n)) }

/** Encoding a decoded code recovers it. */
@Requires({ z >= 0 })
@Ensures({ result == z })
static int reverseRoundTrip(int z) { encode(decode(z)) }
```

Both proofs are over mathematical integers, which matches LemmaScript's `number`. On Java's 32-bit `int` the
laws break, and `@CheckOverflow` says where. Doubling overflows at both ends, and at the bottom
`-2 * n - 1` wraps:

<!-- doclint:case lemmascript-port/zigzag-encode-overflows-32-bit-int -->
```groovy
@CheckOverflow
@Ensures({ result >= 0 })
static int encode(int n) { n >= 0 ? 2 * n : -2 * n - 1 }
```

<!-- doclint:diagnostic lemmascript-port/zigzag-encode-overflows-32-bit-int -->
```
Possible ArithmeticException: subtraction overflows 32-bit signed range
    …
    counterexample: n = -2147483648
    fails on: encode(-2147483648)
```

At runtime `encode(Integer.MIN_VALUE)` really does return `-1`, which `decode`'s precondition rejects.
Protocol Buffers avoids the problem by computing the code with shifts, `(n << 1) ^ (n >> 31)`, and treating the
result as unsigned bits rather than as a signed `int`.

### A bounded counter

<!-- doclint:case lemmascript-port/counter -->
```groovy
class Counter {
    int count = 0
    final int max

    Counter(int max) { this.max = max }

    /** Advances the count, returning its previous value. */
    @Requires({ count < max })
    @Ensures({ count <= max && result == old.count })
    int increment() { int o = count; count = count + 1; return o }

    /** Reports whether the count has reached its bound. */
    @Ensures({ result == (count >= max) })
    boolean isAtMax() { count >= max }
}
```

### High score

LemmaScript's `Math.max(...scores)` is Groovy's `scores.max()`:

<!-- doclint:case lemmascript-port/highscore -->
```groovy
/** Returns the highest of a non-empty set of scores. */
@Requires({ scores != null && scores.length > 0 })
@Ensures({ (0..<scores.length).every { scores[it] <= result } })
static int highScore(int[] scores) { scores.max() }
```

## Not ported yet

These examples hit the edges of what groovy-verify proves today:

- **`continue`, and `break` from a nested loop.** A `break` at the top level of a loop body, or ending a branch of
  the body's final `if`/`else` chain, is supported. A `continue`, or a `break` out of an inner loop, still skips
  loudly.
- **Boyer–Moore majority vote** (`majority.ts`). Its invariants count occurrences in a prefix with a recursive
  `occOf(arr, x, i)`. The Groovy spelling, `arr[0..<i].count(x)`, has no supporting axioms yet: `count` works as
  a whole-array permutation fact, but a loop accumulating it times out.
- **Building lists.** `findAll`, recursion that rebuilds a list, and element facts about values a loop appended
  are all outside the fragment, which is why `pruneWindow` above proves only its size bound.
- **Nonlinear arithmetic.** The money-splitting `allocate`, and the largest-remainder allocation behind the
  bill-splitting case studies, multiply and divide variables by each other.

## The case studies

LemmaScript's [case studies](https://docs.lemmascript.org/case-studies/) are whole applications rather than
examples: a collaborative to-do app on React and Supabase, verified fixes for CVEs in Hono's middleware,
expense splitters that prove money is never lost, an ESLint plugin whose reachability check is proven sound and
complete. They carry hundreds of proof obligations each, with helper lemmas and, in some, Lean proofs
alongside the Dafny. They're a good guide to what verifying a real TypeScript codebase looks like, but they
aren't small enough to port one-to-one, and several depend on the arithmetic and list reasoning listed above.
