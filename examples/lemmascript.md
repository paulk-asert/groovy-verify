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
| a recursive pure count, `occOf(arr, x, n)` | the prefix count `arr[0..<n].count(x)` |
| `forall(y: int, P)`, `exists(x: nat, P)` over all values | `arr.every { y -> P }`, `arr.any { x -> P }` over the values that occur |
| `log.slice(1)` | `log.drop(1)` |
| `[x, ...rest]` | `[x] + rest`, or `[x, *rest]` |
| `sum(arr)` | `arr.sum()`, or `arr[0..<i].sum(0)` for a prefix that may be empty (a Groovy `[].sum()` is `null`) |
| `Math.floor(a / b)` | `a.intdiv(b)` (the same for `a >= 0`, `b > 0`; `intdiv` truncates toward zero) |

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

Both postconditions port, and so does the recursion. `log.slice(1)` is `log.drop(1)`, and `[log[0], ...rest]` is
`[log[0]] + rest` (or the spread literal `[log[0], *rest]`):

<!-- doclint:case lemmascript-port/prunewindow-recursive -->
```groovy
/** Keeps only the requests still inside the sliding time window. */
@Requires({ log != null && log.every { int t -> t <= now } })
@Ensures({ result.size() <= log.size() })
@Ensures({ result.every { int t -> now - w < t && t <= now } })
@Decreases({ log.size() })
static List<Integer> pruneWindow(List<Integer> log, int now, int w) {
    if (log.isEmpty()) return []
    List<Integer> rest = pruneWindow(log.drop(1), now, w)
    if (log[0] > now - w) return [log[0]] + rest
    return rest
}
```

The recursive call is the inductive hypothesis: its precondition holds because every element of `log.drop(1)`
is an element of `log`, its result satisfies both postconditions, and `@Decreases` shows `log.drop(1)` is shorter.
Prepending `log[0]`, which is inside the window on that branch, keeps both.

As a loop that appends with `add`, the Groovy keeps the same contract, and an element invariant carries the
window bound:

<!-- doclint:case lemmascript-port/prunewindow -->
```groovy
/** Keeps only the requests still inside the sliding time window. */
@Requires({ log != null && log.every { int t -> t <= now } })
@Ensures({ result.size() <= log.size() })
@Ensures({ result.every { int t -> now - w < t && t <= now } })
static List<Integer> pruneWindow(List<Integer> log, int now, int w) {
    List<Integer> out = []
    int i = 0
    @Invariant({ 0 <= i && i <= log.size() && out.size() <= i })
    @Invariant({ out.every { int t -> now - w < t && t <= now } })
    @Decreases({ log.size() - i })
    while (i < log.size()) {
        if (log[i] > now - w) out.add(log[i])
        i = i + 1
    }
    return out
}
```

The lower bound `now - w < t` comes from the `if`. The upper bound comes from the precondition, and until Phase
320 it couldn't reach the loop: the `List<Integer> out = []` before the loop made the verifier give up on
bounding what the loop writes, so it assumed none of the precondition inside it. And the idiomatic one-liner
proves too:

<!-- doclint:case p320-list-building/prunewindow-by-findall -->
```groovy
/** Keeps only the requests still inside the sliding time window. */
@Requires({ log != null && log.every { int t -> t <= now } })
@Ensures({ result.size() <= log.size() })
@Ensures({ result.every { int t -> now - w < t && t <= now } })
static List<Integer> pruneWindow(List<Integer> log, int now, int w) {
    return log.findAll { int t -> t > now - w }
}
```

`findAll` is modelled as a list no longer than its source whose every element passes the predicate and comes
from the source. That's what these claims need. It isn't modelled to keep *every* passing element, or to keep
their order, so a claim that depends on either doesn't prove.

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

It ports, with LemmaScript's postcondition unchanged. TypeScript's `Math.floor(total * w / W)` is Groovy's
`(total * w).intdiv(W)`, and the `map` and the leftover loop become two `while` loops:

<!-- doclint:case lemmascript-port/allocate -->
```groovy
/** Splits total across the weights without losing any of it. */
@Requires({ weights != null && total >= 0 && weights.every { int w -> w >= 0 } && weights.sum() > 0 })
@Ensures({ result.sum() == total })
static int[] allocate(int total, int[] weights) {
    int W = weights.sum()
    int[] result = new int[weights.length]
    int s = 0
    int p = 0
    int i = 0
    @Invariant({ 0 <= i && i <= weights.length && result.length == weights.length })
    @Invariant({ s == result[0..<i].sum(0) && p == weights[0..<i].sum(0) })
    @Invariant({ s * W <= total * p && total * p <= s * W + i * (W - 1) })
    @Decreases({ weights.length - i })
    while (i < weights.length) {
        result[i] = (total * weights[i]).intdiv(W)
        s = s + result[i]
        p = p + weights[i]
        i = i + 1
    }
    int left = total - s
    int k = 0
    @Invariant({ 0 <= k && 0 <= left && result.length == weights.length })
    @Invariant({ k + left < weights.length + (left == 0 ? 1 : 0) })
    @Invariant({ result.sum() + left == total })
    @Decreases({ left })
    while (left > 0) {
        result[k] = result[k] + 1
        k = k + 1
        left = left - 1
    }
    return result
}
```

The third invariant of the first loop is the lemma LemmaScript needs separately. Each floored share loses less
than one whole unit, at most `W - 1` out of `total * w`, so after all the shares the leftover is below
`weights.length`. That's what keeps `result[k]` in bounds in the second loop. Drop the `i * (W - 1)` slack and
the verifier reports that `result[k]` may be out of bounds.

The arithmetic is nonlinear: `s * W`, `total * p` and `(total * w).intdiv(W)` multiply and divide variables by
each other. Z3 proves this sort of thing on its own, and it proves the prefix sums on their own, but with both
in the same query it times out. groovy-verify now retries such a query on slices of it (only the arithmetic
with the sum facts it needs, or only the sums), each of which can prove the obligation but never refute it.

The first attempt, which stops after flooring, doesn't prove. It isn't refuted either: the verifier reports
"could not decide", since a counterexample would have to satisfy the recursive sum axioms and the solver can't
build one. That's the same outcome as LemmaScript's, which rejects the attempt rather than printing
`[3, 3, 3]`.

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

### Majority vote

LemmaScript's `majority.ts` is Boyer–Moore's vote. Pass 1 keeps a candidate and a counter; pass 2 checks the
candidate by counting it. Its invariants count occurrences in a prefix through a recursive helper:

```ts
//@ pure
function occOf(arr: number[], x: number, n: number): number {
  //@ requires 0 <= n && n <= arr.length
  //@ decreases n
  return n === 0 ? 0 : occOf(arr, x, n - 1) + (arr[n - 1] === x ? 1 : 0);
}
export function majority(arr: number[]): number {
  //@ requires forall(k: nat, k < arr.length ==> arr[k] >= 0)
  //@ ensures \result === -1 || (\result >= 0 && 2 * occOf(arr, \result, arr.length) > arr.length)
  //@ ensures (exists(x: nat, 2 * occOf(arr, x, arr.length) > arr.length)) ==> \result !== -1
  let cand = 0;
  let cnt = 0;
  let i = 0;
  while (i < arr.length) {
    //@ invariant 0 <= i && i <= arr.length
    //@ invariant cnt >= 0
    //@ invariant cand >= 0
    //@ invariant 2 * occOf(arr, cand, i) <= i + cnt
    //@ invariant forall(y: int, y !== cand ==> 2 * occOf(arr, y, i) <= i - cnt)
    //@ decreases arr.length - i
    if (cnt === 0) {
      cand = arr[i];
      cnt = 1;
    } else if (arr[i] === cand) {
      cnt = cnt + 1;
    } else {
      cnt = cnt - 1;
    }
    i = i + 1;
  }
  let occ = 0;
  let j = 0;
  while (j < arr.length) {
    //@ invariant 0 <= j && j <= arr.length
    //@ invariant occ === occOf(arr, cand, j)
    //@ decreases arr.length - j
    if (arr[j] === cand) {
      occ = occ + 1;
    }
    j = j + 1;
  }
  if (2 * occ > arr.length) {
    return cand;
  } else {
    return -1;
  }
}
```

`occOf(arr, x, n)` is the prefix count `arr[0..<n].count(x)`, so the Groovy needs no helper. The two unbounded
quantifiers, over every `int` `y` and every `nat` `x`, range over the array's own values instead. A value that
never occurs has count 0, so it adds nothing to the `exists`, and for the `forall` the only thing it needs is
`cnt <= i`, which joins the first invariant:

<!-- doclint:case p319-majority/majority-ts-verbatim-boyer-moore-majority-vote -->
```groovy
/** Returns the value occurring in more than half of arr, or -1 when there is none. */
@Requires({ arr.every { int k -> k >= 0 } })
@Ensures({ result == -1 || (result >= 0 && 2 * arr[0..<arr.length].count(result) > arr.length) })
@Ensures({ arr.any { int x -> 2 * arr[0..<arr.length].count(x) > arr.length } ==> result != -1 })
static int majority(int[] arr) {
    int cand = 0
    int cnt = 0
    int i = 0
    @Invariant({ 0 <= i && i <= arr.length && cnt >= 0 && cnt <= i && cand >= 0 })
    @Invariant({ 2 * arr[0..<i].count(cand) <= i + cnt })
    @Invariant({ arr.every { int y -> y == cand || 2 * arr[0..<i].count(y) <= i - cnt } })
    @Decreases({ arr.length - i })
    while (i < arr.length) {
        if (cnt == 0) {
            cand = arr[i]
            cnt = 1
        } else if (arr[i] == cand) {
            cnt = cnt + 1
        } else {
            cnt = cnt - 1
        }
        i = i + 1
    }
    int occ = 0
    int j = 0
    @Invariant({ 0 <= j && j <= arr.length && occ == arr[0..<j].count(cand) })
    @Decreases({ arr.length - j })
    while (j < arr.length) {
        if (arr[j] == cand) {
            occ = occ + 1
        }
        j = j + 1
    }
    if (2 * occ > arr.length) {
        return cand
    } else {
        return -1
    }
}
```

The second loop's invariant says nothing about `cand`, yet the postcondition needs everything the first loop
established about it. The second loop never writes `cand`, `cnt` or `i`, so those facts carry across it, as
they do in Dafny. Until Phase 319 each later loop had to restate them. Neither of pass 1's two counting
invariants is inductive on its own: when `cnt` reaches 0 the body adopts `arr[i]` as the new candidate, and
bounding its count takes the "others" invariant.

One boundary shows here. A *wrong* claim about `majority`, such as `result != -1`, is not refuted with a
counterexample: Z3 can't build a model through the quantified count axioms, so the verdict is "could not
decide". That's loud, and never a false proof, but it gives no failing input.

Since `occOf(arr, x, arr.length)` counts the whole array, the postconditions can also be written in the more
idiomatic Groovy `arr.count(x)`, with the invariants unchanged:

<!-- doclint:case p322-count-bridge/majority-vote-with-whole-array-counts -->
```groovy
@Ensures({ result == -1 || (result >= 0 && 2 * arr.count(result) > arr.length) })
@Ensures({ arr.any { int x -> 2 * arr.count(x) > arr.length } ==> result != -1 })
```

The verifier treats an array's `count(x)` and its prefix count over the full length as the same quantity, so the
loops' prefix counts reach the whole-array claim.

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
- **Refuting nonlinear sums.** [`allocate`](#splitting-money) proves, but a wrong claim in the same territory (the
  first attempt, a bump by two) is "could not decide" rather than a counterexample.

## The case studies

LemmaScript's [case studies](https://docs.lemmascript.org/case-studies/) are whole applications rather than
examples: a collaborative to-do app on React and Supabase, verified fixes for CVEs in Hono's middleware,
expense splitters that prove money is never lost, an ESLint plugin whose reachability check is proven sound and
complete. They carry hundreds of proof obligations each, with helper lemmas and, in some, Lean proofs
alongside the Dafny. They're a good guide to what verifying a real TypeScript codebase looks like, but they
aren't small enough to port one-to-one, and several depend on the reasoning listed above.
