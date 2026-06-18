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

# Dafny examples


The HumanEval ports above are LeetCode-shape problems. To check the engine against the
proofs the **Dafny** community itself uses as credentials, it's also been run over
canonical examples from Dafny's own materials — its
[online tutorial](https://dafny.org/latest/OnlineTutorial/guide) and the
[VSComp 2010 competition suite](https://github.com/dafny-lang/dafny/tree/master/Source/IntegrationTests/TestFiles/LitTests/LitTest/VSComp2010)
(Leino). They're ported *faithfully* — the Groovy adds nothing the fragment can't express —
and none overlaps the examples elsewhere in these docs: the existing set has a *witnessed-extremum equality*
(`max_element`), a *sum biconditional* (`below_zero`), and *full `sorted ∧ permutation`*
(insertion sort), but nothing that is a search-returning-index, a nonlinear bound between two
aggregates, or sorted binary search. All three verify — including Dafny's single most iconic
example, binary search.

In the five-act framing these sit with **Act 5** — full-algorithm depth rather than single-property
checks — but measured against the proofs the Dafny/Verus community recognises rather than ones we chose.

### SumMax — `sum ≤ N · max` (VSComp 2010, Problem 1)

Compute the sum and the max of an array in one pass, and prove `sum ≤ N · max`. The whole
proof rides on a *nonlinear* loop invariant, `sum ≤ i · max` — the multiplicative sibling of
the additive prefix-sum invariants. The Dafny original:

```dafny
method M(N: int, a: array<int>) returns (sum: int, max: int)
  requires 0 <= N && a.Length == N && (forall k :: 0 <= k && k < N ==> 0 <= a[k])
  ensures sum <= N * max
{
  sum := 0; max := 0;
  var i := 0;
  while (i < N)
    invariant i <= N && sum <= i * max
  {
    if (max < a[i]) { max := a[i]; }
    sum := sum + a[i];
    i := i + 1;
  }
}
```

Dafny's `returns (sum, max)` is a **named** tuple, so the faithful Groovy is the map-as-named-tuple
idiom (Phase 83): a map literal whose entries the contract references by name, reading exactly like
Dafny's `sum` / `max`. The literal is the method's trailing expression — Groovy returns it implicitly,
which also mirrors Dafny's named out-parameters (there is no explicit `return` of them either):

<!-- doclint:case dafny-port/summax-vscomp10-p1-sum-n-max -->
```groovy
@Requires({ 0 <= n && a.length == n && (0..<n).every { a[it] >= 0 } })
@Ensures({ result.sum <= n * result.max })
static Map<String, Integer> sumMax(int[] a, int n) {
    int sum = 0, max = 0, i = 0
    @Invariant({ 0 <= i && i <= n && sum <= i * max })
    @Decreases({ n - i })
    while (i < n) {
        if (max < a[i]) max = a[i]
        sum += a[i]
        i++
    }
    [sum: sum, max: max]
}
```

The body leans on Groovy's shorthand where it stays unambiguous — compound assignment (`sum += a[i]`,
`i++`) and the implicit trailing-expression return — rather than Dafny's longhand (`sum := sum + a[i];
i := i + 1`). The control structure, the invariant, and the four loop obligations are identical either
way; the shorthand is just less to read.

Preservation is genuine NIA (Phase 48): `sum + a[i] ≤ (i + 1) · max′` needs `i · max ≤ i · max′`
(monotone because `i ≥ 0` and `max ≤ max′`) *and* `a[i] ≤ max′`. The bound is a different
shape from any of our other examples — an *inequality relating two running aggregates*, not an
equality to one — and a deliberately wrong bound (`≤ (N − 1) · max`) refutes with
`fails on: sumMax(new int[0], 0)`. With the return type declared `Map<String, Integer>`, the map values read
back as `Integer` inside the contract closure (GROOVY-12071), so the arithmetic `n * max` and the `<=`
type-check with no `(int)` cast — the postcondition reads exactly as written. The names still earn their keep:
`result.sum` / `result.max` say what they are where positional `result.v1` / `result.v2` (the typed-`Tuple2`
alternative) wouldn't. (Per Leino's own note, the
`a[k] >= 0` precondition isn't actually needed for the postcondition — it's kept here only to stay
faithful to the source.)

### Find — linear search, "not present ⟹ ∀ `a[k] ≠ key`"

The Dafny tutorial's linear search returns an index, or `−1` with a *universal* witness that the
key is absent:

```dafny
method Find(a: array<int>, key: int) returns (index: int)
  ensures 0 <= index ==> index < a.Length && a[index] == key
  ensures index < 0 ==> forall k :: 0 <= k < a.Length ==> a[k] != key
{
  index := 0;
  while index < a.Length
    invariant 0 <= index <= a.Length
    invariant forall k :: 0 <= k < index ==> a[k] != key
  {
    if a[index] == key { return; }
    index := index + 1;
  }
  index := -1;
}
```

The port reads almost identically:

<!-- doclint:case dafny-port/find-linear-search-index-0-no-element-equals-key -->
```groovy
@Ensures({ result >= 0 ==> result < a.length && a[result] == key })
@Ensures({ result < 0 ==> (0..<a.length).every { a[it] != key } })
static int find(int[] a, int key) {
    int i = 0
    @Invariant({ 0 <= i && i <= a.length && (0..<i).every { a[it] != key } })
    @Decreases({ a.length - i })
    while (i < a.length) {
        if (a[i] == key) return i
        i = i + 1
    }
    return -1
}
```

This is worth pairing with binary search because it is binary search's postcondition *with
sortedness removed* — so it isolates exactly what binary search adds. The in-body early `return i`
(Phase 49b) *witnesses* the found case (binds `result = i` with `a[i] == key`); the invariant
carries the "no earlier element matched" universal to the `return −1` path; and preservation
extends `(0..<i)` to `(0..<i + 1)` in a single quantifier instantiation, because the loop just
checked `a[i] != key` — no transitivity required. A spec claiming the found index holds a
*different* key (`a[result] != key`) correctly refutes.

### BinarySearch — the iconic example

Dafny's flagship tutorial proof, with the `sorted` predicate stated as a *two-dimensional*
quantifier:

```dafny
predicate sorted(a: array<int>)
  reads a
{ forall j, k :: 0 <= j < k < a.Length ==> a[j] <= a[k] }

method BinarySearch(a: array<int>, value: int) returns (index: int)
  requires 0 <= a.Length && sorted(a)
  ensures 0 <= index ==> index < a.Length && a[index] == value
  ensures index < 0 ==> forall k :: 0 <= k < a.Length ==> a[k] != value
{
  var low, high := 0, a.Length;
  while low < high
    invariant 0 <= low <= high <= a.Length
    invariant forall i :: 0 <= i < a.Length && !(low <= i < high) ==> a[i] != value
  {
    var mid := (low + high) / 2;
    if a[mid] < value { low := mid + 1; }
    else if value < a[mid] { high := mid; }
    else { return mid; }
  }
  return -1;
}
```

The port is the **verbatim** shape — `else return mid` inside the loop, `return -1` after — and it
verifies: both postcondition directions, the excluded-region universal preserved across the narrowing,
every `a[mid]` bound, and termination:

<!-- doclint:case dafny-port/binarysearch-textbook-return-mid-both-directions-bounds-termination -->
```groovy
@Requires({ a.isSorted() })
@Ensures({ result < 0  ==> (0..<a.length).every { a[it] != value } })
@Ensures({ result >= 0 ==> result < a.length && a[result] == value })
static int binarySearch(int[] a, int value) {
    int low = 0, high = a.length
    @Invariant({ 0 <= low && low <= high && high <= a.length &&
                 (0..<low).every { a[it] != value } && (high..<a.length).every { a[it] != value } })
    @Decreases({ high - low })
    while (low < high) {
        int mid = low + (high - low).intdiv(2)
        if (a[mid] < value) low = mid + 1
        else if (value < a[mid]) high = mid
        else return mid
    }
    return -1
}
```

The one authoring subtlety worth calling out — and it's a *spec* choice, not an engine detail — is **how
sortedness is stated**. The natural one-dimensional spelling, the adjacent form
`(1..<a.length).every { a[it - 1] <= a[it] }`, doesn't carry the proof: narrowing `low = mid + 1` needs
`a[i] ≤ a[mid]` for *all* `i ≤ mid`, which is range transitivity — induction, not a single instantiation.
The contract above instead writes it the **native** way, `a.isSorted()` — Groovy 6's GDK predicate
(ascending, ties allowed; the primitive `int[]` and `long[]` overloads are native, and the boolean-getter
property `a.sorted` works too) — which the engine lowers to the *two-dimensional* axiom
`∀ j,k. 0 ≤ j < k < n ⟹ a[j] ≤ a[k]` with an explicit multi-pattern trigger `{a[j], a[k]}`, so the gap
fact `a[i] ≤ a[mid]` fires in a single deterministic instantiation. The explicit `Sorted.ascending(a)` /
`.descending` / `.strictlyAscending` helpers (`verification.Sorted`, a sibling of `Forall`/`Sets`) are the
same thing for the orderings without a native spelling. Either way it's all the spec needs; without it,
preservation refutes on a concrete *unsorted* counterexample (`[7719, 7718]`) — the proof genuinely rests
on sortedness. Dafny's verbatim binary search then verifies, structure-for-structure.

