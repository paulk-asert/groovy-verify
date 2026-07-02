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

In the [five-act framing](tour.md) these sit with **[Act 5](tour.md#act-5--all-the-way-to-a-real-algorithm)** — full-algorithm depth rather than single-property
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

### Ticket lock — mutual exclusion (Leino, KRML260)

The three above are sequential algorithms. Leino's lecture notes
[*Modeling Concurrency in Dafny*](https://leino.science/papers/krml260.pdf) (KRML260) are a different animal:
a **bakery-style ticket lock** for mutual exclusion, reasoned about the way UNITY / Event-B / TLA⁺ do — a
concurrent system as atomic events interleaved by a tacit scheduler, each event maintaining a **system
invariant**, and the safety property (*at most one process in the critical section*) proved as a logical
consequence of that invariant. No thread interleavings are enumerated; concurrency is modelled *sequentially*.
This is the same posture as the [concurrency-lite gallery](concurrency.md) — except there we prove the local
half and hand mutual exclusion to the runtime rungs, and here we **prove the mutual-exclusion invariant itself**.

Leino's system invariant `Valid()`, strengthened (over the paper's Section 5.0) until it implies mutual
exclusion — the ticket dispenser never falls behind the display, every waiting/eating process holds a ticket
in `[serving, ticket)`, **distinct waiters hold distinct tickets**, and an eating process holds exactly
`serving`:

```dafny
predicate Valid()
  reads this
{
  cs.Keys == t.Keys == P &&
  serving <= ticket &&
  (forall p :: p in P && cs[p] != Thinking ==> serving <= t[p] < ticket) &&
  (forall p,q :: p in P && q in P && p != q && cs[p] != Thinking && cs[q] != Thinking ==> t[p] != t[q]) &&
  (forall p :: p in P && cs[p] == Eating ==> t[p] == serving)
}

lemma MutualExclusion(p: Process, q: Process)
  requires Valid() && p in P && q in P && cs[p] == Eating && cs[q] == Eating
  ensures p == q
{ }
```

The faithful Groovy fixes `Process` to a small enum — Leino explicitly offers this (`datatype Process = Agnes
| Agatha | Germaine | Jack`) — so `P` is finite, `cs`/`t` are **enum-keyed maps**, and the `∀p` / `∀p,q`
conjuncts expand over the domain. Following the paper's *Section 7* (TLA⁺-style) formulation, each atomic
event is a **two-state predicate** and each proof an **empty-bodied lemma** — the same law-lemma shape the
[lattice/monoid arcs](checkers.md) use. `Valid` and `MutualExclusion` become:

<!-- doclint:case p170-ticket-lock/mutual-exclusion-follows-from-the-invariant -->
```groovy
enum Phil { A, B }
enum CS { Thinking, Hungry, Eating }

static boolean valid(int ticket, int serving, Map<Phil,CS> cs, Map<Phil,Integer> t) {
    serving <= ticket &&
    (cs[Phil.A] != CS.Thinking ==> (serving <= t[Phil.A] && t[Phil.A] < ticket)) &&
    (cs[Phil.B] != CS.Thinking ==> (serving <= t[Phil.B] && t[Phil.B] < ticket)) &&
    ((cs[Phil.A] != CS.Thinking && cs[Phil.B] != CS.Thinking) ==> t[Phil.A] != t[Phil.B]) &&
    (cs[Phil.A] == CS.Eating ==> t[Phil.A] == serving) &&
    (cs[Phil.B] == CS.Eating ==> t[Phil.B] == serving)
}

@Requires({ valid(ticket, serving, cs, t) && cs[p] == CS.Eating && cs[q] == CS.Eating })
@Ensures({ p == q })                        // both eating ⟹ the same process — mutual exclusion
static void mutualExclusion(int ticket, int serving, Map<Phil,CS> cs, Map<Phil,Integer> t, Phil p, Phil q) {}
```

Two details are worth calling out. First, `Process` is a fixed enum, so this is the **N = 2 instance** — the
general symbolic `set<Process>` over an *uninterpreted* sort is out of the fragment (it needs quantification
over an opaque domain). Second, `mutualExclusion` keeps `p` and `q` **symbolic**, exactly as the paper writes
it: the reads `cs[p]` / `cs[q]` are at symbolic keys, yet they connect to the literal-key reads inside `valid`
because an enum scalar carries a **domain-closure axiom** (`p` is `A` or `B`) and maps ride Z3's array theory —
so one lemma covers every process, no per-actor expansion. The same symbolic-actor form proves that each of
`Request`, `Enter`, and `Leave` **preserves** `valid` (the two-state predicate of each event relates the pre-
and post-state passed as parameters). `Leave` — advancing `serving` and re-establishing the strict bound
`serving+1 <= t[q]` for a still-waiting `q` — is the one the paper flags as trickiest; it needs *both* the
uniqueness conjunct and `eating ⟹ served`, exactly the strengthening chain Leino walks through.

That chain is what makes the proof honest: drop the uniqueness conjunct — the last one the paper adds — and
both `mutualExclusion` and `Leave`-preservation **refute** with `Cannot prove postcondition`. Because a lemma
the encoder couldn't interpret would *skip* (compile clean), the refutation is what proves the reasoning
actually ran.

Leino's second half is **liveness** — *a hungry process eventually eats* (Section 7.6). It is genuinely
surprising that an SMT-backed *sequential* checker can touch it at all, and the reason is Leino's: the liveness
proof **is an algorithm** — a proof-loop that walks a well-founded measure down to zero — so it needs no
temporal-logic engine, only a ranking function and `@Decreases`. That measure is **`t[p] - serving`**: the
number of "serving"-display turns between a waiter `p` and its ticket. Its properties verify as the same kind of
empty-bodied lemma — bounded below, strictly decreased by `Leave` and unchanged by the other events, always with
a served process to follow out of the kitchen, and zero enabling entry:

<!-- doclint:ignore illustration: KRML260 §7.6 liveness ranking function (the real cases are P171 in VerifyHarness) -->
```groovy
// bounded below — the measure is a natural number, so it cannot descend forever
@Requires({ valid(ticket, serving, cs, t) && cs[p] != CS.Thinking })
@Ensures({ t[p] - serving >= 0 })
static void measureNonNegative(int ticket, int serving, Map<Phil,CS> cs, Map<Phil,Integer> t, Phil p) {}

// Leave by the served process q drops a distinct waiter p's measure by one — and keeps it >= 0
// (the >= 0 needs uniqueness + eating==>served: a waiter distinct from the eater holds a larger ticket)
@Requires({ valid(ticket, serving, cs, t) && cs[q] == CS.Eating && cs[p] == CS.Hungry && p != q &&
            serving2 == serving + 1 && t2[p] == t[p] })
@Ensures({ (t2[p] - serving2) < (t[p] - serving) && (t2[p] - serving2) >= 0 })
static void leaveDecreasesMeasure(int ticket, int serving, Map<Phil,CS> cs, Map<Phil,Integer> t,
                                  Phil p, Phil q, int serving2, Map<Phil,Integer> t2) {}
```

These are the *ingredients* — a well-founded, monotonically-falling measure with an available step and a base
case. Composing them into an **eventually-eats** means reasoning about the system state *over time*, which Leino
models as functions `serving`, `t[p]`, `cs[p] : nat → …`. groovy-verify can model those as uninterpreted functions
(`Function`-typed, `f.apply(i)`), and a small **engine fix** was needed to make it work here: a numeric-returning
`Function`'s application now mints a stable, shared Int-sorted term that partakes in integer arithmetic (before, the
`int` time index was coerced into the `Object` value sort and `f.apply(i)` fell through unmodelled — a fresh opaque
value per occurrence, so nothing over the trace composed). With that, per-step trace reasoning composes, and — using
bounded bypass to pin the horizon at a *constant* — a **bounded eventually-eats verifies**: a Hungry process at
measure one has the served process leave (`serving` advances, so the waiter's measure hits zero — *derived*, not
assumed), then its `Enter` fires, and it is Eating two trace steps later. Drop the `Enter` step and it refutes.

What stays out of reach is the **fair-schedule** eventually-eats: not the composition (that now works) but
*deriving* that the productive steps occur — that under any fair schedule the served process is eventually picked —
which is Leino's `GetNextStep` search-loop and `Liveness` proof-loop over an *unbounded* horizon. That needs two
things the fragment lacks: **using a recursive lemma's own postcondition as an induction hypothesis** (a probe hits
"no usable @Ensures" on the self-recursive call — the direct telescoping `serving(k) == serving(0) + k` is the same
gap), and an **unbounded `∀i:nat`** hypothesis with on-demand instantiation. Those are the next *engine* increments;
with them, the general (any-N, infinite-trace) liveness is reachable.

What *does* ship is the finiteness that underwrites liveness, as a **state invariant** — no trace needed. Add the
**counting invariant** `ticket - serving == (#non-thinking processes)` (each dispensed-but-unserved ticket is one
waiting/eating process; maintained by every event), and a waiter's measure is provably **`t[p] - serving <= 1`**
for the two-process lock: **a waiting process is overtaken at most once before it enters** — *bounded bypass*, a
liveness property stronger than mere eventual entry, since it bounds the wait. Composed with the ranking function
above (each `Leave` decreases the measure), from any `Hungry` state at most one competitor `Leave` stands between
the waiter and eating. Drop the counting invariant and the bound refutes — the dispenser could run arbitrarily far
ahead of the display. Safety, the ranking function, bounded bypass, and a bounded trace-level eventually-eats all
verify structure-for-structure with the paper; only the fair-schedule temporal composition — deriving that the
productive steps occur over an unbounded horizon — remains out of fragment.

