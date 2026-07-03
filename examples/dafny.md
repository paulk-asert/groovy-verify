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
method M(N: int, a: array<int>) returns (sum: int, max: int)     // Dafny
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
method Find(a: array<int>, key: int) returns (index: int)     // Dafny
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
predicate sorted(a: array<int>)     // Dafny
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

### The Theorem Prover Showdown — leftpad, unique, fulcrum (Hillel Wayne)

Hillel Wayne's [Theorem Prover Showdown](https://www.hillelwayne.com/post/theorem-prover-showdown/) posed
three verification challenges as an imperative-vs-functional duel — and groovy-verify sits squarely on the
imperative side the challenge was designed to exercise: loops carrying `@Invariant`s. All three verify with
their **full specifications**:

- **leftpad** — output length is `max(n, len)`, the pad prefix is all `c`, the suffix is `s` — a single
  fill loop over the two regions ([the famous benchmark](https://github.com/hwayne/lets-prove-leftpad)
  with entries from thirty-odd provers; the Groovy proof is the `int[]` form of the same spec).
- **unique** — the deduplicated prefix is **pairwise-distinct and covers the input in both directions**
  (`output ⊆ input` and `input ⊆ output`, nested `every`/`any` quantifiers) — a *bidirectional* spec, one
  direction more than the challenge's own partial Dafny solution — with a nested membership-scan loop
  whose invariant ties the `found` flag to the scanned prefix.
- **fulcrum** — the crown: return the cut `i` minimizing `|sum(left) − sum(right)|`, in O(n). The prefix
  sum arrives as a guarded pure-recursive `psum` helper (its defining equation ties the loop accumulator
  to the spec term one unfold per iteration), and the argmin invariant carries minimality over every cut
  seen:

<!-- doclint:case p202-prover-showdown/fulcrum-returned-cut-minimizes-left-right-over-all-cuts -->
```groovy
static int psum(int[] a, int k) {
    (a != null && 0 < k && k <= a.length) ? psum(a, k - 1) + a[k - 1] : 0
}

@Requires({ a != null })
@Ensures({ 0 <= result && result <= a.length &&
    (0..a.length).every { int j ->
        (2 * psum(a, result) - psum(a, a.length) >= 0 ?
             2 * psum(a, result) - psum(a, a.length) : psum(a, a.length) - 2 * psum(a, result)) <=
        (2 * psum(a, j) - psum(a, a.length) >= 0 ?
             2 * psum(a, j) - psum(a, a.length) : psum(a, a.length) - 2 * psum(a, j)) } })
static int fulcrum(int[] a) {
    int total = psum(a, a.length)
    int left = 0
    int best = 0
    int bestDiff = total >= 0 ? total : -total
    int i = 1
    @Invariant({ a != null && 1 <= i && i <= a.length + 1 &&
        total == psum(a, a.length) &&
        left == psum(a, i - 1) &&
        0 <= best && best <= i - 1 &&
        bestDiff == (2 * psum(a, best) - total >= 0 ? 2 * psum(a, best) - total : total - 2 * psum(a, best)) &&
        (0..<i).every { int j ->
            bestDiff <= (2 * psum(a, j) - total >= 0 ? 2 * psum(a, j) - total : total - 2 * psum(a, j)) } })
    @Decreases({ a.length + 1 - i })
    while (i <= a.length) {
        left = left + a[i - 1]
        int d = 2 * left - total
        int diff = d >= 0 ? d : -d
        if (diff < bestDiff) { best = i; bestDiff = diff }
        i = i + 1
    }
    return best
}
```

The teeth: a mis-offset leftpad suffix refutes, a fulcrum that never updates its best cut fails invariant
preservation, and an over-strong unique claim (`result == a.length` — "the input never had duplicates")
refutes at the exit check.

**The siblings in the leftpad repo.** Two entries there are old acquaintances. The
[`java`](https://github.com/hwayne/lets-prove-leftpad/tree/master/java) entry is **OpenJML** — the same
JML-annotated `char[]` spec, with *two* sequential annotated loops where our fragment mandates one (the
single-loop body above is the same proof, folded); since Java is largely a syntactic subset of Groovy,
that entry is line-for-line comparable with ours. The
[`verus (rust)`](https://github.com/hwayne/lets-prove-leftpad/tree/master/verus%20(rust)) entry — the tool
whose HumanEval suite the repo already ports — uses a *functional* `spec fn` + a recursive `proof fn`
whose self-call is the induction hypothesis: exactly the recursive-lemma-with-`@Decreases` pattern here.

**The functional sibling.** The repo also has a
[`dafny (functional)`](https://github.com/hwayne/lets-prove-leftpad/tree/master/dafny%20(functional))
entry — no loops, no mutation: a recursion prepending one pad character per step, all four properties as
`ensures` on the function itself, proved by structural induction. The same shape proves here, over
Strings, with Z3's native sequence theory carrying length-of-concat as a theorem:

<!-- doclint:case p206-functional-leftpad/identity-length-by-induction -->
```groovy
@Requires({ pad != null && s != null && pad.length() == 1 })
@Ensures({ (s.length() >= n ==> result == s) &&
           (s.length() < n ==> result.length() == n) })
@Decreases({ n - s.length() })
static String leftpad(String pad, int n, String s) {
    s.length() >= n ? s : leftpad(pad, n, pad + s)
}
```

The honest boundary: the two **character** clauses are mutually inductive — the prefix clause alone
*refutes* (its index `n − |s| − 1` is covered by the recursive call's *suffix* clause, which is exactly
why the Dafny entry states all four `ensures` together — a fact the corpus pins as an instructive refute
case), and the full four-clause spec defeats the solver's timeout (seq-`nth` quantifiers under induction;
pinned as a boundary case that fails loudly if a future solver win flips it). So the functional twin
carries identity + length by induction; the character clauses are where the imperative port's loop
invariants earn their keep.

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
predicate Valid()     // Dafny
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
conjuncts expand over the domain (the **symbolic-N** form follows once the enum machinery is on the
table). The paper gives the system twice — **Model 1**, atomic events as mutating
*methods* on a class, and **Model 2** (Section 7), events as TLA⁺-style *two-state predicates* — and both
verify below. Model 2 comes first here, out of the paper's order, because it is the shape the liveness
development builds on: each atomic event a **two-state predicate**, each proof an **empty-bodied lemma** —
the same law-lemma shape the [lattice/monoid arcs](checkers.md) use. `Valid` and `MutualExclusion` become:

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

Two details are worth calling out. First, `Process` is a fixed enum, so this block is the **N = 2
instance**; the symbolic-N form — int-indexed processes, the skolemization Leino's finite `set<Process>`
admits — closes that gap below. Second, `mutualExclusion` keeps `p` and `q` **symbolic**, exactly as the paper writes
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

With the invariant chain established, **Model 1** — the paper's *first*, imperative formulation, atomic
events as **mutating methods** on a class whose state is the ticket dispenser, the display, and the two
process maps, with `Valid()` as the class invariant — verifies too, exactly as he writes it: the invariant is
assumed on entry to each event and checked restored at exit, with the map assignments modelled as
value-store + key-set updates:

<!-- doclint:case p186-map-mutation/leino-ticket-lock-model-1-all-three-events-preserve-valid -->
```groovy
@Invariant({ serving <= ticket &&
    (cs[Phil.A] != CS.Thinking ==> (serving <= t[Phil.A] && t[Phil.A] < ticket)) &&
    (cs[Phil.B] != CS.Thinking ==> (serving <= t[Phil.B] && t[Phil.B] < ticket)) &&
    ((cs[Phil.A] != CS.Thinking && cs[Phil.B] != CS.Thinking) ==> t[Phil.A] != t[Phil.B]) &&
    (cs[Phil.A] == CS.Eating ==> t[Phil.A] == serving) &&
    (cs[Phil.B] == CS.Eating ==> t[Phil.B] == serving) })
class Ticket {
    enum Phil { A, B }
    enum CS { Thinking, Hungry, Eating }
    int ticket
    int serving
    Map<Phil,CS> cs
    Map<Phil,Integer> t
    @Requires({ cs[p] == CS.Thinking })
    void request(Phil p) { t[p] = ticket; ticket = ticket + 1; cs[p] = CS.Hungry }
    @Requires({ cs[p] == CS.Hungry })
    void enter(Phil p) { if (t[p] == serving) cs[p] = CS.Eating }
    @Requires({ cs[p] == CS.Eating })
    void leave(Phil p) { serving = serving + 1; cs[p] = CS.Thinking }
}
```

A dispenser that fails to advance (`request` without `ticket = ticket + 1` — the same bug the TLA⁺ model's
`TicketBad` variant plants) **refutes the class invariant**: the compile-time twin of TLC's
two-philosophers-Eating trace. So both of the paper's formulations now verify — Model 1 for the imperative
reading, Model 2 (above) as the base the liveness development builds on.

**Any-N safety.** The enum bound is not where the safety story ends: processes int-indexed
`0..<N` with `N` symbolic, `cs`/`t` as functions (control states as ints — 0 Thinking, 1 Hungry,
2 Eating), and `valid` in Leino's own quantified spelling — the per-process bound a bounded `every` over
the symbolic domain, ticket uniqueness a **nested** `every`:

<!-- doclint:case p198-any-n-safety/mutual-exclusion-for-any-n-helper-valid -->
```groovy
static boolean valid(int N, int ticket, int serving, Function<Integer,Integer> cs, Function<Integer,Integer> t) {
    cs != null && t != null && serving <= ticket &&
    (0..<N).every { int r -> cs(r) != 0 ==> (serving <= t(r) && t(r) < ticket) } &&
    (0..<N).every { int r1 -> (0..<N).every { int r2 ->
        (r1 != r2 && cs(r1) != 0 && cs(r2) != 0) ==> t(r1) != t(r2) } } &&
    (0..<N).every { int r -> cs(r) == 2 ==> t(r) == serving }
}
@Requires({ 0 <= p && p < N && 0 <= q && q < N &&
    valid(N, ticket, serving, cs, t) && cs(p) == 2 && cs(q) == 2 })
@Ensures({ p == q })
static void mutualExclusion(int N, int ticket, int serving,
                            Function<Integer,Integer> cs, Function<Integer,Integer> t, int p, int q) {}
```

Mutual exclusion and all three transition preservations (`Request`/`Enter`/`Leave`, each framing the other
`N − 1` processes in one quantified conjunct) verify for **any** `N`; drop uniqueness and mutual exclusion
refutes with `N = 2, p = 0, q = 1`, drop the strict dispenser bound and `Request` refutes — the paper's
invariant-strengthening story, now at any process count. (The refute twin here also caught — and fixed — a
real engine unsoundness in how boolean helpers unfolded inside quantifier closures; the verify-and-refute
discipline at work.)

Leino's second half is **liveness** — *a hungry process eventually eats* (Section 7.6). It is genuinely
surprising that an SMT-backed *sequential* checker can touch it at all, and the reason is Leino's: the liveness
proof **is an algorithm** — a proof-loop that walks a well-founded measure down to zero — so it needs no
temporal-logic engine: a ranking function, and ordinary recursion with a `@Decreases` measure to walk it down
(the recursion comes further below, once there is a trace to walk). The ranking function is **`t[p] - serving`**:
the number of "serving"-display turns between a waiter `p` and its ticket, and its properties verify as
empty-bodied lemmas — bounded below, strictly decreased by `Leave` and unchanged by the other events, always with
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
case. One more joins them before the composition: the finiteness that makes it *bounded*, provable as a plain
**state invariant** with no trace in sight. Add the **counting invariant** `ticket - serving == (#non-thinking
processes)` (each dispensed-but-unserved ticket is one waiting/eating process; maintained by every event), and
a waiter's measure is provably **`t[p] - serving <= 1`** for the two-process lock: **a waiting process is
overtaken at most once before it enters** — *bounded bypass*, a liveness property stronger than mere eventual
entry, since it bounds the wait. Composed with the ranking function above (each `Leave` decreases the
measure), from any `Hungry` state at most one competitor `Leave` stands between the waiter and eating; drop
the counting invariant and the bound refutes — the dispenser could run arbitrarily far ahead of the display.

Composing the ingredients into an **eventually-eats** means reasoning about the system state *over time*, which Leino
models as functions `serving`, `t[p]`, `cs[p] : nat → …`. groovy-verify models those as uninterpreted functions
(`Function`-typed, applied as `f.apply(i)` — which the lemmas below write with Groovy's call-operator shorthand
`f(i)`, sugar for the same SAM `apply`): a numeric-returning `Function`'s application is a stable, shared Int-sorted
term that partakes in integer arithmetic, so per-step reasoning over the trace composes. Using bounded bypass to pin
the horizon at a *constant*, a **bounded eventually-eats verifies**: a Hungry process at
measure one has the served process leave (`serving` advances, so the waiter's measure hits zero — *derived*, not
assumed), then its `Enter` fires, and it is Eating two trace steps later. Drop the `Enter` step and it refutes.

The **fair-schedule** eventually-eats rests on **recursive-lemma induction** over trace functions: a recursive
call's `@Ensures` serves as the induction hypothesis — exactly how Dafny discharges the loop, not by proving the
closed form (the direct telescoping `serving(k) == serving(0) + k` does not close) but by a recursion the solver
checks one step at a time. Leino's `GetNextStep` frame argument is then expressible — a trace value frozen
step-by-step across a window is unchanged end-to-end, by a recursive lemma over the window:

<!-- doclint:case p174-fair-liveness/windowed-frame-lemma-via-recursive-induction -->
```groovy
@Requires({ n <= u && (n..<u).every { int i -> csF(i + 1) == csF(i) } })
@Ensures({ csF(u) == csF(n) })
@Decreases({ u - n })
static void frame(Function<Integer,Integer> csF, int n, int u) {
    if (n < u) frame(csF, n + 1, u)
}
```

That frame lemma — with a stability twin for `serving` — is what makes
**`Liveness` verify with progress derived from fairness, not assumed.** The base case is the waiter already
holding the served ticket: given a fairness witness `u` (a later time it is scheduled), it stays ready across
`[n, u)` (the frame lemma for its state, a stability lemma for `serving`), so its `Enter` fires at `u` and it is
`Eating` at `u + 1`. The other case — the **overtaken** waiter (measure 1) — is Leino's loop body: it first follows
the served process out of the kitchen, whose `Leave` advances `serving` by one; composing the frame and stability
lemmas with that step drops the waiter's measure to zero (`reduceMeasure1`), reducing to the base case
(`overtakenEats`). Bounded bypass caps the measure at ≤ 1, so those two cases are **exhaustive** and the two-process
`eventually-eats` is **complete** — mirroring Leino's loop (base case = exit, reduction = one body iteration, ≤ 1
bound = at most one iteration), so no unbounded trace loop is needed.

That is the **two-process development complete** — the ranking function, bounded bypass, and the
fair-schedule eventually-eats (base case *and* the measure-1 reduction), verifying structure-for-structure
with the paper. The rest of the section lifts it to any process count.

**The any-N trace loop.** What is specific to two processes above is only the ≤ 1 measure bound, which turned
Leino's `Liveness` loop into a two-case split. The loop itself also proves, for a **symbolic** measure `k` —
hence any process count:

<!-- doclint:case p197-any-n-liveness/advanceto-the-trace-loop-over-symbolic-rounds -->
```groovy
@Requires({ vF != null && servingF != null && 0 <= m && m <= k &&
    (0..<k).every { int j -> vF(j) + 1 <= vF(j + 1) } &&
    (0..<k).every { int j -> servingF(vF(j) + 1) == servingF(vF(j)) + 1 } &&
    (0..<k).every { int j -> (vF(j) + 1..<vF(j + 1)).every { int i -> servingF(i + 1) == servingF(i) } } })
@Ensures({ servingF(vF(m)) == servingF(vF(0)) + m })
@Decreases({ m })
static void advanceTo(Function<Integer,Integer> vF, Function<Integer,Integer> servingF, int k, int m) {
    if (m > 0) {
        advanceTo(vF, servingF, k, m - 1)
        stableServing(servingF, vF(m - 1) + 1, vF(m))
    }
}
```

`advanceTo` is the trace loop: recursion over a symbolic number of serving-advance rounds (`@Decreases m`),
where the per-round window facts arrive as a **nested bounded quantifier** — an `every` over
witness-function bounds inside an `every` over rounds — instantiated at `j = m − 1` on each step to feed the
window lemma. A companion `reduceMeasureK` does the k-fold measure descent (a waiter framed across a window
in which `serving` advanced `k` times lands at measure 0 — pure arithmetic once framing holds), and the
composition chains it into the base case above: a waiter at **any** measure `k` reaches `Eating`. The
teeth hold at both ends: one advance short and the reduction refutes; a round that fails to advance
`serving` and the trace loop's walk refutes. The hypotheses keep the development's skolemized-witness
posture — the advance times `vF(j)` are supplied as witnesses, exactly as the two-process lemmas take
scheduled times.

The derivation goes one round deeper still: with processes nameable (the any-N indexing from the safety
section), the round **holder** `hF(j)` enters the picture, and the advance becomes a **conclusion** — per-round fairness says
the holder is scheduled at its round's time (`schedF(vF(j)) == hF(j)`), the step implication says a
scheduled holder's `Leave` advances `serving`, and the trace loop chains the modus ponens per round
(`advanceDerived`), with the full `holderEats` composition taking a `Hungry` waiter at any measure to
`Eating`.

**The finale: liveness from the transition relation.** With the time×process state `cs(i, r)`
expressible (the 2-ary apply — `BiFunction.apply` as a two-argument UF, with the `cs(i, r)` shorthand),
the lock's transition relation is spelled directly — per-step frame as a nested `every` (everyone but
`schedF(i)` unchanged), `serving` stable unless the scheduled process eats, the scheduled eater's `Leave`
advancing it, the hungry holder's `Enter` — and the whole liveness chain is **derived** from it. `oneRound`
takes a hungry holder through its scheduled `Enter` and `Leave` (the framing and stability lemmas
recursive, the steps instantiated from the relation — the step implication is now a *theorem*);
`roundsAdvance` is the trace loop over `k` such rounds; and the last lemma finishes with the waiter's own
`Enter`:

<!-- doclint:case p201-transition-relation/hungryeats-hungry-to-eating-all-derived -->
```groovy
@Ensures({ cs.apply(w + 1, A) == 2 })
static void hungryEats(BiFunction<Integer,Integer,Integer> cs, BiFunction<Integer,Integer,Integer> tk,
                       Function<Integer,Integer> servingF, Function<Integer,Integer> schedF,
                       Function<Integer,Integer> sF, Function<Integer,Integer> uF,
                       Function<Integer,Integer> vF, Function<Integer,Integer> hF, int A, int k, int w) {
    roundsAdvance(cs, tk, servingF, schedF, sF, uF, vF, hF, k, k)
    holderFrame(cs, tk, schedF, A, sF(0), w)
    stableNoEat(cs, servingF, schedF, sF(k), w)
}
```

**`Hungry → Eating`, for any measure — hence any process count — from `IsTrace` + fairness witnesses +
holder identities alone.** The teeth hold: a relation whose `Leave` does not advance `serving` refutes the
round, and an interior eater breaks the stability derivation. What stays skolemized, by design rather than
limitation: the fairness *witnesses* (the schedule times) and the holder *identities* — the ∃-half of
fairness, which the fragment's posture never inverts into a search. That is the same trade Leino's `lemma
GetTicketHolder` makes when it *returns* the holder rather than merely asserting one exists. KRML260 —
safety in both of the paper's formulations and at both scales (enum-bounded and symbolic-N), the ranking
function, bounded bypass, and the fair-schedule liveness with every round's progress derived — is closed.



**The rung-2 companion.** Because the artifact here is a *model* of the protocol — in either formulation —
rather than a threaded implementation, its natural second rung is a **model checker**, not a stress test. [`src/tlc/Ticket.tla`](../src/tlc/Ticket.tla)
transcribes the same state machine into **TLA⁺**, and `./gradlew tlcTicket` has **TLC** enumerate every
interleaving at N = 3 (179 states): mutual exclusion, the same strengthened `valid` invariant, and the
fair-schedule `Hungry ~> Eating` all hold; a broken-dispenser variant prints the two-processes-Eating trace.
That does three things the proof can't: it **validates the frame/fairness facts the liveness proof assumes**
(TLC derives them from the transition system rather than taking them as `@Requires`), it **reaches N = 3** where
the symbolic liveness composition is witness-parameterised, and it confirms the invariant exhaustively — the "two independent
methods, one artifact" pairing (see [`CONCURRENCY.md`](../CONCURRENCY.md) rung 2).

