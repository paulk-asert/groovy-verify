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

# groovy-verify

An SMT-backed verification extension for Groovy, packaged as a standalone
type-checking extension. Annotate code with stock
[`groovy.contracts`](https://github.com/spockframework/groovy-contracts) contracts,
compile a caller under

```groovy
@TypeChecked(extensions = 'verification.VerifyChecker')
```

and Z3 discharges the proof obligations **at compile time** — before the
runtime contract checks would ever fire. Failed proofs surface as ordinary
compile errors with Dafny-style counterexamples.

This started life as the verification spike in the *groovy6-functional* blog
companion repo. It was split out so it can grow on its own; that repo now
consumes it (via a Gradle composite build) rather than vendoring it.

## Examples

Each snippet below is compiled under `@TypeChecked(extensions = 'verification.VerifyChecker')`,
so the proofs run at **compile time**. The contracts are stock `groovy.contracts`
annotations, so the same `@Requires`/`@Ensures`/`@Invariant` still execute as ordinary
runtime checks when verification is off.

**Postconditions — the contract is the spec.** Z3 proves the body satisfies `@Ensures`:

```groovy
@Ensures({ result >= a && result >= b })
static int max(int a, int b) { a >= b ? a : b }
```

Get the body wrong — return the *smaller* (`a >= b ? b : a`) — and the proof fails at compile
time with an input that breaks it:

```
[Static type checking] - Cannot prove postcondition of max holds on this return path
    ensured: ((result >= a) && (result >= b))
    counterexample: a = -1, b = 0
    fails on: max(-1, 0)
```

**Loop invariants & termination.** The invariant carries the proof across iterations and
`@Decreases` shows the loop ends — so the postcondition `result == n` is *proven of the
computed value*, not assumed. (Recursion is handled the same way: a method-level
`@Decreases` lets the method's own `@Ensures` serve as the inductive hypothesis at the
recursive call.)

```groovy
@Requires({ n >= 0 })
@Ensures({ result == n })
static int countUp(int n) {
    int i = 0
    @Invariant({ 0 <= i && i <= n })
    @Decreases({ n - i })
    while (i < n) { i = i + 1 }
    return i
}
```

**Bounded quantifiers over arrays — in the idiom you'd already write.** A *sorted*
precondition (every element ≤ its successor) lets the checker conclude adjacent elements
are ordered. The quantifier is plain GDK Groovy, so the runtime contract evaluates it too:

```groovy
@Requires({ (0..<a.length - 1).every { a[it] <= a[it + 1] } && 0 <= k && k + 1 < a.length })
@Ensures({ result <= 0 })
static int diff(int[] a, int k) { a[k] - a[k + 1] }
```

Drop the `every { … }` precondition and the claim no longer holds — and the counterexample is
a concrete array, with the offending elements reconstructed (here a decreasing adjacent pair):

```
[Static type checking] - Cannot prove postcondition of diff holds on this return path
    ensured: (result <= 0)
    counterexample: a.length = 2, k = 0
    fails on: diff([21239, 21238] as int[], 0)
```

**Lists and boxed types — same reasoning, same syntax.** The encoder never inspects whether a value
is `int` or `Integer`, or whether a sequence is an `int[]` or a `List` — it models every integer type
as a mathematical integer and any subscripted, sized receiver as its contents. So `max` above proves
identically declared `Integer max(Integer a, Integer b)`, and the sorted-`diff` holds verbatim over a
`List<Integer>`, in the same idiom (`xs[i]`, `xs.size()`):

```groovy
@Requires({ (0..<xs.size() - 1).every { xs[it] <= xs[it + 1] } && 0 <= k && k + 1 < xs.size() })
@Ensures({ result <= 0 })
static int diff(List<Integer> xs, int k) { xs[k] - xs[k + 1] }
```

A `List<String>` index is bounds-checked the same way — the element type is irrelevant to the access.
This covers list *index* read and subscript update today; the method-call idioms (`xs.get(i)` /
`xs.set(i, v)`), size-changing mutation (`add`/`remove`), immutable-list detection, and element
nullability are tracked in the roadmap.

**Object state — instance fields, read and written.** Not just static functions: a method may
read and update its receiver's fields, and the checker threads field state across the write (so
the contract's entry `count` and exit `count` are different values, related by the assignment).
A mutator is proven to maintain its bound:

```groovy
class Counter {
    int count, max
    @Requires({ count < max })
    @Ensures({ count <= max })
    void increment() { count = count + 1 }
}
```

A postcondition can relate the *exit* state to the *entry* state with `old` — `@Ensures({ count
== old.count + 1 })` — and `old` reaches into array contents too, which is how a method frames what
it leaves alone: a setter that touches only `a[j]` proves every other element is unchanged,
`@Ensures({ (0..<a.length).every { it == j || a[it] == old.a[it] } })` (groovy-contracts clones the
field for `old`, so this holds at runtime as well as in the proof).

**Bugs caught at compile time — with a counterexample and a runnable repro.** The implicit
safety obligations (bounds, divide-by-zero, null) need no annotation; an access the checker
can't prove safe fails the build the way the JVM would name it, plus an input that triggers it:

```groovy
static int g(int[] a, int i) { a[i] }   // index never checked
```
```
[Static type checking] - Possible IndexOutOfBoundsException: index may be out of bounds
    obligation: 0 <= i && i < a.size()
    counterexample: a.size() = 0, i = -1
    fails on: g(new int[0], -1)
```

The headline mirrors the exception a developer would actually hit
(`ArithmeticException: Division by zero`, `NullPointerException: Cannot invoke method
size() on null object`, …); the `fails on:` line reconstructs a runnable input — scalars
and a null receiver exact, solver-constrained array elements pinned as literals
(`diff([21239, 21238] as int[], 0)`), contents that don't matter left size-filled
(`new int[3]`).

**Putting it all together — an in-place sort.** Everything above composes into one result: a
recursive in-place insertion sort whose **postcondition** is proven **sorted *and* a permutation of its
input** — the two halves of sorting correctness — with no loops; the recursion *is* the proof, and the
array is mutated in place under a sound `@Modifies` frame (the checker *havocs* the array across each call
and reframes it from the callee's `@Ensures`, so nothing is assumed unchanged for free).

> **Honesty note (Phase 24).** The postcondition (sorted ∧ permutation) and termination verify. The one
> obligation the solver cannot discharge is `insert`'s *recursive precondition* at `insert(m-1, a[m], v)`:
> under sound call-site checking it must prove the swap preserves the sorted prefix *and* the new tight
> `hi`-bound — a two-quantifier proof over a nested-store array that Z3 times out on (valid, but past its
> e-matching). It is reported as a loud "could not decide". (Before Phase 24 it passed *vacuously*, via a
> recursive-call name-conflation; the call-site soundness fix corrected that.) A user-supplied instantiation
> hint / helper lemma is the follow-on to restore it.

Two ghost parameters carry the proof, both ordinary ints the runtime ignores: `hi` is an upper
bound on the active elements (the recursion passes the pivot `a[m]` as the new, tight bound — that
tightness is what lets the order argument go through), and `v` is an arbitrary value whose
*occurrence count* must be preserved (`a.count(v) == old.a.count(v)` for all `v` ≡ same multiset ≡
a permutation). The `every`/`count`/`old` are all plain GDK Groovy, so the same contract is checked
at runtime.

```groovy
@Requires({ 0 <= m && m < a.length &&
            (0..<m - 1).every { a[it] <= a[it + 1] } &&   // prefix sorted
            (0..<m + 1).every { a[it] <= hi } })           // active region bounded by hi
@Modifies({ this.a })
@Ensures({ (0..<m).every { a[it] <= a[it + 1] } &&         // a[0..m] now sorted
           (0..<m + 1).every { a[it] <= hi } &&            // bound preserved
           (m + 1..<a.length).every { a[it] == old.a[it] } && // suffix framed (untouched)
           a.count(v) == old.a.count(v) })                 // permutation
@Decreases({ m })
void insert(int m, int hi, int v) {
    if (m > 0 && a[m] < a[m - 1]) {
        int t = a[m]; a[m] = a[m - 1]; a[m - 1] = t
        insert(m - 1, a[m], v)                              // recurse with the pivot as the bound
    }
}

@Requires({ 0 <= n && n <= a.length && (0..<n).every { a[it] <= hi } })
@Modifies({ this.a })
@Ensures({ (0..<n - 1).every { a[it] <= a[it + 1] } &&
           (0..<n).every { a[it] <= hi } &&
           (n..<a.length).every { a[it] == old.a[it] } &&
           a.count(v) == old.a.count(v) })
@Decreases({ n })
void sort(int n, int hi, int v) {
    if (n > 1) { sort(n - 1, hi, v); insert(n - 1, hi, v) }
}
```

Both *postcondition* halves are checked, not assumed: a "sort" that zeroed the array fails the permutation
clause, and one that left elements out of order fails the sortedness clause — bounded quantifiers, induction
(`@Decreases`), the multiset `count` law, `old` pre-state, and sound `@Modifies` framing, in one proof
(modulo the recursive-precondition could-not-decide noted above).

**Finite sets — membership and a cardinality law.** A `Set<Integer>` is modelled as a characteristic
array (`x in s` is a membership read; `s.add(x)` is a store threaded through the body), so a method's
effect on the set is provable. `s.size()` is an uninterpreted cardinality carrying a per-mutation
*update law* — adding an element that isn't already present grows the size by exactly one — which is
the building block a set-valued termination measure (e.g. DFS over a finite node domain) rests on:

```groovy
class C {
    Set<Integer> s
    @Requires({ !(x in s) })            // x is new …
    @Modifies({ this.s })
    @Ensures({ x in s &&                // … so after add it is a member …
               s.size() == old.s.size() + 1 })   // … and the size grew by one
    void put(int x) { s.add(x) }
}
```

Drop the `!(x in s)` precondition and the `+ 1` no longer holds — `x` might already be present — so
the proof fails with a concrete `put(2)`. Set union/intersection/subset (`s.containsAll(t)`) need an
unbounded quantifier and stay a loud "skipped", never a silent pass.

**Finite maps — a value array plus a key-set.** A `Map<Integer,Integer>` is modelled as its values
(`m[k]` / `m.get(k)`, an array) together with its key domain (`m.containsKey(k)` / `k in m`, a *set*).
A `m.put(k,v)` does both — stores the value and adds the key — so value reads, the key frame, and the
key-set cardinality law all hold at once; and because the key-set is the Phase-16 set, `m.size()`
drives the same DFS-shaped recursive measure over a map's key domain:

```groovy
class C {
    Map<Integer,Integer> m
    @Requires({ j != k })
    @Modifies({ this.m })
    @Ensures({ m[k] == v &&                 // the value just put …
               m.containsKey(k) &&          // … the key is now in the domain …
               m[j] == old.m[j] })          // … every other key is untouched
    void put(int k, int v, int j) { m.put(k, v) }
}
```

`m.containsValue(v)` (a search over the values) needs an unbounded quantifier and stays a loud skip.

**Reachability — a recursive graph traversal, verified.** Sets, maps, induction, and bounded quantifiers
compose into the property a search algorithm is *for*: a depth-first traversal of a functional graph
(`next` is a `Map<Node,Node>` successor) marking nodes in a `Set<Node>`. Two reachability postconditions
hold at once — **soundness** (`visited` only ever grows, a bounded universal over the node domain) and
**progress** (the node handed in ends up visited, while the traversal budget lasts). The recursive call
*havocs* `visited` and reframes it from the callee's `@Ensures` (sound `@Modifies`), and the self-`@Ensures`
is the inductive hypothesis:

```groovy
class C {
    Map<Integer,Integer> next   // functional graph: successor of node u
    Set<Integer> visited
    int n                       // node domain 0..<n
    @Requires({ 0 <= u && u < n && (0..<n).every { 0 <= next[it] && next[it] < n } })
    @Modifies({ this.visited })
    @Decreases({ fuel })
    @Ensures({ (0..<n).every { !(it in old.visited) || (it in visited) } &&   // soundness: visited only grows
               (fuel <= 0 || (u in visited)) })                               // progress: u gets visited
    void visit(int u, int fuel) {
        if (fuel > 0 && !(u in visited)) {
            visited.add(u)
            visit(next[u], fuel - 1)
        }
    }
}
```

The same soundness half also goes through under the set-cardinality measure `@Decreases({ n - visited.size() })`
— the DFS-shaped termination from Phase 16. A traversal that *removes* a node breaks monotonic growth and
refutes.

**The cardinality axiom — `Sets.bounded`.** The uninterpreted set size (Phase 16) knows only its per-mutation
deltas — it has no link to *which* elements a set holds. `Sets.bounded(s, n)` supplies the **pigeonhole**
relationship for a set whose elements live in a finite domain `[0, n)`: it means exactly `s ⊆ [0, n)`, and
lowers to `s.size() <= n && (s.size() < n || (0..<n).every { it in s })` — a faithful boolean definition over
the cardinality and a bounded membership universal (no trusted axiom). From it the engine *derives* the two
facts cardinality-driven search rests on:

```groovy
@Requires({ Sets.bounded(s, n) && s.size() == n && 0 <= u && u < n })
@Ensures({ u in s })                       // FULL ⇒ MEMBER: a full bounded set covers the whole domain
static int f(Set<Integer> s, int n, int u) { 0 }

@Requires({ Sets.bounded(s, n) && 0 <= u && u < n && !(u in s) })
@Ensures({ s.size() < n })                 // HOLE ⇒ NOT FULL: a missing in-domain node means room remains
static int g(Set<Integer> s, int n, int u) { 0 }
```

Drop `Sets.bounded` from either and the claim refutes — without it the (uninterpreted) size says nothing
about membership. The `HOLE ⇒ NOT FULL` fact is exactly what a cardinality-terminating DFS needs at its
coverage branch.

**The honest boundary.** *Completeness* (every reachable node visited — the closure fixpoint) needs the DFS
frontier/stack invariant, not a simple inductive set property. And *whole-traversal* unconditional
`start ∈ visited` still isn't closed: `Sets.bounded` gives the pigeonhole *consequences*, but **preserving**
boundedness across the add that fills the set needs the converse counting (`|s| = n-1 ⇒ exactly one hole`),
which wants the bounded-sum cardinality below.

**Bounded-sum cardinality — `bcount`, earned by induction.** The genuine count of a set's members in a
domain, `bcount(s,k) = Σ_{i<k} (i ∈ s ? 1 : 0)`, is just an ordinary recursive method — and its foundational
properties are proved by the framework's *own* induction (`@Decreases` on `k`, the self-`@Ensures` as the
hypothesis), no built-in axiom:

```groovy
@Requires({ k >= 0 })
@Ensures({ 0 <= result && result <= k })          // the BOUND — the converse counting `card` lacked
@Decreases({ k })
static int bcount(Set<Integer> s, int k) {
    if (k == 0) return 0
    int rest = bcount(s, k - 1)
    return rest + ((k - 1) in s ? 1 : 0)
}
```

The same shape with `@Requires({ (0..<k).every { it in s } })` proves `result == k` — **full domain ⇒ count
= k**, tying the count to actual membership. Break the recursion (`rest + 2`) and the bound refutes. These are
the converse-counting facts the uninterpreted `card` and the definitional `Sets.bounded` couldn't reach.

**The per-add law — `Sets.count` as a primitive.** The recursive `bcount` *earns* its bound by induction but
is opaque across a method boundary (and can't take `s ∪ {u}` as an argument), so it can't thread a count
*through a mutation*. `Sets.count(s, k)` is the same bounded count as a **primitive** — carrying its bound
axiom, and, at every set mutation, the bcount analogue of the per-store `count` law (Phase 12):
`Sets.count(s∪{u}, k) = Sets.count(s, k) + (0 <= u < k ∧ u ∉ s ? 1 : 0)`. So a fresh in-domain add raises the
count by exactly one:

```groovy
@Requires({ 0 <= u && u < k && !(u in s) })
@Modifies({ this.s })
@Ensures({ Sets.count(s, k) == Sets.count(old.s, k) + 1 })
void put(int u, int k) { s.add(u) }
```

Drop the freshness guard and the `+ 1` refutes; add an element *outside* `[0, k)` and the count is
unchanged (the law's domain guard); `remove` of a present in-domain element decrements it.

**The capstone — DFS proves unconditional coverage.** The last piece is the **full-characterization**:
`Sets.count(s, k) == k ⟺ (0..<k).every { it ∈ s }` — a full count over a `k`-slot domain forces every node
in (the converse of Phase 20's *full ⇒ count*). Both directions are theorems of the count, so the encoder
asserts the iff for every `Sets.count` term. With it, a **cardinality-terminating** DFS proves the node it is
handed ends up visited — *unconditionally*, no fuel bound — the property that was the honest boundary two
phases ago:

```groovy
class C {
    Map<Integer,Integer> next         // functional graph
    Set<Integer> visited
    int n
    @Requires({ 0 <= u && u < n && (0..<n).every { 0 <= next[it] && next[it] < n } })
    @Modifies({ this.visited })
    @Decreases({ n - Sets.count(visited, n) })          // strictly decreases — the per-add law
    @Ensures({ (u in visited) &&                         // ← UNCONDITIONAL coverage
               (0..<n).every { !(it in old.visited) || (it in visited) } })
    void visit(int u) {
        if (!(u in visited) && Sets.count(visited, n) < n) {
            visited.add(u)
            visit(next[u])
        }
    }
}
```

Termination is `n - Sets.count(visited, n)` (the per-add law makes it drop by one on a fresh add); coverage
closes at the "set full" branch, where `Sets.count(visited, n) == n` forces — via the full-characterization —
every domain node, `u` included. It composes *everything*: sets, the functional-graph map, induction,
caller-side set framing, bounded quantifiers, the per-add law, and the full-characterization.

**What remains — completeness.** We prove the node itself is covered, **not its successors**: claiming
`next[u] in visited` refutes, because a node visited earlier needn't have had its edge followed. Completeness
(*every reachable node is visited*) is the closure fixpoint; a run at it (Phase 23) proves the inductive **step**
— a set closed under `next` covers the successor of any visited node (`closure ∧ u∈visited ⊢ next[u]∈visited`) —
and maps the three obstacles to the full result: **(1)** iterating that step needs recursive-definition reasoning
in contracts (the same gap `bcount` cross-lemma use hits); **(2)** the DFS *establishing* closure needs the
frontier/stack invariant (a plain `mark` provably breaks closure — the new node's successor isn't visited yet —
so closure can't be a simple invariant); **(3)** the run also surfaced a call-site soundness fix to make first —
`verifyCallSite` doesn't replay intervening straight-line mutations before a callee's precondition, so a naive
closure-threading DFS would pass spuriously. See the roadmap's Phase 23 for the details.

## What's demonstrated

The examples above are a slice; here is the full inventory of what the engine proves today, by phase:

| Capability | Authoring | Status |
|---|---|---|
| Preconditions discharged at call sites | `@Requires` | ✅ |
| Postconditions vs. method body | `@Ensures` | ✅ |
| Loop invariants & termination | `@Invariant` / `@Decreases` | ✅ |
| **Array/list index in bounds** | *(implicit)* | ✅ Phase 1 |
| **Division / modulo by zero** | *(implicit)* | ✅ Phase 1 |
| **Null dereference** | *(implicit)* | ✅ Phase 1 |
| **`xs.size()` / `xs.length` / `xs.isEmpty()`** in contracts | `@Requires`/`@Ensures` | ✅ Phase 4 |
| **`x == null` / `x != null`** nullity in contracts | `@Requires`/`@Ensures` | ✅ Phase 4 |
| **`x.equals(y)`** (numeric `==`) | `@Requires`/`@Ensures` | ✅ Phase 4 |
| **`xs.contains(y)`** (precise membership over contents) | `@Requires`/`@Ensures` | ✅ Phase 4 / 9 |
| **Cross-boundary nullity/size at call sites** | `@Requires` | ✅ Phase 4 |
| **Value-flow: safety implied by an assignment** | *(implicit)* | ✅ Phase 5 |
| **Loop-fused bounds (obligation under `@Invariant`)** | *(implicit)* | ✅ Phase 5 |
| **Short-circuit guard path conditions** | `i > 0 && a[i - 1] < a[i]` | ✅ Phase 5 |
| **Bounded-universal quantifiers over arrays** | `Forall.range(lo, hi) { … a[it] … }` | ✅ Phase 6 |
| **Native GDK quantifier idioms** | `(lo..<hi).every{…}`, `xs.indices.every{…}`, `xs.every{ it… }` | ✅ Phase 9 |
| **Existential quantifier (`any`)** | `a.any{ it < 0 }`, `(lo..<hi).any{…}` | ✅ Phase 9 |
| **Array contents: read (`select`) & update (`store`)** | `a[i]` in contracts / `a[i] = v` | ✅ Phase 6 |
| **Array update inside a loop (invariant over contents)** | `a[i] = v` in a `@Invariant`-carrying loop | ✅ Phase 6 |
| **Inter-procedural: assume a callee's `@Ensures`** | `int z = f(args)` | ✅ Phase 7 (slice 1) |
| **Recursion by induction (self-`@Ensures` + termination)** | `@Decreases({ n })` on a method | ✅ Phase 7 (slice 2) |
| **Lemmas: prove a `void` method by induction, call to apply** | `lemma(args)` as a statement | ✅ Phase 7 (slice 3) |
| **Flow-sensitive precondition (use the preceding call's `@Ensures`)** | `sort(a, n-1); insert(a, n-1)` | ✅ Phase 7 (slice 4) |
| **Recursive insertion sort — *sortedness*, end-to-end** | `insert` + `sort` by induction | ✅ Phase 7 |
| **Closed-constant folding (normalise-then-SMT)** | `(2 + 2) * (2 + 2)`, `a[(1 + 1) * 2]` | ✅ Phase 8a (slice 1) |
| **Closed pure-function evaluation** | `pow2(10)`, `factorial(5)` in a contract/body | ✅ Phase 8a (slice 2) |
| **Bounded symbolic unfolding (fuel) + `ite`** | `absV(x)`, `pow2(n)` against a symbolic arg | ✅ Phase 8a (slice 3) |
| **Instance methods & field state (read + write)** | `this.count`, `count = count + 1` | ✅ Phase 10 |
| **Pre-state `old` (field & array-content snapshots)** | `old.count`, `old.a[i]` in `@Ensures` | ✅ Phase 11 |
| **Multiset / `count` preservation (per-store law)** | `a.count(v) == old.a.count(v)` | ✅ Phase 12 |
| **`@Modifies` framing — frame-check + caller-side havoc & sound inter-proc `old`** | `@Modifies({ this.a })` | ✅ Phase 13 |
| **In-place sort — *sorted ∧ permutation* postcondition + termination** | recursive insertion sort under sound `@Modifies` (its recursive *precondition* is a could-not-decide under Phase 24 — see below) | ✅ Phase 14 / ⚠️ Phase 24 |
| **Class `@Invariant` — instance methods (assume on entry, prove on exit, super-walked)** | `@Invariant({ count >= 0 })` on a class | ✅ Phase 15a |
| **Boxed scalars & index-accessed collections** | `Integer`, `Integer[]`, `List<Integer>` via `xs[i]` / `xs.size()` | ✅ (structural) |
| **Finite sets — membership, add/remove, cardinality law** | `x in s`, `s.contains(x)`, `s.add(x)`, `s.size()` over `Set<Integer>` | ✅ Phase 16 |
| **Set-cardinality `@Decreases` measure (DFS-shaped termination)** | `@Decreases({ n - s.size() })` on a recursion that adds a fresh element | ✅ Phase 16 |
| **Finite maps — lookup, key membership, put, key-set cardinality law** | `m[k]`, `m.get(k)`, `k in m`, `m.containsKey(k)`, `m.put(k,v)`, `m.size()` over `Map<Integer,Integer>` | ✅ Phase 17 |
| **Reachability — recursive graph traversal: visited grows (soundness) + node covered (progress)** | DFS over a `Map<Node,Node>` graph marking a `Set<Node>`, fuel- or cardinality-terminated | ✅ Phase 18 |
| **Cardinality axiom — pigeonhole over a bounded domain** | `Sets.bounded(s, n)` ⇒ `s.size() <= n`, full ⇒ covers `[0,n)`, a hole ⇒ not full | ✅ Phase 19 |
| **Bounded-sum cardinality `bcount(s,k)` — bound & full-count, earned by induction** | recursive `bcount`; `0 <= bcount(s,k) <= k` and `(0..<k).every{it in s} ⇒ bcount==k` | ✅ Phase 20 |
| **`Sets.count(s,k)` primitive + per-add law** | a set mutation threads the bounded count: a fresh in-domain `add` raises `Sets.count(s,k)` by one | ✅ Phase 21 |
| **Full-characterization `count==k ⟺ covers [0,k)` — and end-to-end DFS unconditional coverage** | `Sets.count(s,k)==k ⇒ u in s`; a cardinality-terminating DFS proves `start ∈ visited` with no fuel bound | ✅ Phase 22 |
| **Completeness — closure ⇒ successor covered (the inductive step)** | `closure ∧ u∈visited ⇒ next[u]∈visited`; and `mark` breaks closure (boundary) | ✅ Phase 23 (one step) |
| **Call-site precondition soundness** | intervening mutations threaded, fresh callee formals, early-return narrowing — a precondition is checked at the *state at the call* | ✅ Phase 24 |
| List method-call idioms (`xs.get`/`set`/`add`), size-changing mutation, immutable-list detection, element nullability | — | ⏳ later |
| Set/map union/intersection/subset (`s.containsAll(t)`, `m.containsValue`, `s + t`), non-Int domains, `Map<K, Set<V>>` nesting | — | ⏳ later |
| DFS *completeness* (full: all reachable visited) | — | ⏳ later (recursive-defs in contracts; the frontier/stack invariant) |
| Class `@Invariant` for constructors and cross-class call-site assumption, 32-bit overflow, heap aliasing | — | ⏳ later |

## Building & testing

Requires JDK 25. It builds against `org.apache.groovy:6.0.0-SNAPSHOT` from the
[ASF snapshot repository](https://repository.apache.org/content/repositories/snapshots) —
it relies on some fixes due for release in the next Groovy 6 pre-release.

```sh
./gradlew verify          # compile a battery of good/bad snippets and assert diagnostics
VERIFY_VERBOSE=1 ./gradlew verify   # also print the counterexamples for refuted cases
```

The self-test ([`src/test/groovy/VerifyHarness.groovy`](src/test/groovy/VerifyHarness.groovy))
compiles annotated snippets on the fly and asserts that good ones verify and
bad ones fail with the expected diagnostic.

## Using it in your own build

It isn't on Maven Central yet, but you don't need to wait for that — there are three
ways to consume `au.com.asert:groovy-verify:0.1.0-SNAPSHOT`:

- **Local install.** `./gradlew publishToMavenLocal` drops the jar into your `~/.m2`;
  then add `mavenLocal()` and the dependency to any Gradle/Maven project.
- **Composite build (source dependency).** Clone this repo alongside yours and add
  `includeBuild('../groovy-verify')` to your `settings.gradle` — Gradle substitutes the
  dependency with this project's output, so changes here are picked up without a publish.
  (The companion *groovy6-functional* repo consumes it this way.)
- **JitPack.** Because the build is self-contained (ASF snapshot, no local patch), JitPack
  can build it straight from a GitHub tag/commit — add the JitPack repo and depend on
  `com.github.<owner>:groovy-verify:<tag>`, no publishing step on your side.

Either way the consumer compiles under `@TypeChecked(extensions = 'verification.VerifyChecker')`;
the artifact carries Z3 (via z3-turnkey, native libs bundled) on the compile classpath.

## The fragment

Verification is sound *within* a deliberately small fragment and **loudly
unsound outside it**: anything the encoder cannot model emits a "skipped"
warning rather than passing silently. In expressions the fragment is:

- integer `+`, `-`, and *linear* `*` — a product needs a constant operand, but any
  closed constant subterm is folded first, so `(2 + 2) * (2 + 2)` and `a[(1 + 1) * 2]`
  are fine; `/` and `%` are checked for divide-by-zero but not otherwise modelled;
- comparisons, the boolean connectives `&&`/`||`/`!`, and the conditional `?:` — all
  short-circuit-aware, so a guard's left operand protects accesses in its right
  (`i > 0 && a[i - 1] < a[i]`) and a `?:` branch is checked under its condition;
- the size / nullity / membership oracles from the table above
  (`xs.size()`, `x == null`, `xs.contains(y)`, `x.equals(y)`, `isEmpty()`);
- array/list contents under Z3's array theory (`a[i]` reads, `a[i] = v` updates) with
  bounded-universal quantifiers — `Forall.range` or the native GDK idioms
  `(lo..<hi).every{…}` / `xs.indices.every{…}` / `xs.every{ it… }`;
- finite `Set<Integer>` membership (`x in s`, `s.contains(x)`), mutation (`s.add(x)` /
  `s.remove(x)`, threaded through the body) and cardinality (`s.size()`) — a set is a
  characteristic array, and `size()` carries a per-mutation update law (`add` of an absent
  element raises it by one), which drives a set-valued `@Decreases` measure (`n - s.size()`,
  the DFS-shaped termination argument); union/intersection/subset stay outside the fragment;
- finite `Map<Integer,Integer>` — value lookup (`m[k]`, `m.get(k)`), key membership (`k in m`,
  `m.containsKey(k)`), mutation (`m.put(k,v)` / `m[k] = v`) and size (`m.size()`): a map is a
  value array plus a key-set, so a put both stores the value and adds the key (with the same
  cardinality law), and `m.size()` likewise drives a recursive measure over the key domain;
  `containsValue` / `keySet` / `Map<K,Set<V>>` nesting stay outside the fragment;
- fuel-bounded inlining of contract-free pure functions (a closed call like
  `pow2(10)` is evaluated to a literal, a symbolic one unfolded);
- scalar instance-field reads (`this.count` / bare `count`) in contracts and bodies.

For method bodies: straight-line code, `if`/`else`, locals and instance fields (re-assignable,
tracked in SSA so a mutator's pre/post state differ), and a single annotated `while` loop. See
`Encoder` and the roadmap for the exact boundaries.

## Relationship to Groovy's other checkers

groovy-verify is one of a family of `@TypeChecked` extensions, and it deliberately owns a narrow,
deep slice — SMT-backed *functional* verification. Two things place it: how its null story relates
to Groovy's existing null tooling, and what guards the code its fragment can't yet reach.

### Null handling — three layers, one of them a sibling

Groovy already answers "null" at more than one point in the lifecycle, and it's worth not conflating
them (note especially the runtime `@NullCheck` transform versus the compile-time `NullChecker`):

| Piece | Kind | When | What it does |
|---|---|---|---|
| `@groovy.transform.NullCheck` | AST transform | runtime | injects fail-fast guards on parameters |
| `?.` / `?:` | language operators | runtime | safe-navigation / Elvis |
| **`groovy.typecheckers.NullChecker`** | **type-checking extension** | **compile time** | flow-sensitive nullness via `@Nullable` / `@NonNull` / `@MonotonicNonNull` |
| **groovy-verify** | **type-checking extension** | **compile time** | SMT obligation `recv != null` at each dereference |

The last two are siblings — the same extension SPI — approaching null from opposite ends.
**`NullChecker` is the specialist:** annotation-driven and flow-sensitive (it follows null guards,
early-exit `if (x == null) return`, safe navigation, monotonic fields, non-null-by-default), modelled
on the Checker Framework's Nullness Checker, and it answers *"could this be null here?"* without a
solver. **groovy-verify treats nullity as a by-product** of proving richer properties: it asserts
`¬(recv != null)` and asks Z3, so it catches a dereference when the surrounding logic or a
`@Requires` makes non-nullness *provable* — and returns a refuting input (`g(null, 0)`). It has no
`@Nullable` / `@NonNull` awareness, does not model `?.`, and makes every named-receiver dereference an
unconditional obligation. **For dedicated null-safety, reach for `NullChecker`;** the boxed-element gap
noted earlier (`List<@Nullable String>`) is exactly what its annotations express and ours do not.

Because both are just extensions, they **compose** — nullness-by-annotation and SMT functional
verification in a single compile, each doing what it is best at:

```groovy
@TypeChecked(extensions = ['groovy.typecheckers.NullChecker', 'verification.VerifyChecker'])
```

### Outside the fragment, the code is still guarded

groovy-verify is *loudly* partial: anything outside its fragment is skipped, never silently passed
(see [Non-goals](ROADMAP.md)). Two safety nets mean "skipped" does not mean "unprotected":

- **The contracts still run.** The annotations are stock `groovy.contracts`, so every
  `@Requires` / `@Ensures` / `@Invariant` / `@Decreases` / `@Modifies` that groovy-verify *couldn't*
  discharge at compile time is still enforced as an ordinary **runtime assertion**. A proof we skip
  degrades to a runtime check, not to nothing — and the spec is written once, serving both. Being
  machine-readable and compiler-enforced, those same contracts also read as a specification a human or
  AI agent can reason from without opening the body — even mechanically deriving property-based tests
  (see [*Groovy 6 features for Functional Programmers*](https://groovy.apache.org/blog/groovy6-functional)) — and groovy-verify only sharpens that, since a `@Ensures` it has discharged is *proven*, not merely asserted.
- **Sibling checkers cover orthogonal properties.** The `groovy-typecheckers` module ships a set of
  `@TypeChecked` extensions, each owning a property groovy-verify doesn't model: `NullChecker`
  (nullness), `RegexChecker` (invalid regular expressions caught at compile time), `FormatStringChecker`
  (`printf` / `String.format` argument mismatches), and `PurityChecker` / `ModifiesChecker`
  (`@Pure` / `@SideEffectFree` / `@Contract` side-effect compliance) — the last directly relevant
  here, since groovy-verify's pure-function evaluation (Phase 8a) and `@Modifies` framing (Phase 13)
  *assume* a purity those checkers can actually verify. Others (`CombinerChecker`, `MonadicChecker`, …)
  cover further ground, and they compose the same way. Together the family checks far more than any one
  extension's fragment.

## Architecture

| File | Role |
|---|---|
| `VerifyChecker` | the `@TypeChecked` extension; call-site, body, loop & implicit checks |
| `Encoder` | Groovy expression → SMT (the fragment lives here) |
| `BodyEncoder` / `LoopEncoder` | path enumeration & symbolic execution for `@Ensures`/loops |
| `PureEvaluator` | closed pure-function evaluation & fuel-bounded unfolding — the normalise-then-SMT accelerator (Phase 8a) |
| `Forall` | the `Forall.range(lo, hi){…}` bounded-quantifier helper (the native GDK `every`/`any` idioms are the preferred surface) |
| `PathFacts` | enclosing-`if` path conditions per expression site |
| `ContractExpansionTransform` / `ContractSource` | global CONVERSION transform capturing verbatim contract text (`requires`/`ensures`/`decreases`/`modifies`) + clean body snapshots onto the runtime `@ContractSource` carrier the checker re-parses |
| `SmtBackend` / `Z3Backend` | the solver seam and its z3-turnkey implementation |
| `Reporter` | OpenJML-style diagnostics with inline counterexamples |

`Encoder` is written against the `SmtSession` interface; `Z3Backend` is the only
concrete binding, so an alternative solver is a drop-in.

## License

Apache-2.0.
