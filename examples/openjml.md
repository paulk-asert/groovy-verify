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

# OpenJML examples


[OpenJML](https://www.openjml.org/) is the JML verifier for Java — the closest existing tool to
this one on the JVM, and named as prior art above. Its [examples page](https://www.openjml.org/examples/)
collects small, self-contained proofs chosen to each show *one* idea. Two of them have been ported here.
Examples ported from openjml.org are © their authors, used under the page's **CC BY-NC** terms.

The first is already above, in **Act 3**: the [BitVectors tutorial](https://www.openjml.org/tutorial/BitVectors)
— round a number up to the next multiple of a power of two with `(n + 0xF) & ~0xF`, proven against the
arithmetic spec it's meant to implement, counterexample at `Integer.MIN_VALUE` and all. The second is here.

### Max by elimination — a disjunctive loop invariant

Find the index of a maximum element, but not by the usual running-best scan. Instead, hold a window
`[x, y]` over the array and shrink it from whichever end is no larger, until it collapses to a single
index. The OpenJML original (`MaxByElimination`) is a worked example of an invariant that most first
attempts get *wrong*:

```java
//@ requires a.length > 0;
//@ ensures 0 <= \result && \result < a.length;
//@ ensures (\forall int i; 0 <= i && i < a.length; a[i] <= a[\result]);
int max(int[] a) {
    int x = 0, y = a.length - 1;
    //@ maintaining 0 <= x && x <= y && y < a.length;
    //@ maintaining (\forall int i; 0<=i && i<x; a[i] <= a[y]) && (\forall int i; y<i && i<a.length; a[i] <= a[y])
    //@            || (\forall int i; 0<=i && i<x; a[i] <= a[x]) && (\forall int i; y<i && i<a.length; a[i] <= a[x]);
    //@ decreasing y - x;
    while (x != y) { if (a[x] <= a[y]) x++; else y--; }
    return x;
}
```

The Groovy is the same proof, structure for structure:

<!-- doclint:case p104-openjml/max-by-elimination-result-indexes-a-maximum -->
```groovy
@Requires({ a != null && a.length > 0 })
@Ensures({ 0 <= result && result < a.length && Forall.range(0, a.length) { int i -> a[i] <= a[result] } })
static int max(int[] a) {
    int x = 0
    int y = a.length - 1
    @Invariant({ 0 <= x && x <= y && y < a.length &&
        ((Forall.range(0, x) { int i -> a[i] <= a[y] } && Forall.range(y + 1, a.length) { int i -> a[i] <= a[y] }) ||
         (Forall.range(0, x) { int i -> a[i] <= a[x] } && Forall.range(y + 1, a.length) { int i -> a[i] <= a[x] })) })
    @Decreases({ y - x })
    while (x != y) { if (a[x] <= a[y]) x = x + 1 else y = y - 1 }
    return x
}
```

The lesson the example exists to teach is the shape of that invariant. It is **disjunctive**: at every
step the maximum-so-far sits at *one* of the two endpoints — but which one isn't fixed, it flips each time
the window shrinks from the other side. A single-disjunct invariant (`everything ≤ a[x]`) isn't preserved
when you advance `x`; you genuinely need the *or*. The engine carries the disjunction through preservation
and then, at loop exit where `x == y`, collapses both arms onto the same index to discharge the
postcondition `∀i. a[i] ≤ a[result]`. `@Decreases({ y - x })` proves termination. Flip the postcondition to
claim `result` indexes a *minimum* and it refutes — the proof rests on the maximum direction of the
invariant, not on the loop merely running.

### ChangeCase — the same proof, on the array theory

OpenJML's `ChangeCase` upper-cases a buffer character by character. The natural Groovy — build a `String` by
concatenation in a loop — is the one shape Z3's string theory *can't* carry: a content invariant over `str.++`
(`∀i. r.charAt(i) == …`) times out, because re-establishing a quantified fact across each concat is a
quantifier-on-quantifier induction its seq solver won't close (measured: stuck even with a hand-supplied
`nth`-of-concat lemma and a 30s budget). The *same* content invariant over an **array** discharges at once —
Z3's array theory is exactly where the engine's quantified-loop machinery already lives (it's how **Act 5**'s
matrix fill proves `∀. a[it] == 0`). So spell the buffer as a `char[]` (an Int-element array — `char` is
integral) and ChangeCase falls straight out, with no new engine support beyond folding the char literal:

<!-- doclint:case p106-char-seq/functional-changecase-upper-verifies -->
```groovy
@Requires({ a != null })
@Ensures({ result.length == a.length &&
    (0..<a.length).every { result[it] == ((a[it] >= ('a' as char) && a[it] <= ('z' as char)) ? (char)((int) a[it] - 32) : a[it]) } })
static char[] upper(char[] a) {
    char[] r = new char[a.length]
    int i = 0
    @Invariant({ 0 <= i && i <= a.length && r.length == a.length &&
        (0..<i).every { r[it] == ((a[it] >= ('a' as char) && a[it] <= ('z' as char)) ? (char)((int) a[it] - 32) : a[it]) } })
    @Decreases({ a.length - i })
    while (i < a.length) {
        if (a[i] >= ('a' as char) && a[i] <= ('z' as char)) r[i] = (char)((int) a[i] - 32)
        else r[i] = a[i]
        i = i + 1
    }
    return r
}
```

The whole element-wise postcondition proves — `result` *is* the upper-cased copy, not merely "has no lowercase
left" — and dropping the lowercase guard from the spec refutes. Two Groovy spelling notes: `('a' as char)` is
the char literal (no primitive char syntax exists, and `char >= String` doesn't type-check), and the
arithmetic is `(char)((int) a[i] - 32)` because `char[]` subscripts box to `Number`. The seq-vs-array split is
the real lesson — *the same proof, opposite tractability, decided by which theory you hand Z3.*

