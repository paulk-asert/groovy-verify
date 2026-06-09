/*
 * SPDX-License-Identifier: Apache-2.0
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     https://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
import org.codehaus.groovy.control.MultipleCompilationErrorsException
import org.codehaus.groovy.control.messages.ExceptionMessage
import org.codehaus.groovy.control.messages.SyntaxErrorMessage
import verification.Z3Backend

/**
 * Standalone self-test for the verification engine: compiles a battery of
 * annotated snippets on the fly and asserts what VerifyChecker does to each.
 *
 *   - PASS (ok)    : the snippet must compile cleanly (every obligation discharged).
 *   - PASS (error) : the snippet must FAIL to compile with a diagnostic containing
 *                    the expected substring (the checker caught the bug).
 *
 * This replaces the blog repo's per-case demo scripts with one runnable check, so
 * the engine is verifiable in its own repo without the companion demos. Run with:
 *
 *   ./gradlew verify
 */
class VerifyHarness {

    static final String HDR = '''
        import groovy.transform.TypeChecked
        import groovy.contracts.Requires
        import groovy.contracts.Ensures
        import groovy.contracts.Invariant
        import groovy.contracts.Decreases
        import groovy.contracts.Modifies
        import verification.Forall
        import verification.Sets
        import verification.Sorted
        import verification.Fib
        import verification.Trib
        import verification.Gcd
        import verification.CheckOverflow
    '''.stripIndent()

    /** A contracted producer reused by the cross-call precondition cases. */
    static final String PRODUCER = '''
        class P {
            @Requires({ x >= 0 })
            static int sq(int x) { (int) Math.sqrt((double) x) }
        }
    '''.stripIndent()

    /** A producer whose precondition is reference nullity — exercises the cross-boundary nullity oracle. */
    static final String NULLITY_PRODUCER = '''
        class N {
            @Requires({ s != null })
            static int len(String s) { s.length() }
        }
    '''.stripIndent()

    /** A producer whose precondition is collection size — exercises the cross-boundary size oracle. */
    static final String SIZE_PRODUCER = '''
        class L {
            @Requires({ xs.size() > 0 })
            static int first(List xs) { 0 }
        }
    '''.stripIndent()

    static final List<Map> CASES = [

        // ---------- Phase 1: array bounds ----------
        [group: 'P1 bounds', name: 'unguarded index refuted', expect: 'IndexOutOfBoundsException',
         src: tc('class C { static int g(int[] a, int i) { a[i] } }')],
        [group: 'P1 bounds', name: 'guarded index verified', ok: true,
         src: tc('class C { static int g(int[] a, int i) { if (i >= 0 && i < a.length) return a[i]; return -1 } }')],

        // ---------- Phase 1: division ----------
        [group: 'P1 division', name: 'unguarded modulo refuted', expect: 'ArithmeticException: Division by zero',
         src: tc('class C { static int d(int x, int y) { x % y } }')],
        [group: 'P1 division', name: 'guarded modulo verified', ok: true,
         src: tc('class C { static int d(int x, int y) { if (y != 0) return x % y; return 0 } }')],

        // ---------- Phase 1: null dereference ----------
        [group: 'P1 null', name: 'unguarded deref refuted', expect: 'NullPointerException: Cannot invoke method length()',
         src: tc('class C { static int n(String s) { s.length() } }')],
        [group: 'P1 null', name: 'guarded deref verified', ok: true,
         src: tc('class C { static int n(String s) { if (s != null) return s.length(); return 0 } }')],
        [group: 'P1 null', name: '@Requires non-null verifies deref', ok: true,
         src: tc('class C { @Requires({ s != null }) static int n(String s) { s.length() } }')],

        // ---------- Phase 4: .length / .size() in contracts ----------
        [group: 'P4 size', name: '@Requires bound verifies index', ok: true,
         src: tc('class C { @Requires({ i >= 0 && i < a.length }) static int g(int[] a, int i) { a[i] } }')],

        // ---------- Phase 4: isEmpty() ----------
        [group: 'P4 isEmpty', name: 'isEmpty === size()==0', ok: true,
         src: tc('class C { @Requires({ xs.size() == 0 }) @Ensures({ xs.isEmpty() }) static int f(List xs) { 0 } }')],

        // ---------- Phase 4: equals() ----------
        [group: 'P4 equals', name: 'equals() === ==', ok: true,
         src: tc('class C { @Requires({ x.equals(0) }) @Ensures({ result == 0 }) static int f(int x) { x } }')],
        [group: 'P4 equals', name: 'missing assumption refuted', expect: 'Cannot prove postcondition',
         src: tc('class C { @Ensures({ result == 0 }) static int f(int x) { x } }')],

        // ---------- Phase 4: contains() (uninterpreted predicate) ----------
        [group: 'P4 contains', name: 'contains assumed entails contains', ok: true,
         src: tc('class C { @Requires({ xs.contains(y) }) @Ensures({ xs.contains(y) }) static int f(List xs, int y) { 0 } }')],
        [group: 'P4 contains', name: 'contains unproven refuted', expect: 'Cannot prove postcondition',
         src: tc('class C { @Ensures({ xs.contains(y) }) static int f(List xs, int y) { 0 } }')],

        // ---------- Phase 4: cross-boundary oracle binding (nullity + size) ----------
        // A guard in the caller establishes non-null, which the formal↔actual
        // nullity oracle carries across to the callee's @Requires({ s != null }).
        [group: 'P4 cross-boundary', name: 'guard proves callee non-null', ok: true,
         src: HDR + NULLITY_PRODUCER + tc('class C { static int go(String t) { if (t != null) return N.len(t); return 0 } }')],
        // The caller's own @Requires (now assumed at call sites) establishes it.
        [group: 'P4 cross-boundary', name: 'enclosing @Requires proves callee non-null', ok: true,
         src: HDR + NULLITY_PRODUCER + tc('class C { @Requires({ t != null }) static int go(String t) { N.len(t) } }')],
        // No guard, no enclosing contract: the argument may be null → refuted.
        [group: 'P4 cross-boundary', name: 'possibly-null arg refuted', expect: 'Cannot prove precondition',
         src: HDR + NULLITY_PRODUCER + tc('class C { static int go(String t) { N.len(t) } }')],
        // Size oracle carried across via the caller's own @Requires.
        [group: 'P4 cross-boundary', name: 'enclosing @Requires proves callee size', ok: true,
         src: HDR + SIZE_PRODUCER + tc('class C { @Requires({ ys.size() > 0 }) static int go(List ys) { L.first(ys) } }')],
        // No size knowledge in the caller: the list may be empty → refuted.
        [group: 'P4 cross-boundary', name: 'unconstrained size refuted', expect: 'Cannot prove precondition',
         src: HDR + SIZE_PRODUCER + tc('class C { static int go(List ys) { L.first(ys) } }')],

        // ---------- Phase 5a: value-flow (safety implied by an assignment) ----------
        // j == 3 is threaded, so 0 <= 3 < a.length follows from a.length > 5.
        [group: 'P5a value-flow', name: 'assignment-implied index verified', ok: true,
         src: tc('class C { @Requires({ a.length > 5 }) static int f(int[] a) { int j = 3; return a[j] } }')],
        // Same body without the precondition: a may be empty → refuted.
        [group: 'P5a value-flow', name: 'unconstrained assignment index refuted', expect: 'IndexOutOfBoundsException',
         src: tc('class C { static int f(int[] a) { int j = 3; return a[j] } }')],
        // Aliased counter: j == i, guard bounds i, precondition bounds a — needs value-flow + guard together.
        [group: 'P5a value-flow', name: 'aliased index under guard verified', ok: true,
         src: tc('class C { @Requires({ a.length > 10 }) static int f(int[] a, int i) { int j = i; if (i >= 0 && i < 5) return a[j]; return 0 } }')],
        // Modulo by an assigned value known non-zero.
        [group: 'P5a value-flow', name: 'assignment-implied divisor verified', ok: true,
         src: tc('class C { static int f(int x) { int d = 2; x % d } }')],

        // ---------- Phase 5b: loop-fused bounds (obligation under the invariant) ----------
        // a[i] inside the loop: i < n (guard) and n <= a.length (req) ⇒ i < a.size.
        [group: 'P5b loop-fused', name: 'in-loop index verified', ok: true,
         src: tc('''class C {
                       @Requires({ 0 <= n && n <= a.length })
                       static int sum(int[] a, int n) {
                           int s = 0
                           int i = 0
                           @Invariant({ 0 <= i && i <= n })
                           while (i < n) { s = s + a[i]; i = i + 1 }
                           return s
                       }
                   }''')],
        // Same loop without n <= a.length: the array may be shorter than n → refuted.
        [group: 'P5b loop-fused', name: 'in-loop index unbounded refuted', expect: 'IndexOutOfBoundsException',
         src: tc('''class C {
                       @Requires({ 0 <= n })
                       static int sum(int[] a, int n) {
                           int s = 0
                           int i = 0
                           @Invariant({ 0 <= i && i <= n })
                           while (i < n) { s = s + a[i]; i = i + 1 }
                           return s
                       }
                   }''')],
        // a[i] AFTER the loop: invariant i <= n and ¬guard i >= n pin i == n; n < a.length ⇒ safe.
        [group: 'P5b loop-fused', name: 'post-loop index verified', ok: true,
         src: tc('''class C {
                       @Requires({ 0 <= n && n < a.length })
                       static int at(int[] a, int n) {
                           int i = 0
                           @Invariant({ 0 <= i && i <= n })
                           while (i < n) { i = i + 1 }
                           return a[i]
                       }
                   }''')],

        // ---------- Phase 6: quantifiers (bounded universal via Forall.range) ----------
        // "every element >= 0" assumed entails the element at an in-range index >= 0.
        [group: 'P6 quantifiers', name: 'forall assumed entails instance', ok: true,
         src: tc('''class C {
                       @Requires({ Forall.range(0, a.length) { a[it] >= 0 } && 0 <= k && k < a.length })
                       @Ensures({ result >= 0 })
                       static int get(int[] a, int k) { a[k] }
                   }''')],
        // Without the forall, nothing constrains the element → postcondition refuted.
        [group: 'P6 quantifiers', name: 'missing forall refuted', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                       @Requires({ 0 <= k && k < a.length })
                       @Ensures({ result >= 0 })
                       static int get(int[] a, int k) { a[k] }
                   }''')],
        // Sortedness (a[i] <= a[i+1] for all i) assumed entails adjacent elements ordered.
        [group: 'P6 quantifiers', name: 'sortedness entails adjacent order', ok: true,
         src: tc('''class C {
                       @Requires({ Forall.range(0, a.length - 1) { i -> a[i] <= a[i + 1] } && 0 <= k && k + 1 < a.length })
                       @Ensures({ result <= 0 })
                       static int diff(int[] a, int k) { a[k] - a[k + 1] }
                   }''')],
        // Without sortedness, adjacent elements need not be ordered → refuted.
        [group: 'P6 quantifiers', name: 'missing sortedness refuted', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                       @Requires({ 0 <= k && k + 1 < a.length })
                       @Ensures({ result <= 0 })
                       static int diff(int[] a, int k) { a[k] - a[k + 1] }
                   }''')],

        // ---------- Phase 9: native GDK quantifier idioms (same universal, no Forall helper) ----------
        // (lo..<hi).every — a bounded IntRange + every, the form a Groovy dev would actually write.
        [group: 'P9 native quantifiers', name: 'range.every (exclusive) entails instance', ok: true,
         src: tc('''class C {
                       @Requires({ (0..<a.length).every { a[it] >= 0 } && 0 <= k && k < a.length })
                       @Ensures({ result >= 0 })
                       static int get(int[] a, int k) { a[k] }
                   }''')],
        // xs.indices.every — the array's own index range.
        [group: 'P9 native quantifiers', name: 'indices.every entails instance', ok: true,
         src: tc('''class C {
                       @Requires({ a.indices.every { a[it] >= 0 } && 0 <= k && k < a.length })
                       @Ensures({ result >= 0 })
                       static int get(int[] a, int k) { a[k] }
                   }''')],
        // xs.every { it … } — element-wise: `it` is the element a[i], not the index.
        [group: 'P9 native quantifiers', name: 'collection.every (element-wise) entails instance', ok: true,
         src: tc('''class C {
                       @Requires({ a.every { it >= 0 } && 0 <= k && k < a.length })
                       @Ensures({ result >= 0 })
                       static int get(int[] a, int k) { a[k] }
                   }''')],
        // (lo..hi).every — inclusive range normalised to the half-open [lo, hi+1).
        [group: 'P9 native quantifiers', name: 'range.every (inclusive) covers last index', ok: true,
         src: tc('''class C {
                       @Requires({ (0..a.length - 1).every { a[it] >= 0 } && 0 <= k && k < a.length })
                       @Ensures({ result >= 0 })
                       static int get(int[] a, int k) { a[k] }
                   }''')],
        // The element idiom is a faithful universal, not vacuous: >= 0 does not give > 0 → refuted.
        [group: 'P9 native quantifiers', name: 'element-wise idiom is not vacuous', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                       @Requires({ a.every { it >= 0 } && 0 <= k && k < a.length })
                       @Ensures({ result > 0 })
                       static int get(int[] a, int k) { a[k] }
                   }''')],
        // The native idiom works in @Invariant too — no explicit `Forall.range(...)` helper call and no
        // typed index param: the same zero-fill proof written plainly with `(0..<i).every { ... }`.
        [group: 'P9 native quantifiers', name: 'range.every in @Invariant (zero-fill)', ok: true,
         src: tc('''class C {
                       @Requires({ 0 <= n && n <= a.length })
                       @Ensures({ (0..<n).every { a[it] == 0 } })
                       static int zero(int[] a, int n) {
                           int i = 0
                           @Invariant({ 0 <= i && i <= n && (0..<i).every { a[it] == 0 } })
                           @Decreases({ n - i })
                           while (i < n) { a[i] = 0; i = i + 1 }
                           return 0
                       }
                   }''')],

        // ---------- Phase 9: existential quantifier (`any`) + precise membership ----------
        // An assumed `any` (∃) carries across to the same claim (a positive ∃ goal from a ∃ premise).
        [group: 'P9 any', name: 'element any assumed entails', ok: true,
         src: tc('class C { @Requires({ a.any { it < 0 } }) @Ensures({ a.any { it < 0 } }) static int f(int[] a) { 0 } }')],
        // Existential GOAL with a witness: the element at a valid index is in the array.
        [group: 'P9 any', name: 'any proves membership at a valid index', ok: true,
         src: tc('class C { @Requires({ 0 <= k && k < a.length }) @Ensures({ a.any { it == a[k] } }) static int f(int[] a, int k) { 0 } }')],
        // Range form: `(0..<n).any { … }` is the same existential over indices.
        [group: 'P9 any', name: 'range.any entails element any', ok: true,
         src: tc('class C { @Requires({ (0..<a.length).any { a[it] < 0 } }) @Ensures({ a.any { it < 0 } }) static int f(int[] a) { 0 } }')],
        // Not vacuous: with nothing assumed, an existential claim cannot be proved.
        [group: 'P9 any', name: 'unproven any refuted', expect: 'Cannot prove postcondition',
         src: tc('class C { @Ensures({ a.any { it < 0 } }) static int f(int[] a) { 0 } }')],
        // `contains` is now precise (relates to actual contents): a[k] is contained for a valid k —
        // the old opaque uninterpreted predicate could not prove this.
        [group: 'P9 any', name: 'precise contains at a valid index', ok: true,
         src: tc('class C { @Requires({ 0 <= k && k < a.length }) @Ensures({ a.contains(a[k]) }) static int f(int[] a, int k) { 0 } }')],

        // ---------- Phase 10 (Layer A): instance methods with parameter-only contracts ----------
        // No `static` — the VC machinery is instance-agnostic, so this verifies like a static method.
        [group: 'P10 instance', name: 'instance method, param contract', ok: true,
         src: tc('''class C {
                       @Requires({ x >= 0 })
                       @Ensures({ result >= x })
                       int inc(int x) { x + 1 }
                   }''')],
        // Layer B — instance field READ: a getter relates result to field state.
        [group: 'P10 instance', name: 'field read in getter', ok: true,
         src: tc('''class C {
                       int lo, hi
                       @Requires({ lo <= hi })
                       @Ensures({ result >= lo && result <= hi })
                       int clamp(int x) { x < lo ? lo : (x > hi ? hi : x) }
                   }''')],
        // Layer B — instance field WRITE (SSA): the mutator reads the entry field, writes the exit field.
        [group: 'P10 instance', name: 'field write mutator verified', ok: true,
         src: tc('''class C {
                       int count, max
                       @Requires({ count < max })
                       @Ensures({ count <= max })
                       void inc() { count = count + 1 }
                   }''')],
        // Soundness: a mutator that can break the bound is refuted (no @Requires guard).
        [group: 'P10 instance', name: 'field write mutator refuted', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                       int count, max
                       @Ensures({ count <= max })
                       void inc() { count = count + 1 }
                   }''')],
        // `this.x` spelling reads/writes the same field state as the bare name.
        [group: 'P10 instance', name: 'this.field spelling', ok: true,
         src: tc('''class C {
                       int count, max
                       @Requires({ this.count < this.max })
                       @Ensures({ this.count <= this.max })
                       void inc() { this.count = this.count + 1 }
                   }''')],

        // ---------- Phase 11: old(...) pre-state — relate the result to the method's entry state ----------
        // Scalar field delta: the exit count is the entry count plus one.
        [group: 'P11 old', name: 'field delta vs old', ok: true,
         src: tc('''class C {
                       int count
                       @Ensures({ count == old.count + 1 })
                       void inc() { count = count + 1 }
                   }''')],
        // Soundness: a body that doesn't match the old-delta is refuted.
        [group: 'P11 old', name: 'wrong old delta refuted', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                       int count
                       @Ensures({ count == old.count + 1 })
                       void inc() { count = count + 2 }
                   }''')],
        // Array element FRAME (the @Modifies enabler): a setter changes only a[j]; every other
        // element equals its old value. `old.a[it]` is the entry snapshot of the array's contents.
        [group: 'P11 old', name: 'array element frame via old', ok: true,
         src: tc('''class C {
                       int[] a
                       @Requires({ 0 <= j && j < a.length })
                       @Ensures({ (0..<a.length).every { it == j || a[it] == old.a[it] } })
                       void set(int j, int v) { a[j] = v }
                   }''')],

        // ---------- Phase 12: permutation — multiset preserved via per-store count law ----------
        // Building block: a swap preserves a.count(v) for an arbitrary value v (the ghost param) →
        // the array stays a permutation. The two stores' count updates cancel.
        [group: 'P12 perm', name: 'swap preserves count', ok: true,
         src: tc('''class C {
                       int[] a
                       @Requires({ 0 <= i && i < a.length && 0 <= j && j < a.length })
                       @Ensures({ a.count(v) == old.a.count(v) })
                       void swap(int i, int j, int v) { int t = a[i]; a[i] = a[j]; a[j] = t }
                   }''')],
        // Soundness: a plain copy (not a swap) drops an element → some count changes → refuted.
        [group: 'P12 perm', name: 'copy is not a permutation', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                       int[] a
                       @Requires({ 0 <= i && i < a.length && 0 <= j && j < a.length })
                       @Ensures({ a.count(v) == old.a.count(v) })
                       void copy(int i, int j, int v) { a[i] = a[j] }
                   }''')],
        // ---------- Phase 14: the verified sort — sorted AND a permutation ----------
        // insert threads a ghost upper bound `hi` (the recursion passes the pivot a[m] as the new,
        // tight bound), a ghost count value `v` (permutation), and frames the suffix it doesn't touch.
        // Under sound call-site checking (Phase 24) the recursive precondition `insert(m-1, a[m], v)` needs
        // the *transitive* bound `a[it] <= a[m-1]` for all it<m-1 (the new pivot bound), which Z3 cannot get
        // from *adjacent* sortedness by e-matching (it times out). A monotone-bound LEMMA (`maxBound`, proved
        // by induction) supplies it: called before the swap, its @Ensures threads through the swap (Phase 24)
        // to the recursive call — and the sort is fully verified again.
        [group: 'P14 sort', name: 'insertion sort: sorted AND permutation', ok: true,
         src: tc('''class C {
                       int[] a
                       // lemma: every element of an adjacent-sorted prefix [0,k] is <= a[k], by induction on k.
                       @Requires({ 0 <= k && k < a.length && (0..<k).every { a[it] <= a[it + 1] } })
                       @Ensures({ (0..<k + 1).every { a[it] <= a[k] } })
                       @Decreases({ k })
                       void maxBound(int k) {
                           if (k > 0) maxBound(k - 1)
                       }
                       @Requires({ 0 <= m && m < a.length &&
                                   (0..<m - 1).every { a[it] <= a[it + 1] } &&
                                   (0..<m + 1).every { a[it] <= hi } })
                       @Modifies({ this.a })
                       @Ensures({ (0..<m).every { a[it] <= a[it + 1] } &&
                                  (0..<m + 1).every { a[it] <= hi } &&
                                  (m + 1..<a.length).every { a[it] == old.a[it] } &&
                                  a.count(v) == old.a.count(v) })
                       @Decreases({ m })
                       void insert(int m, int hi, int v) {
                           if (m > 0 && a[m] < a[m - 1]) {
                               maxBound(m - 1)
                               int t = a[m]; a[m] = a[m - 1]; a[m - 1] = t
                               insert(m - 1, a[m], v)
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
                   }''')],
        // Soundness anchor: a sort that does nothing cannot claim its result is sorted → refuted.
        [group: 'P14 sort', name: 'no-op sort cannot claim sorted', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                       int[] a
                       @Requires({ 0 <= n && n <= a.length })
                       @Modifies({ this.a })
                       @Ensures({ (0..<n - 1).every { a[it] <= a[it + 1] } })
                       void sort(int n) { }
                   }''')],

        // ---------- Phase 13 (frame-check): a method writes only what its @Modifies declares ----------
        // Honest: inc declares it modifies count and writes only count → frame-check passes.
        [group: 'P13 frame', name: 'honest modifies verified', ok: true,
         src: tc('''class C {
                       int count, other
                       @Modifies({ this.count })
                       void inc() { count = count + 1 }
                   }''')],
        // Array modifies: a setter declares it modifies a, and writes only a.
        [group: 'P13 frame', name: 'array modifies verified', ok: true,
         src: tc('''class C {
                       int[] a
                       @Requires({ 0 <= j && j < a.length })
                       @Modifies({ this.a })
                       void set(int j, int v) { a[j] = v }
                   }''')],
        // Violation: writes an undeclared field → loud frame error.
        [group: 'P13 frame', name: 'undeclared write refuted', expect: 'not in its @Modifies',
         src: tc('''class C {
                       int count, other
                       @Modifies({ this.count })
                       void bad() { count = count + 1; other = 7 }
                   }''')],
        // @Modifies({ [] }) means pure: any field write violates it.
        [group: 'P13 frame', name: 'pure method that writes refuted', expect: 'not in its @Modifies',
         src: tc('''class C {
                       int count
                       @Modifies({ [] })
                       void touch() { count = 1 }
                   }''')],
        // Caller-side framing: clobber() may change a (declared, @Ensures says nothing), so the caller
        // can NO LONGER assume a[0] is unchanged across the call → refuted. (Pre-framing this passed
        // unsoundly — the call left `a` untouched.)
        [group: 'P13 frame', name: 'callee may clobber shared array', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                       int[] a
                       @Requires({ a.length > 0 })
                       @Modifies({ this.a })
                       void clobber() { a[0] = 999 }
                       @Requires({ a.length > 0 && a[0] == 5 })
                       @Modifies({ this.a })
                       @Ensures({ a[0] == 5 })
                       void caller() { clobber() }
                   }''')],

        // Composition (now sound, via @Modifies caller-side framing): a recursive insertion sort
        // preserves the multiset — `a.count(v) == old.a.count(v)` for arbitrary v — across the swaps
        // *and* the recursive calls (each call havocs a, then reframes count from the callee's @Ensures
        // with `old.a` bound to the array at the call). Permutation only; sound sortedness-under-havoc
        // additionally needs a prefix bound (see ROADMAP Phase 13).
        [group: 'P12 perm', name: 'recursive insertion sort permutes', ok: true,
         src: tc('''class C {
                       int[] a
                       @Requires({ 0 <= i && i < a.length })
                       @Modifies({ this.a })
                       @Ensures({ a.count(v) == old.a.count(v) })
                       @Decreases({ i })
                       void insert(int i, int v) {
                           if (i > 0 && a[i] < a[i - 1]) {
                               int t = a[i]; a[i] = a[i - 1]; a[i - 1] = t
                               insert(i - 1, v)
                           }
                       }
                       @Requires({ 0 <= n && n <= a.length })
                       @Modifies({ this.a })
                       @Ensures({ a.count(v) == old.a.count(v) })
                       @Decreases({ n })
                       void sort(int n, int v) {
                           if (n > 1) { sort(n - 1, v); insert(n - 1, v) }
                       }
                   }''')],
        // Soundness (no longer vacuous, now that `old` is bound at the call): an overwriting insert
        // drops an element → permutation refuted.
        [group: 'P12 perm', name: 'overwrite insert breaks permutation', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                       int[] a
                       @Requires({ 0 <= i && i < a.length })
                       @Modifies({ this.a })
                       @Ensures({ a.count(v) == old.a.count(v) })
                       @Decreases({ i })
                       void insert(int i, int v) {
                           if (i > 0 && a[i] < a[i - 1]) {
                               a[i - 1] = a[i]
                               insert(i - 1, v)
                           }
                       }
                   }''')],

        // ---------- Phase 9: diagnostics echo the accessor the developer wrote (not the internal a.size) ----------
        // No size accessor written (just a[i]) → the universal Groovy idiom .size(), valid for arrays too.
        [group: 'P9 diagnostics', name: 'implicit access defaults to .size()', expect: 'a.size()',
         src: tc('class C { static int g(int[] a, int i) { a[i] } }')],
        // The developer wrote a.length, so the obligation and counterexample echo .length.
        [group: 'P9 diagnostics', name: 'written .length is echoed', expect: 'a.length',
         src: tc('''class C {
                       @Requires({ i < a.length })
                       static int g(int[] a, int i) { a[i] }
                   }''')],
        // A collection's size, written as xs.size(), is echoed verbatim.
        [group: 'P9 diagnostics', name: 'written .size() is echoed', expect: 'xs.size()',
         src: tc('''class C {
                       @Requires({ xs.size() > 5 })
                       @Ensures({ result < 0 })
                       static int f(List xs) { xs.size() }
                   }''')],

        // ---------- Phase 9: counterexample reconstructed as a runnable failing call ----------
        // Array out-of-bounds → an array rebuilt at the modelled size + the offending index.
        [group: 'P9 repro', name: 'bounds failure reconstructs a call', expect: 'fails on: g(new int[3]',
         src: tc('''class C {
                       @Requires({ a.length == 3 })
                       static int g(int[] a, int i) { a[i] }
                   }''')],
        // Division by zero → the divisor argument is the zero from the model.
        [group: 'P9 repro', name: 'division failure reconstructs a call', expect: 'fails on: d(',
         src: tc('class C { static int d(int x, int y) { x % y } }')],
        // Null dereference → the receiver argument is rendered as null.
        [group: 'P9 repro', name: 'null deref reconstructs a null argument', expect: 'fails on: n(null)',
         src: tc('class C { static int n(String s) { s.length() } }')],
        // Slice 2: a contents-dependent failure pins the array elements as a literal, not new int[n].
        [group: 'P9 repro', name: 'contents failure pins array elements', expect: 'fails on: f([',
         src: tc('''class C {
                       @Requires({ a.length == 2 })
                       @Ensures({ a[0] == a[1] })
                       static int f(int[] a) { 0 }
                   }''')],

        // ---------- Phase 7: recursive insertion sort (sortedness, end-to-end) ----------
        // insert places a[i] into the sorted prefix; sort composes it under induction. The driver
        // relies on the @Ensures of the `sort(a, n-1)` call immediately before `insert(a, n-1)`.
        [group: 'P7 recursive sort', name: 'recursive insertion sort (sortedness)', ok: true,
         src: tc('''class C {
                       @Requires({ 0 <= i && i < a.length && (0..<i - 1).every { a[it] <= a[it + 1] } })
                       @Ensures({ (0..<i).every { a[it] <= a[it + 1] } })
                       @Decreases({ i })
                       static void insert(int[] a, int i) {
                           if (i > 0 && a[i] < a[i - 1]) {
                               int t = a[i]; a[i] = a[i - 1]; a[i - 1] = t
                               insert(a, i - 1)
                           }
                       }
                       @Requires({ 0 <= n && n <= a.length })
                       @Ensures({ (0..<n - 1).every { a[it] <= a[it + 1] } })
                       @Decreases({ n })
                       static void sort(int[] a, int n) {
                           if (n > 1) {
                               sort(a, n - 1)
                               insert(a, n - 1)
                           }
                       }
                   }''')],
        // Soundness A: an intervening store invalidates the prefix → insert's precondition must NOT
        // be assumable from the earlier sort (the immediately-preceding statement is the store).
        [group: 'P7 recursive sort', name: 'intervening store breaks precondition', expect: 'Cannot prove precondition',
         src: tc('''class C {
                       @Requires({ 0 <= i && i < a.length && (0..<i - 1).every { a[it] <= a[it + 1] } })
                       @Ensures({ (0..<i).every { a[it] <= a[it + 1] } })
                       @Decreases({ i })
                       static void insert(int[] a, int i) {
                           if (i > 0 && a[i] < a[i - 1]) { int t = a[i]; a[i] = a[i - 1]; a[i - 1] = t; insert(a, i - 1) }
                       }
                       @Requires({ 2 <= n && n <= a.length })
                       @Ensures({ (0..<n - 1).every { a[it] <= a[it + 1] } })
                       @Decreases({ n })
                       static void sort(int[] a, int n) {
                           sort(a, n - 1)
                           a[0] = 999
                           insert(a, n - 1)
                       }
                   }''')],
        // Soundness B: forget to insert → the suffix isn't placed → postcondition must refute.
        [group: 'P7 recursive sort', name: 'missing insert refutes', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                       @Requires({ 0 <= n && n <= a.length })
                       @Ensures({ (0..<n - 1).every { a[it] <= a[it + 1] } })
                       @Decreases({ n })
                       static void sort(int[] a, int n) {
                           if (n > 1) { sort(a, n - 1) }
                       }
                   }''')],

        // ---------- Phase 5a: short-circuit guard path conditions (&& / ||) ----------
        // The `&&` left operands (`i > 0 && i <= a.length`) protect `a[i-1]` in the right operand.
        [group: 'P5a short-circuit', name: 'and-guard protects right operand', ok: true,
         src: tc('class C { static int g(int[] a, int i) { (i > 0 && i <= a.length && a[i - 1] > 0) ? 1 : 0 } }')],
        // `||`: entering the right operand means the left disjuncts are false → `0 < i <= a.length`.
        [group: 'P5a short-circuit', name: 'or-guard protects right operand', ok: true,
         src: tc('class C { static int g(int[] a, int i) { (i <= 0 || i > a.length || a[i - 1] > 0) ? 1 : 0 } }')],
        // Still sound: with the guard removed, the access is genuinely unprotected → refuted.
        [group: 'P5a short-circuit', name: 'unguarded access still refuted', expect: 'IndexOutOfBoundsException',
         src: tc('class C { static int g(int[] a, int i) { (a[i - 1] > 0) ? 1 : 0 } }')],
        // The natural (single-&&) recursive insert now verifies — no nested-if workaround needed.
        [group: 'P5a short-circuit', name: 'natural insert guard verifies', ok: true,
         src: tc('''class C {
                       @Requires({ 0 <= i && i < a.length && (0..<i - 1).every { a[it] <= a[it + 1] } })
                       @Ensures({ (0..<i).every { a[it] <= a[it + 1] } })
                       @Decreases({ i })
                       static void insert(int[] a, int i) {
                           if (i > 0 && a[i] < a[i - 1]) {
                               int t = a[i]; a[i] = a[i - 1]; a[i - 1] = t
                               insert(a, i - 1)
                           }
                       }
                   }''')],

        // ---------- Phase 6: array update (store) ----------
        // After a[k] = v, reading a[k] yields v — postcondition about the produced array.
        [group: 'P6 store', name: 'post-store element verified', ok: true,
         src: tc('''class C {
                       @Requires({ 0 <= k && k < a.length })
                       @Ensures({ a[k] == v })
                       static int set(int[] a, int k, int v) { a[k] = v; a[k] }
                   }''')],
        // Storing the wrong value violates the postcondition → refuted.
        [group: 'P6 store', name: 'wrong store value refuted', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                       @Requires({ 0 <= k && k < a.length })
                       @Ensures({ a[k] == v })
                       static int set(int[] a, int k, int v) { a[k] = v + 1; a[k] }
                   }''')],

        // ---------- Phase 7 (slice 1): inter-procedural @Ensures (result-binding) ----------
        // h can't see inside absv, but assumes absv's @Ensures (result >= 0) for z.
        [group: 'P7 inter-proc', name: 'callee @Ensures used at call site', ok: true,
         src: tc('''class C {
                       @Ensures({ result >= 0 })
                       static int absv(int x) { if (x >= 0) return x; return -x }

                       @Ensures({ result >= 0 })
                       static int h(int w) { int z = absv(w); z }
                   }''')],
        // The callee's @Requires is discharged at the call, its @Ensures then assumed.
        [group: 'P7 inter-proc', name: 'callee @Requires + @Ensures threaded', ok: true,
         src: tc('''class C {
                       @Requires({ x >= 0 })
                       @Ensures({ result >= x })
                       static int bump(int x) { x + 5 }

                       @Requires({ y >= 0 })
                       @Ensures({ result >= y })
                       static int g(int y) { int z = bump(y); z }
                   }''')],
        // Modular reasoning: only the contract (result >= x), not the body (x + 5),
        // is used — so the stronger bound result >= y + 1 cannot be proven.
        [group: 'P7 inter-proc', name: 'contract not body refuted', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                       @Requires({ x >= 0 })
                       @Ensures({ result >= x })
                       static int bump(int x) { x + 5 }

                       @Requires({ y >= 0 })
                       @Ensures({ result >= y + 1 })
                       static int g(int y) { int z = bump(y); z }
                   }''')],

        // ---------- Phase 6: in-loop store (array update threaded through a loop) ----------
        // Fill a[0..n) with 0; the content invariant is preserved across the store and
        // proves the postcondition that the whole range is zeroed.
        [group: 'P6 in-loop store', name: 'zero-fill verified', ok: true,
         src: tc('''class C {
                       @Requires({ 0 <= n && n <= a.length })
                       @Ensures({ Forall.range(0, n) { i -> a[i] == 0 } })
                       static int zero(int[] a, int n) {
                           int i = 0
                           @Invariant({ 0 <= i && i <= n && Forall.range(0, i, { int j -> a[j] == 0 }) })
                           @Decreases({ n - i })
                           while (i < n) { a[i] = 0; i = i + 1 }
                           return 0
                       }
                   }''')],
        // The body stores 1 but the invariant claims the range is 0 → preservation refuted.
        [group: 'P6 in-loop store', name: 'store breaks invariant refuted', expect: 'invariant is preserved',
         src: tc('''class C {
                       @Requires({ 0 <= n && n <= a.length })
                       static int fill(int[] a, int n) {
                           int i = 0
                           @Invariant({ 0 <= i && i <= n && Forall.range(0, i, { int j -> a[j] == 0 }) })
                           @Decreases({ n - i })
                           while (i < n) { a[i] = 1; i = i + 1 }
                           return 0
                       }
                   }''')],

        // ---------- Phase 7 (induction): recursion via @Decreases + self-IH ----------
        // The canonical inductive proof: assume sumUp's @Ensures at the recursive call (IH),
        // prove it for this call; @Decreases({ n }) discharges termination (n - 1 < n, >= 0).
        [group: 'P7 induction', name: 'recursive sumUp verified', ok: true,
         src: tc('''class C {
                       @Requires({ n >= 0 })
                       @Ensures({ result >= n })
                       @Decreases({ n })
                       static int sumUp(int n) {
                           if (n == 0) return 0
                           int r = sumUp(n - 1)
                           return r + n
                       }
                   }''')],
        // Recurses on the same n: the measure does not decrease → termination refuted.
        [group: 'P7 induction', name: 'non-decreasing recursion refuted', expect: 'recursion measure',
         src: tc('''class C {
                       @Requires({ n >= 0 })
                       @Ensures({ result >= n })
                       @Decreases({ n })
                       static int bad(int n) {
                           if (n == 0) return 0
                           int r = bad(n)
                           return r + n
                       }
                   }''')],
        // The inductive hypothesis isn't strong enough for a strict postcondition (fails at n == 0).
        [group: 'P7 induction', name: 'too-strong postcondition refuted', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                       @Requires({ n >= 0 })
                       @Ensures({ result > n })
                       @Decreases({ n })
                       static int sumUp(int n) {
                           if (n == 0) return 0
                           int r = sumUp(n - 1)
                           return r + n
                       }
                   }''')],
        // Without @Decreases the self-IH is disabled — the recursive result is opaque → skipped.
        [group: 'P7 induction', name: 'recursion without measure skipped', expect: 'Skipped verification of postcondition',
         src: tc('''class C {
                       @Requires({ n >= 0 })
                       @Ensures({ result >= n })
                       static int sumUp(int n) {
                           if (n == 0) return 0
                           int r = sumUp(n - 1)
                           return r + n
                       }
                   }''')],

        // ---------- Phase 7 (standalone lemmas): void methods + self-IH + standalone calls ----------
        // Machinery: a void, self-recursive method verifies (void paths + standalone self-call IH + termination).
        [group: 'P7 lemmas', name: 'void recursive method verified', ok: true,
         src: tc('''class C {
                       @Requires({ n >= 0 })
                       @Ensures({ n >= 0 })
                       @Decreases({ n })
                       static void countDown(int n) {
                           if (n > 0) countDown(n - 1)
                       }
                   }''')],
        // Load-bearing lemma: sortedness transitivity, proved by induction on j - i.
        [group: 'P7 lemmas', name: 'sortedness transitivity lemma verified', ok: true,
         src: tc('''class C {
                       @Requires({ Forall.range(0, a.length - 1, { k -> a[k] <= a[k + 1] }) && 0 <= i && i <= j && j < a.length })
                       @Ensures({ a[i] <= a[j] })
                       @Decreases({ j - i })
                       static void leSorted(int[] a, int i, int j) {
                           if (i < j) leSorted(a, i + 1, j)
                       }
                   }''')],
        // Using the lemma: a standalone call injects a[p] <= a[q], proving the postcondition.
        [group: 'P7 lemmas', name: 'standalone lemma call used', ok: true,
         src: tc('''class C {
                       @Requires({ Forall.range(0, a.length - 1, { k -> a[k] <= a[k + 1] }) && 0 <= i && i <= j && j < a.length })
                       @Ensures({ a[i] <= a[j] })
                       @Decreases({ j - i })
                       static void leSorted(int[] a, int i, int j) {
                           if (i < j) leSorted(a, i + 1, j)
                       }
                       @Requires({ Forall.range(0, a.length - 1, { k -> a[k] <= a[k + 1] }) && 0 <= p && p <= q && q < a.length })
                       @Ensures({ result <= 0 })
                       static int diff(int[] a, int p, int q) {
                           leSorted(a, p, q)
                           return a[p] - a[q]
                       }
                   }''')],
        // A void lemma whose measure does not decrease → termination refuted.
        [group: 'P7 lemmas', name: 'void lemma non-decreasing refuted', expect: 'recursion measure',
         src: tc('''class C {
                       @Decreases({ j - i })
                       static void bad(int[] a, int i, int j) {
                           if (i < j) bad(a, i, j)
                       }
                   }''')],

        // ---------- Phase 8a (normalise-then-SMT): closed-constant folding ----------
        // (2 + 2) * (2 + 2): both operands are compound (non-literal), so the NIA opt-out would
        // skip it; constant folding reduces it to 16 and the postcondition verifies.
        [group: 'P8a folding', name: 'closed nonlinear product verified', ok: true,
         src: tc('class C { @Ensures({ result == (2 + 2) * (2 + 2) }) static int f() { 16 } }')],
        // Same fold, wrong answer → refuted (folding is correct, not vacuous).
        [group: 'P8a folding', name: 'closed product wrong value refuted', expect: 'Cannot prove postcondition',
         src: tc('class C { @Ensures({ result == (2 + 2) * (2 + 2) }) static int f() { 15 } }')],
        // Folded constant used as an array index: a[(1 + 1) * 2] needs index 4 in bounds.
        [group: 'P8a folding', name: 'folded index in bounds verified', ok: true,
         src: tc('class C { @Requires({ a.length > 4 }) static int g(int[] a) { a[(1 + 1) * 2] } }')],

        // ---------- Phase 8a (pure-function evaluation): closed calls computed to literals ----------
        // A recursive pure function applied to a constant in a contract is evaluated: pow2(10) = 1024.
        [group: 'P8a eval', name: 'closed recursive call in contract verified', ok: true,
         src: tc('''class C {
                       static int pow2(int n) { n == 0 ? 1 : 2 * pow2(n - 1) }
                       @Ensures({ result == pow2(10) })
                       static int f() { 1024 }
                   }''')],
        // Pure function call in the body (implicit return), evaluated to 120.
        [group: 'P8a eval', name: 'closed call in body verified', ok: true,
         src: tc('''class C {
                       static int factorial(int n) { n <= 1 ? 1 : n * factorial(n - 1) }
                       @Ensures({ result == 120 })
                       static int f() { factorial(5) }
                   }''')],
        // Evaluation is correct, not vacuous: a wrong expected value is refuted.
        [group: 'P8a eval', name: 'wrong evaluated value refuted', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                       static int pow2(int n) { n == 0 ? 1 : 2 * pow2(n - 1) }
                       @Ensures({ result == pow2(10) })
                       static int f() { 1000 }
                   }''')],

        // ---------- Phase 8a (bounded symbolic unfolding): inline a pure fn against symbolic args ----------
        // A non-recursive helper applied to a symbolic argument is inlined to its body: twice(x) = x + x.
        [group: 'P8a unfold', name: 'non-recursive helper inlined', ok: true,
         src: tc('''class C {
                       static int twice(int n) { n + n }
                       @Ensures({ result == twice(x) })
                       static int f(int x) { x + x }
                   }''')],
        // A ternary-bodied helper unfolds to an `ite`; the @Requires path picks the branch.
        [group: 'P8a unfold', name: 'ternary helper unfolds to ite', ok: true,
         src: tc('''class C {
                       static int absV(int x) { x >= 0 ? x : -x }
                       @Requires({ x < 0 })
                       @Ensures({ result == -x })
                       static int f(int x) { absV(x) }
                   }''')],
        // A recursive helper on a path-constrained symbolic arg unfolds until the base case fires.
        [group: 'P8a unfold', name: 'recursive helper unfolds under path constraint', ok: true,
         src: tc('''class C {
                       static int pow2(int n) { n == 0 ? 1 : 2 * pow2(n - 1) }
                       @Requires({ n == 2 })
                       @Ensures({ result == 4 })
                       static int f(int n) { pow2(n) }
                   }''')],
        // Unfolding is faithful, not vacuous: a body that differs from the inlined definition is refuted.
        [group: 'P8a unfold', name: 'mismatched body refuted', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                       static int twice(int n) { n + n }
                       @Ensures({ result == twice(x) })
                       static int f(int x) { x + x + 1 }
                   }''')],

        // ---------- Regression: call-site preconditions ----------
        [group: 'regression @Requires', name: 'bad literal call refuted', expect: 'Cannot prove precondition',
         src: HDR + PRODUCER + tc('class C { static int go() { P.sq(-1) } }')],
        [group: 'regression @Requires', name: 'good literal call verified', ok: true,
         src: HDR + PRODUCER + tc('class C { static int go() { P.sq(5) } }')],

        // ---------- Regression: postconditions ----------
        [group: 'regression @Ensures', name: 'max verified', ok: true,
         src: tc('class C { @Ensures({ result >= a && result >= b }) static int max(int a, int b) { if (a > b) a else b } }')],
        [group: 'regression @Ensures', name: 'maxBuggy refuted', expect: 'Cannot prove postcondition',
         src: tc('class C { @Ensures({ result >= a && result >= b }) static int max(int a, int b) { if (a > b) b else a } }')],

        // ---------- Phase 88: do..while (body runs once before the first guard/invariant check) ----------
        // `do B while (G)` ≡ `B; while (G) B`. Establishment therefore checks the invariant AFTER the first
        // body, not at entry: the `1 <= i` clause here is FALSE at entry (i=0) but true after one `i++` —
        // so this verifies only with do-while-faithful establishment (Phase 88), and `result == n` follows
        // from the exit `i == n`. Termination on `n - i`.
        [group: 'P88 do-while', name: 'do-while countUp (body-first establishment)', ok: true,
         src: tc('''class C {
                        @Requires({ n >= 1 })
                        @Ensures({ result == n })
                        static int countUp(int n) {
                            int i = 0
                            @Invariant({ 1 <= i && i <= n })
                            @Decreases({ n - i })
                            do { i++ } while (i < n)
                            return i
                        }
                    }''')],
        // SOUNDNESS (the bug Phase 88 fixes): at n==0 the body runs once (result is 1), but `@Invariant({i==0})`
        // holds at entry and is vacuously preserved (guard never true), and exit `i==0` would prove the FALSE
        // `result==0`. Treating do-while as while verified this silently; now establishment runs the body once
        // (i=1) and the invariant fails there — correctly rejected, with do-while-aware wording.
        [group: 'P88 do-while', name: 'do-while false invariant rejected (was unsound)',
         expect: "after the do-while's first iteration",
         src: tc('''class C {
                        @Requires({ n == 0 })
                        @Ensures({ result == 0 })
                        static int f(int n) {
                            int i = 0
                            @Invariant({ i == 0 })
                            @Decreases({ n - i })
                            do { i++ } while (i < n)
                            return i
                        }
                    }''')],
        // A wrong postcondition still refutes at the use obligation (exit is i==n, not n+1).
        [group: 'P88 do-while', name: 'do-while wrong postcondition refuted',
         expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Requires({ n >= 1 })
                        @Ensures({ result == n + 1 })
                        static int countUp(int n) {
                            int i = 0
                            @Invariant({ 1 <= i && i <= n })
                            @Decreases({ n - i })
                            do { i++ } while (i < n)
                            return i
                        }
                    }''')],

        // ---------- Phase 89 (slice 1): reference identity + identity-keyed field reads ----------
        // Two same-class object params are "alias-modelled": their Int fields read through a per-(class,field)
        // heap map indexed by object identity, so `a.is(b)`/`a === b` (identity equality) makes the fields
        // provably coincide. Here `a.is(b)` ⇒ a.balance == b.balance ⇒ a.balance + b.balance == 2 * a.balance.
        [group: 'P89 ref-identity', name: 'a.is(b) ⇒ fields coincide (identity model)', ok: true,
         src: tc('''class Account { int balance }
                    @TypeChecked(extensions = 'verification.VerifyChecker')
                    class C {
                        @Requires({ a.is(b) })
                        @Ensures({ result == 2 * a.balance })
                        static int twice(Account a, Account b) { a.balance + b.balance }
                    }''')],
        // The `===` operator form, as a pure model tautology: equal identities ⇒ equal field reads.
        [group: 'P89 ref-identity', name: 'a === b ==> a.balance == b.balance', ok: true,
         src: tc('''class Account { int balance }
                    @TypeChecked(extensions = 'verification.VerifyChecker')
                    class C {
                        @Ensures({ (a === b) ==> (a.balance == b.balance) })
                        static void f(Account a, Account b) { }
                    }''')],
        // Without the identity assumption the two references may differ — so `result == 2 * a.balance`
        // is NOT provable (b.balance is unconstrained relative to a.balance). Refutes.
        [group: 'P89 ref-identity', name: 'no identity ⇒ fields need not coincide (refuted)',
         expect: 'Cannot prove postcondition',
         src: tc('''class Account { int balance }
                    @TypeChecked(extensions = 'verification.VerifyChecker')
                    class C {
                        @Ensures({ result == 2 * a.balance })
                        static int twice(Account a, Account b) { a.balance + b.balance }
                    }''')],

        // ---------- Phase 89 (slice 2): field WRITES through object references ----------
        // `a.balance = v` stores into the identity-keyed heap map, so a post-state read sees it.
        [group: 'P89 field-write', name: 'write seen through the same reference', ok: true,
         src: tc('''class Account { int balance }
                    @TypeChecked(extensions = 'verification.VerifyChecker')
                    class C {
                        @Ensures({ a.balance == 100 })
                        static void setHundred(Account a, Account b) { a.balance = 100 }
                    }''')],
        // THE HEADLINE: a write through `a` is observed through `b` *exactly when* they alias. With
        // `a.is(b)` the store at id(a) is read back at id(b) — "mutate via one handle, observe via another".
        [group: 'P89 field-write', name: 'aliased write observed through the other reference', ok: true,
         src: tc('''class Account { int balance }
                    @TypeChecked(extensions = 'verification.VerifyChecker')
                    class C {
                        @Requires({ a.is(b) })
                        @Ensures({ b.balance == 100 })
                        static void setHundred(Account a, Account b) { a.balance = 100 }
                    }''')],
        // Without the alias assumption the write to `a` need NOT be visible through `b` — refuted.
        [group: 'P89 field-write', name: 'write not observed through a non-aliased reference (refuted)',
         expect: 'Cannot prove postcondition',
         src: tc('''class Account { int balance }
                    @TypeChecked(extensions = 'verification.VerifyChecker')
                    class C {
                        @Ensures({ b.balance == 100 })
                        static void setHundred(Account a, Account b) { a.balance = 100 }
                    }''')],
        // The aliasing bug-catch: setBoth *looks* correct, but if a === b the second write wins
        // (a.balance ends at 200, not 100) — the verifier refuses it and the counterexample is a === b.
        [group: 'P89 field-write', name: 'setBoth refuted under aliasing (forgot a !== b)', expect: 'Cannot prove postcondition',
         src: tc('''class Account { int balance }
                    @TypeChecked(extensions = 'verification.VerifyChecker')
                    class C {
                        @Ensures({ a.balance == 100 && b.balance == 200 })
                        static void setBoth(Account a, Account b) { a.balance = 100; b.balance = 200 }
                    }''')],
        // The distinctness precondition `a !== b` (the identity operator) makes it verify.
        [group: 'P89 field-write', name: 'setBoth verifies with a !== b', ok: true,
         src: tc('''class Account { int balance }
                    @TypeChecked(extensions = 'verification.VerifyChecker')
                    class C {
                        @Requires({ a !== b })
                        @Ensures({ a.balance == 100 && b.balance == 200 })
                        static void setBoth(Account a, Account b) { a.balance = 100; b.balance = 200 }
                    }''')],

        // ---------- Regression: loops ----------
        [group: 'regression loop', name: 'countUp verified', ok: true,
         src: tc('''class C {
                       @Requires({ n >= 0 })
                       @Ensures({ result == n })
                       static int countUp(int n) {
                           int i = 0
                           @Invariant({ 0 <= i && i <= n })
                           @Decreases({ n - i })
                           while (i < n) { i++ }
                           return i
                       }
                   }''')],

        // ---------- Boxed types & lists (structural: the encoder is untyped) ----------
        // The encoder treats every integer type as a mathematical Int and matches arrays/lists by
        // syntactic shape (`a[i]`, `.length`/`.size()`), so `Integer`, `Integer[]`, and index-accessed
        // `List<Integer>` verify exactly like `int` / `int[]`. (Element nullability is the known gap.)
        [group: 'boxed & list', name: 'Integer scalar postcondition', ok: true,
         src: tc('''class C {
                       @Ensures({ result >= a && result >= b })
                       static Integer max(Integer a, Integer b) { a >= b ? a : b }
                   }''')],
        [group: 'boxed & list', name: 'Integer scalar postcondition refuted', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                       @Ensures({ result >= a && result >= b })
                       static Integer max(Integer a, Integer b) { a >= b ? b : a }
                   }''')],
        [group: 'boxed & list', name: 'Integer[] sorted-diff verified', ok: true,
         src: tc('''class C {
                       @Requires({ (0..<a.length - 1).every { a[it] <= a[it + 1] } && 0 <= k && k + 1 < a.length })
                       @Ensures({ result <= 0 })
                       static int diff(Integer[] a, int k) { a[k] - a[k + 1] }
                   }''')],
        [group: 'boxed & list', name: 'Integer[] bounds bug refuted', expect: 'IndexOutOfBoundsException',
         src: tc('class C { static int g(Integer[] a, int i) { a[i] } }')],
        [group: 'boxed & list', name: 'List<Integer> index read (range.every)', ok: true,
         src: tc('''class C {
                       @Requires({ (0..<xs.size()).every { xs[it] >= 0 } && 0 <= k && k < xs.size() })
                       @Ensures({ result >= 0 })
                       static int get(List<Integer> xs, int k) { xs[k] }
                   }''')],
        [group: 'boxed & list', name: 'List<Integer> index read (element-wise every)', ok: true,
         src: tc('''class C {
                       @Requires({ xs.every { it >= 0 } && 0 <= k && k < xs.size() })
                       @Ensures({ result >= 0 })
                       static int get(List<Integer> xs, int k) { xs[k] }
                   }''')],
        [group: 'boxed & list', name: 'List<Integer> subscript store frame', ok: true,
         src: tc('''class C {
                       @Requires({ 0 <= j && j < xs.size() })
                       @Ensures({ xs[j] == v })
                       static void set(List<Integer> xs, int j, int v) { xs[j] = v }
                   }''')],
        [group: 'boxed & list', name: 'List<Integer> sorted-diff verified', ok: true,
         src: tc('''class C {
                       @Requires({ (0..<xs.size() - 1).every { xs[it] <= xs[it + 1] } && 0 <= k && k + 1 < xs.size() })
                       @Ensures({ result <= 0 })
                       static int diff(List<Integer> xs, int k) { xs[k] - xs[k + 1] }
                   }''')],
        // List<String>: value reasoning over elements is out of fragment, but the index-bounds safety
        // check is element-type-agnostic — guarded verifies, unguarded refutes.
        [group: 'boxed & list', name: 'List<String> guarded index verified', ok: true,
         src: tc('''class C {
                       @Requires({ 0 <= k && k < xs.size() })
                       static String get(List<String> xs, int k) { xs[k] }
                   }''')],
        [group: 'boxed & list', name: 'List<String> unguarded index refuted', expect: 'IndexOutOfBoundsException',
         src: tc('class C { static String g(List<String> xs, int i) { xs[i] } }')],

        // ---------- Phase 15a (step 3): class @Invariant — entry-assume + exit-prove ----------
        // Entry-assume: the class invariant gives a fact the @Ensures otherwise can't show.
        [group: 'P15a class-invariant', name: 'invariant assumed at entry', ok: true,
         src: tc('''@groovy.contracts.Invariant({ count >= 0 })
                    class C { int count
                        @Ensures({ result >= 0 })
                        int get() { count }
                    }''')],
        // Exit-prove (void, invariant-only): the mutator preserves the invariant.
        [group: 'P15a class-invariant', name: 'invariant preserved by inc', ok: true,
         src: tc('''@groovy.contracts.Invariant({ count >= 0 })
                    class C { int count
                        void inc() { count = count + 1 }
                    }''')],
        // Exit-prove (refuted): a mutator that can drop count below zero violates the invariant.
        [group: 'P15a class-invariant', name: 'invariant broken by dec refuted',
         expect: 'Cannot prove class invariant',
         src: tc('''@groovy.contracts.Invariant({ count >= 0 })
                    class C { int count
                        void dec() { count = count - 1 }
                    }''')],
        // The @Requires guard plus the entry-assumed invariant together establish the exit obligation.
        [group: 'P15a class-invariant', name: 'guarded dec preserves invariant', ok: true,
         src: tc('''@groovy.contracts.Invariant({ count >= 0 })
                    class C { int count
                        @Requires({ count > 0 })
                        void dec() { count = count - 1 }
                    }''')],
        // Step 4 — the class invariant `n <= a.length` lets `a[i]` inside a counted loop verify
        // without restating the bound in @Requires on every method. The implicit-obligation pass
        // sees the invariant alongside the loop's @Invariant when discharging the index check.
        [group: 'P15a class-invariant', name: 'loop body uses class invariant', ok: true,
         src: tc('''@groovy.contracts.Invariant({ a != null && 0 <= n && n <= a.length })
                    class C { int[] a; int n
                        int sum() {
                            int s = 0; int i = 0
                            @Invariant({ 0 <= i && i <= n })
                            while (i < n) { s = s + a[i]; i = i + 1 }
                            return s
                        }
                    }''')],
        // Step 5 — an invariant whose body is outside the encoder fragment (a {@code split} call,
        // which returns an array — list-from-string is structurally invasive and not yet wired)
        // is dropped with a single "Skipped class invariant" diagnostic at the method level.
        // Verification continues for everything else.
        [group: 'P15a class-invariant', name: 'unmodelled invariant skipped',
         expect: 'Skipped class invariant',
         src: tc('''@groovy.contracts.Invariant({ name.split(",").length > 0 })
                    class C { String name
                        int n() { 0 }
                    }''')],
        // Step 6 — a child inherits the parent's class invariant (AND-conjoined). The child's
        // inc() must hold both clauses at exit: `count >= 0` (parent) and `count <= max` (child).
        // Without the parent clause inherited, the verifier would have no way to know count stays
        // non-negative after the increment — so this case is the end-to-end proof that the super-
        // walk wired in step 2 flows through to the discharge sites.
        [group: 'P15a class-invariant', name: 'parent invariant inherited', ok: true,
         src: tc('''@groovy.contracts.Invariant({ count >= 0 })
                    class P { int count }
                    @groovy.contracts.Invariant({ count <= max })
                    class C extends P { int max
                        @Requires({ count < max })
                        void inc() { count = count + 1 }
                    }''')],
        // Step 7 — a static method on an @Invariant class is not subject to the invariant
        // (no `this`). The method verifies even though its body would violate the invariant if
        // applied as an exit obligation — confirming the isStatic() skip in beforeVisitMethod.
        [group: 'P15a class-invariant', name: 'static method skips invariant', ok: true,
         src: tc('''@groovy.contracts.Invariant({ count >= 0 })
                    class C { int count
                        static int twice(int x) { x + x }
                    }''')],

        // ---------- Phase 15b: class @Invariant on constructors (establishment) ----------
        // Default constructor: int fields default-init to 0, so `count >= 0` holds at exit. The
        // implicit no-arg constructor doesn't appear in declaredConstructors; an explicit empty one
        // does. (A class with no explicit constructor and no body to verify is uninteresting here.)
        [group: 'P15b ctor-invariant', name: 'empty constructor establishes default-Int invariant', ok: true,
         src: tc('''@groovy.contracts.Invariant({ count >= 0 })
                    class C { int count
                        C() { }
                    }''')],
        // Constructor body assigns an explicit value the invariant requires — verifies.
        [group: 'P15b ctor-invariant', name: 'constructor sets count from non-negative argument', ok: true,
         src: tc('''@groovy.contracts.Invariant({ count >= 0 })
                    class C { int count
                        @Requires({ initial >= 0 })
                        C(int initial) { count = initial }
                    }''')],
        // Without the @Requires guard, the argument might be negative — the invariant is violated
        // at constructor exit. Refute with the OpenJML-shaped class-invariant message.
        [group: 'P15b ctor-invariant', name: 'constructor with negative initial refuted',
         expect: 'Cannot prove class invariant',
         src: tc('''@groovy.contracts.Invariant({ count >= 0 })
                    class C { int count
                        C(int initial) { count = initial }
                    }''')],
        // Establishment AND maintenance compose: a class with both a constructor and a mutator,
        // both verifying under the same invariant.
        [group: 'P15b ctor-invariant', name: 'constructor + mutator compose', ok: true,
         src: tc('''@groovy.contracts.Invariant({ count >= 0 && count <= max })
                    class C { int count, max
                        @Requires({ m > 0 })
                        C(int m) { max = m }
                        @Requires({ count < max })
                        void inc() { count = count + 1 }
                    }''')],
        // Soundness: a constructor that violates the bound (count = max + 1) is caught.
        [group: 'P15b ctor-invariant', name: 'constructor that overshoots bound refuted',
         expect: 'Cannot prove class invariant',
         src: tc('''@groovy.contracts.Invariant({ count >= 0 && count <= max })
                    class C { int count, max
                        C(int m) { max = m; count = m + 1 }
                    }''')],

        // ---------- Phase 29: Sets.boundedBy / Sets.boundedCount generalised to enum-element sets ----------
        // FSM via ordinals — the workaround pattern still works.
        [group: 'P29 enum-sets', name: 'FSM via Set<Integer> ordinals: full coverage verifies', ok: true,
         src: tc('''class FSM {
                        enum State { IDLE, RUNNING, DONE }
                        Set<Integer> handled
                        @Requires({ Sets.boundedCount(handled, State.values().length) == State.values().length })
                        @Ensures({ (0..<State.values().length).every { it in handled } })
                        boolean allHandled() { true }
                    }''')],
        // Direct Set<State> spelling — the headline Phase 29 capability. Sets.boundedCount(s, N) where
        // N is the enum's domain size proves every state is handled, via the iff axiom asserted
        // at setFor time.
        [group: 'P29 enum-sets', name: 'FSM via Set<State>: full coverage entails every state', ok: true,
         src: tc('''class FSM {
                        enum State { IDLE, RUNNING, DONE }
                        Set<State> handled
                        @Requires({ Sets.boundedCount(handled, State.values().length) == State.values().length })
                        @Ensures({ State.IDLE in handled && State.RUNNING in handled && State.DONE in handled })
                        boolean allHandled() { true }
                    }''')],
        // Soundness: without the full-coverage @Requires, the full-state @Ensures must refute.
        [group: 'P29 enum-sets', name: 'partial coverage cannot prove every state',
         expect: 'Cannot prove postcondition',
         src: tc('''class FSM {
                        enum State { IDLE, RUNNING, DONE }
                        Set<State> handled
                        @Ensures({ State.IDLE in handled && State.RUNNING in handled && State.DONE in handled })
                        boolean allHandled() { true }
                    }''')],
        // Pigeonhole: card(Set<Enum>) <= enum.values().length asserted at setFor time, so a
        // postcondition relying on it (s.size() <= 3 for a 3-state enum) verifies without an
        // explicit Sets.boundedBy clause.
        [group: 'P29 enum-sets', name: 'pigeonhole bound is automatic for enum sets', ok: true,
         src: tc('''class FSM {
                        enum State { IDLE, RUNNING, DONE }
                        @Ensures({ s.size() <= 3 })
                        static int f(Set<State> s) { 0 }
                    }''')],
        // Sets.boundedBy over Set<Enum> with matching n verifies (pigeonhole + iff already asserted).
        [group: 'P29 enum-sets', name: 'Sets.boundedBy matching enum size verifies', ok: true,
         src: tc('''class FSM {
                        enum State { IDLE, RUNNING, DONE }
                        @Requires({ Sets.boundedBy(s, State.values().length) })
                        @Ensures({ s.size() <= State.values().length })
                        static int f(Set<State> s) { 0 }
                    }''')],
        // Sets.boundedBy with NON-matching n on enum set: still skips (no partial-ordering meaning).
        [group: 'P29 enum-sets', name: 'Sets.boundedBy non-matching n on enum set skipped',
         expect: 'outside fragment',
         src: tc('''class FSM {
                        enum State { IDLE, RUNNING, DONE }
                        @Requires({ Sets.boundedBy(s, 2) })
                        @Ensures({ s.size() <= 2 })
                        static int f(Set<State> s) { 0 }
                    }''')],

        // ---------- Phase 30: s.containsAll(t) — subset reasoning over enum-element sets ----------
        // Subset assumption carries through: granted ⊇ required ∧ x ∈ required ⟹ x ∈ granted.
        [group: 'P30 subset', name: 'containsAll: subset entails membership transfer', ok: true,
         src: tc('''class C {
                        enum Role { ADMIN, USER, GUEST }
                        @Requires({ granted.containsAll(required) && Role.ADMIN in required })
                        @Ensures({ Role.ADMIN in granted })
                        static int check(Set<Role> granted, Set<Role> required) { 0 }
                    }''')],
        // Soundness: if granted does NOT contain all of required, the claim can refute.
        [group: 'P30 subset', name: 'containsAll: membership without subset refuted',
         expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        enum Role { ADMIN, USER, GUEST }
                        @Requires({ Role.ADMIN in required })
                        @Ensures({ Role.ADMIN in granted })
                        static int check(Set<Role> granted, Set<Role> required) { 0 }
                    }''')],
        // Reflexivity — every set contains all of itself (every constant ∈ s ⟹ ∈ s, trivially).
        [group: 'P30 subset', name: 'containsAll: reflexivity', ok: true,
         src: tc('''class C {
                        enum Role { ADMIN, USER, GUEST }
                        @Ensures({ s.containsAll(s) })
                        static int f(Set<Role> s) { 0 }
                    }''')],
        // Transitivity: a ⊇ b ∧ b ⊇ c ⟹ a ⊇ c. Each containsAll lowers to a per-constant
        // implication; the conjunction chain gives transitive ⟹ for each constant.
        [group: 'P30 subset', name: 'containsAll: transitivity', ok: true,
         src: tc('''class C {
                        enum Role { ADMIN, USER, GUEST }
                        @Requires({ a.containsAll(b) && b.containsAll(c) })
                        @Ensures({ a.containsAll(c) })
                        static int f(Set<Role> a, Set<Role> b, Set<Role> c) { 0 }
                    }''')],
        // Empty subset: `granted.containsAll(required)` when required.size() == 0. Verifies via
        // the empty iff `card(s) == 0 ⟺ no enum constant ∈ s` — so the per-constant implications
        // `c ∈ required ⟹ c ∈ granted` are all vacuously true.
        [group: 'P30 subset', name: 'containsAll: empty subset', ok: true,
         src: tc('''class C {
                        enum Role { ADMIN, USER, GUEST }
                        @Requires({ required.size() == 0 })
                        @Ensures({ granted.containsAll(required) })
                        static int f(Set<Role> granted, Set<Role> required) { 0 }
                    }''')],
        // Composition with @Modifies: a grant operation that adds a role preserves the subset
        // claim against a stable `required` set.
        [group: 'P30 subset', name: 'containsAll: add preserves subset', ok: true,
         src: tc('''class C {
                        enum Role { ADMIN, USER, GUEST }
                        Set<Role> granted
                        @Requires({ granted.containsAll(required) })
                        @Modifies({ this.granted })
                        @Ensures({ granted.containsAll(required) })
                        void grant(Set<Role> required, Role r) { granted.add(r) }
                    }''')],
        // Int-element subset WITHOUT a bound on the subset operand still skips honestly.
        [group: 'P30 subset', name: 'containsAll: Int-element subset without bound skipped',
         expect: 'outside fragment',
         src: tc('''class C {
                        @Requires({ a.containsAll(b) })
                        @Ensures({ true })
                        static int f(Set<Integer> a, Set<Integer> b) { 0 }
                    }''')],

        // ---------- Phase 31: Int-element s.containsAll(t) via bounded-domain context ----------
        // With Sets.boundedBy(t, n) registered, subset entails membership transfer for any in-domain
        // element — the bounded-universal lowering instantiates at the in-bounds witness.
        [group: 'P31 int-subset', name: 'Int subset with Sets.boundedBy verifies membership transfer', ok: true,
         src: tc('''class C {
                        @Requires({ Sets.boundedBy(required, n) && granted.containsAll(required) &&
                                    0 <= u && u < n && u in required })
                        @Ensures({ u in granted })
                        static int f(Set<Integer> granted, Set<Integer> required, int n, int u) { 0 }
                    }''')],
        // Soundness: without the containsAll, membership in required doesn't transfer to granted.
        [group: 'P31 int-subset', name: 'Int subset: membership without subset refuted',
         expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Requires({ Sets.boundedBy(required, n) && 0 <= u && u < n && u in required })
                        @Ensures({ u in granted })
                        static int f(Set<Integer> granted, Set<Integer> required, int n, int u) { 0 }
                    }''')],
        // Reflexivity: s.containsAll(s) once s is bounded — the bounded universal degenerates
        // to ∀i. 0<=i<n ⟹ (i ∈ s ⟹ i ∈ s), trivially true.
        [group: 'P31 int-subset', name: 'Int subset: reflexivity', ok: true,
         src: tc('''class C {
                        @Requires({ Sets.boundedBy(s, n) })
                        @Ensures({ s.containsAll(s) })
                        static int f(Set<Integer> s, int n) { 0 }
                    }''')],
        // Transitivity: a ⊇ b ∧ b ⊇ c ⟹ a ⊇ c, when all three are bounded by the same n. Z3
        // chains the bounded universals via the shared range guard.
        [group: 'P31 int-subset', name: 'Int subset: transitivity', ok: true,
         src: tc('''class C {
                        @Requires({ Sets.boundedBy(b, n) && Sets.boundedBy(c, n) &&
                                    a.containsAll(b) && b.containsAll(c) })
                        @Ensures({ a.containsAll(c) })
                        static int f(Set<Integer> a, Set<Integer> b, Set<Integer> c, int n) { 0 }
                    }''')],
        // Bound on the SUPERSET (not the subset operand) doesn't unblock — the universal needs
        // to range over the subset's domain. Honest skip.
        [group: 'P31 int-subset', name: 'Int subset: bound on superset only still skips',
         expect: 'outside fragment',
         src: tc('''class C {
                        @Requires({ Sets.boundedBy(granted, n) && granted.containsAll(required) })
                        @Ensures({ true })
                        static int f(Set<Integer> granted, Set<Integer> required, int n) { 0 }
                    }''')],

        // ---------- Phase 32a: m.containsValue(v) over enum-keyed maps ----------
        // A value the map has under some enum key is "containsValue"-true. Lowered to a finite
        // disjunction over the enum's key constants.
        [group: 'P32 containsValue/equals', name: 'containsValue: key-pinned value verifies', ok: true,
         src: tc('''class C {
                        enum State { IDLE, RUNNING, DONE }
                        @Requires({ m[State.RUNNING] == 42 })
                        @Ensures({ m.containsValue(42) })
                        static int f(Map<State,Integer> m) { 0 }
                    }''')],
        // Soundness: without a key fixed to the value, containsValue cannot be proved.
        [group: 'P32 containsValue/equals', name: 'containsValue: no key fixes the value, refuted',
         expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        enum State { IDLE, RUNNING, DONE }
                        @Ensures({ m.containsValue(42) })
                        static int f(Map<State,Integer> m) { 0 }
                    }''')],
        // Works for String-valued maps too (any value sort).
        [group: 'P32 containsValue/equals', name: 'containsValue: String-valued map', ok: true,
         src: tc('''class C {
                        enum State { IDLE, RUNNING, DONE }
                        @Requires({ m[State.DONE] == "ok" })
                        @Ensures({ m.containsValue("ok") })
                        static int f(Map<State,String> m) { 0 }
                    }''')],
        // Int-keyed maps skip honestly (no finite key domain to enumerate).
        [group: 'P32 containsValue/equals', name: 'containsValue: Int-keyed map skipped',
         expect: 'outside fragment',
         src: tc('''class C {
                        @Requires({ m[5] == 42 })
                        @Ensures({ m.containsValue(42) })
                        static int f(Map<Integer,Integer> m) { 0 }
                    }''')],

        // ---------- Phase 32b: s.equals(t) for sets via containsAll composition ----------
        // Set equality via mutual subset — both directions composed from the Phase-30/31 subset
        // lowering. Verifies when mutual subset assumptions are made.
        [group: 'P32 containsValue/equals', name: 'set equals: mutual subset entails equals', ok: true,
         src: tc('''class C {
                        enum Role { ADMIN, USER, GUEST }
                        @Requires({ a.containsAll(b) && b.containsAll(a) })
                        @Ensures({ a.equals(b) })
                        static int f(Set<Role> a, Set<Role> b) { 0 }
                    }''')],
        // Soundness: without mutual subset, equals refutes.
        [group: 'P32 containsValue/equals', name: 'set equals: one-way subset insufficient',
         expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        enum Role { ADMIN, USER, GUEST }
                        @Requires({ a.containsAll(b) })
                        @Ensures({ a.equals(b) })
                        static int f(Set<Role> a, Set<Role> b) { 0 }
                    }''')],
        // Reflexivity — s.equals(s) is trivially true (forward and backward subset both reflexive).
        [group: 'P32 containsValue/equals', name: 'set equals: reflexivity', ok: true,
         src: tc('''class C {
                        enum Role { ADMIN, USER, GUEST }
                        @Ensures({ s.equals(s) })
                        static int f(Set<Role> s) { 0 }
                    }''')],

        // ---------- Phase 33: inline set union / intersection (lazy lowering on .contains, .containsAll) ----------
        // Union .contains: membership in (a + b) follows from membership in either operand.
        [group: 'P33 union/intersect', name: 'union: contains is disjunction of operand memberships', ok: true,
         src: tc('''class C {
                        enum Role { ADMIN, USER, GUEST }
                        @Requires({ Role.ADMIN in a })
                        @Ensures({ Role.ADMIN in (a + b) })
                        static int f(Set<Role> a, Set<Role> b) { 0 }
                    }''')],
        // Soundness: union .contains refuted when neither operand contains the element.
        [group: 'P33 union/intersect', name: 'union: contains refuted when neither operand has it',
         expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        enum Role { ADMIN, USER, GUEST }
                        @Ensures({ Role.ADMIN in (a + b) })
                        static int f(Set<Role> a, Set<Role> b) { 0 }
                    }''')],
        // Intersection .contains: membership in (a ∩ b) requires membership in BOTH operands.
        [group: 'P33 union/intersect', name: 'intersect: contains is conjunction', ok: true,
         src: tc('''class C {
                        enum Role { ADMIN, USER, GUEST }
                        @Requires({ Role.ADMIN in a && Role.ADMIN in b })
                        @Ensures({ Role.ADMIN in a.intersect(b) })
                        static int f(Set<Role> a, Set<Role> b) { 0 }
                    }''')],
        // Soundness: intersection refuted when only one operand contains the element.
        [group: 'P33 union/intersect', name: 'intersect: contains refuted with only one operand',
         expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        enum Role { ADMIN, USER, GUEST }
                        @Requires({ Role.ADMIN in a })
                        @Ensures({ Role.ADMIN in a.intersect(b) })
                        static int f(Set<Role> a, Set<Role> b) { 0 }
                    }''')],
        // Union .containsAll: every element of u is in a OR in b.
        [group: 'P33 union/intersect', name: 'union: containsAll via finite conjunction', ok: true,
         src: tc('''class C {
                        enum Role { ADMIN, USER, GUEST }
                        @Requires({ a.containsAll(u) })
                        @Ensures({ (a + b).containsAll(u) })
                        static int f(Set<Role> a, Set<Role> b, Set<Role> u) { 0 }
                    }''')],
        // Intersection .containsAll: every element of u must be in BOTH a and b.
        [group: 'P33 union/intersect', name: 'intersect: containsAll via finite conjunction', ok: true,
         src: tc('''class C {
                        enum Role { ADMIN, USER, GUEST }
                        @Requires({ a.containsAll(u) && b.containsAll(u) })
                        @Ensures({ a.intersect(b).containsAll(u) })
                        static int f(Set<Role> a, Set<Role> b, Set<Role> u) { 0 }
                    }''')],
        // Soundness anchor: union .containsAll refutes when neither operand alone covers u.
        [group: 'P33 union/intersect', name: 'union: containsAll refuted with neither operand covering',
         expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        enum Role { ADMIN, USER, GUEST }
                        @Ensures({ (a + b).containsAll(u) })
                        static int f(Set<Role> a, Set<Role> b, Set<Role> u) { 0 }
                    }''')],

        // ---------- Phase 35: materialised set ops (Set u = a + b as first-class set) ----------
        // Materialised union: the new local `u` is a first-class set with the membership iff axiom.
        // The body uses `ADMIN in u` to drive the return value; under @Requires({ ADMIN in a }) the
        // iff makes `ADMIN in u` provably true, so result == 1 is verified.
        // (@Ensures can't reference body-locals through the @TypeChecked closure scope, so we drive
        //  the postcondition via the result instead — the meaningful work happens in the body.)
        [group: 'P35 materialised set', name: 'materialised union: member follows from operand member', ok: true,
         src: tc('''class C {
                        enum Role { ADMIN, USER, GUEST }
                        @Requires({ Role.ADMIN in a })
                        @Ensures({ result == 1 })
                        static int f(Set<Role> a, Set<Role> b) {
                            Set<Role> u = a + b
                            Role.ADMIN in u ? 1 : 0
                        }
                    }''')],
        // Materialised intersection: ADMIN in u requires ADMIN in BOTH operands.
        // The intersect's GDK signature returns Collection, so the assignment needs an explicit
        // `as Set<Role>` cast — setBinopFor unwraps the outer CastExpression. Explicit non-null
        // guards on a/b because `.intersect` is a method call (implicit-NPE obligation), unlike `+`.
        [group: 'P35 materialised set', name: 'materialised intersection: member requires both operands', ok: true,
         src: tc('''class C {
                        enum Role { ADMIN, USER, GUEST }
                        @Requires({ a != null && b != null && Role.ADMIN in a && Role.ADMIN in b })
                        @Ensures({ result == 1 })
                        static int f(Set<Role> a, Set<Role> b) {
                            Set<Role> u = a.intersect(b) as Set<Role>
                            Role.ADMIN in u ? 1 : 0
                        }
                    }''')],
        // Soundness: when neither operand contains ADMIN, the body's branch must go to 0 — but
        // the @Ensures result == 1 fails. The refute confirms the iff axiom isn't over-strong.
        [group: 'P35 materialised set', name: 'materialised union: member refuted when neither operand has it',
         expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        enum Role { ADMIN, USER, GUEST }
                        @Ensures({ result == 1 })
                        static int f(Set<Role> a, Set<Role> b) {
                            Set<Role> u = a + b
                            Role.ADMIN in u ? 1 : 0
                        }
                    }''')],
        // Pigeonhole on the materialised set: `u.size() <= 3` auto-holds via the enum-domain axioms
        // (set u is a Set<Role> with N=3 constants, so card(u) ≤ N is asserted on mint).
        [group: 'P35 materialised set', name: 'materialised union: pigeonhole on size', ok: true,
         src: tc('''class C {
                        enum Role { ADMIN, USER, GUEST }
                        @Ensures({ u.size() <= 3 })
                        static int f(Set<Role> a, Set<Role> b) {
                            Set<Role> u = a + b
                            0
                        }
                    }''')],
        // containsAll composes through the materialised set: if a covers z then so does a + b.
        // The iff axiom on u gives every-element-of-u-is-in-a-or-b; combined with a.containsAll(z),
        // every-element-of-z-is-in-u follows.
        [group: 'P35 materialised set', name: 'materialised union: containsAll composes through u', ok: true,
         src: tc('''class C {
                        enum Role { ADMIN, USER, GUEST }
                        @Requires({ a.containsAll(z) })
                        @Ensures({ u.containsAll(z) })
                        static int f(Set<Role> a, Set<Role> b, Set<Role> z) {
                            Set<Role> u = a + b
                            0
                        }
                    }''')],
        // equals through the materialised set: a + b = b + a (commutativity), verified via mutual
        // containsAll on the materialised forms.
        [group: 'P35 materialised set', name: 'materialised union: commutativity via equals', ok: true,
         src: tc('''class C {
                        enum Role { ADMIN, USER, GUEST }
                        @Ensures({ u.equals(v) })
                        static int f(Set<Role> a, Set<Role> b) {
                            Set<Role> u = a + b
                            Set<Role> v = b + a
                            0
                        }
                    }''')],

        // ---------- Phase 36: Map<K, Set<V>> nesting (read-only) ----------
        // Enum key + enum value set: x in m[k] over Map<Role, Set<Role>> lowers to membership in
        // the inner set, an SMT array term (no named handle minted). Round-trip identity.
        [group: 'P36 nested map<set>', name: 'enum/enum: in m[k] round-trip', ok: true,
         src: tc('''class C {
                        enum Role { ADMIN, USER, GUEST }
                        @Requires({ Role.USER in m[Role.ADMIN] })
                        @Ensures({ Role.USER in m[Role.ADMIN] })
                        static int f(Map<Role, Set<Role>> m) { 0 }
                    }''')],
        // m[k].contains(x) as method-form sibling of `in` — same lowering through
        // translateMethodCall instead of translateBinary.
        [group: 'P36 nested map<set>', name: 'enum/enum: m[k].contains round-trip', ok: true,
         src: tc('''class C {
                        enum Role { ADMIN, USER, GUEST }
                        @Requires({ m[Role.ADMIN].contains(Role.USER) })
                        @Ensures({ m[Role.ADMIN].contains(Role.USER) })
                        static int f(Map<Role, Set<Role>> m) { 0 }
                    }''')],
        // Soundness: m[k] at one key tells us nothing about m[k'] at another key.
        [group: 'P36 nested map<set>', name: 'enum/enum: distinct keys do not leak membership',
         expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        enum Role { ADMIN, USER, GUEST }
                        @Requires({ Role.USER in m[Role.ADMIN] })
                        @Ensures({ Role.USER in m[Role.GUEST] })
                        static int f(Map<Role, Set<Role>> m) { 0 }
                    }''')],
        // containsAll on the nested set: m[k] covers an enum-element subset s ⟹ every constant of
        // s is in m[k]. Finite conjunction over the inner enum domain.
        [group: 'P36 nested map<set>', name: 'enum/enum: m[k].containsAll(s) over enum V', ok: true,
         src: tc('''class C {
                        enum Role { ADMIN, USER, GUEST }
                        @Requires({ m[Role.ADMIN].containsAll(s) && Role.USER in s })
                        @Ensures({ Role.USER in m[Role.ADMIN] })
                        static int f(Map<Role, Set<Role>> m, Set<Role> s) { 0 }
                    }''')],
        // Non-enum inner element type: Map<Role, Set<Integer>>. Membership lowers through the
        // Int sort cleanly; .containsAll over Int element domain is out of scope (needs
        // bounded universal with intSubsetBounds on a transient receiver — known limit).
        [group: 'P36 nested map<set>', name: 'enum/Int: in m[k] over Set<Integer> values', ok: true,
         src: tc('''class C {
                        enum Role { ADMIN, USER, GUEST }
                        @Requires({ 42 in m[Role.ADMIN] })
                        @Ensures({ 42 in m[Role.ADMIN] })
                        static int f(Map<Role, Set<Integer>> m) { 0 }
                    }''')],
        // Composes with Phase 32a's containsKey: m.containsKey rides the independent key-set,
        // which is unaffected by the nested-value-sort change.
        [group: 'P36 nested map<set>', name: 'enum/enum: m.containsKey still works alongside nested values', ok: true,
         src: tc('''class C {
                        enum Role { ADMIN, USER, GUEST }
                        @Requires({ m.containsKey(Role.ADMIN) && Role.USER in m[Role.ADMIN] })
                        @Ensures({ m.containsKey(Role.ADMIN) })
                        static int f(Map<Role, Set<Role>> m) { 0 }
                    }''')],
        // README example anchor: RBAC over Map<Role, Set<Perm>>. ADMIN covering the required
        // permission set implies a specific requested perm is in ADMIN's grant set via the
        // finite conjunction over Perm constants.
        [group: 'P36 nested map<set>', name: 'README RBAC: adminMayWrite verifies', ok: true,
         src: tc('''class Acl {
                        enum Role { ADMIN, USER, GUEST }
                        enum Perm { READ, WRITE, DELETE }
                        @Requires({ grants[Role.ADMIN].containsAll(required) })
                        @Ensures({ (Perm.WRITE in required) ==> (Perm.WRITE in grants[Role.ADMIN]) })
                        static int adminMayWrite(Map<Role, Set<Perm>> grants, Set<Perm> required) { 0 }
                    }''')],
        // Soundness anchor: without the containsAll precondition, the postcondition refutes.
        [group: 'P36 nested map<set>', name: 'README RBAC: refutes without containsAll',
         expect: 'Cannot prove postcondition',
         src: tc('''class Acl {
                        enum Role { ADMIN, USER, GUEST }
                        enum Perm { READ, WRITE, DELETE }
                        @Ensures({ (Perm.WRITE in required) ==> (Perm.WRITE in grants[Role.ADMIN]) })
                        static int adminMayWrite(Map<Role, Set<Perm>> grants, Set<Perm> required) { 0 }
                    }''')],

        // ---------- Phase 37: element nullability ----------
        // Refute: xs[0].method() without a per-element non-null guarantee. The bounds @Requires lets
        // the index check pass; the nullity obligation still fires because xs[0] is unconstrained.
        [group: 'P37 element null', name: 'unguarded xs[i].method() refutes',
         expect: 'Possible NullPointerException: Cannot invoke method length()',
         src: tc('''class C {
                        @Requires({ xs.size() > 0 })
                        static int f(List<String> xs) { xs[0].length() }
                    }''')],
        // Verify: @Requires({ xs[i] != null }) constrains the per-element nullity oracle, which
        // discharges the implicit obligation at the .length() deref.
        [group: 'P37 element null', name: 'guarded by @Requires xs[i] != null verifies', ok: true,
         src: tc('''class C {
                        @Requires({ xs.size() > 0 && xs[0] != null })
                        static int f(List<String> xs) { xs[0].length() }
                    }''')],
        // Verify: in-body if-guard discharges via the path-fact mechanism — same oracle.
        [group: 'P37 element null', name: 'in-body if (xs[i] != null) guard verifies', ok: true,
         src: tc('''class C {
                        @Requires({ xs.size() > 0 })
                        static int f(List<String> xs) {
                            if (xs[0] != null) return xs[0].length()
                            return 0
                        }
                    }''')],
        // Refute soundness: a guard on xs[0] doesn't license a deref on xs[1].
        [group: 'P37 element null', name: 'guard on wrong index refutes',
         expect: 'Possible NullPointerException: Cannot invoke method length()',
         src: tc('''class C {
                        @Requires({ xs.size() > 1 && xs[0] != null })
                        static int f(List<String> xs) { xs[1].length() }
                    }''')],
        // xs.get(i) shape: same lowering through translateBinary's null path; same DerefSite.
        [group: 'P37 element null', name: 'xs.get(i).method() shape: refute',
         expect: 'Possible NullPointerException: Cannot invoke method length()',
         src: tc('''class C {
                        @Requires({ xs.size() > 0 })
                        static int f(List<String> xs) { xs.get(0).length() }
                    }''')],
        // The scalar deref on xs itself fires (xs.get(0) is a method call), so xs != null also needed.
        [group: 'P37 element null', name: 'xs.get(i).method() shape: verify with @Requires xs.get(i) != null', ok: true,
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() > 0 && xs.get(0) != null })
                        static int f(List<String> xs) { xs.get(0).length() }
                    }''')],
        // ---------- Phase 38: immutable-container factory recognition ----------
        // List.of(...).size() folds to a literal count — usable as a ground int in @Ensures.
        [group: 'P38 factory', name: 'List.of(args).size() folds to literal', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 3 })
                        static int f() { List.of(1, 2, 3).size() }
                    }''')],
        // Soundness: List.of(1, 2, 3).size() is provably 3, not 4 — refute the wrong literal.
        [group: 'P38 factory', name: 'List.of size: wrong literal refutes',
         expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Ensures({ result == 4 })
                        static int f() { List.of(1, 2, 3).size() }
                    }''')],
        // Groovy list literal: same fold via the ListExpression branch.
        [group: 'P38 factory', name: 'Groovy [a, b, c].size() folds', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 2 })
                        static int f() { [10, 20].size() }
                    }''')],
        // .contains() over a list factory: disjunction over the entries.
        [group: 'P38 factory', name: 'List.of(...).contains folds to disjunction', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { List.of(1, 2, 3).contains(2) ? 1 : 0 }
                    }''')],
        // Soundness on contains: refute the wrong claim.
        [group: 'P38 factory', name: 'List.of(...).contains refutes wrong element',
         expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { List.of(1, 2, 3).contains(99) ? 1 : 0 }
                    }''')],
        // `x in [...]` operator form, same lowering as .contains.
        [group: 'P38 factory', name: 'x in [a, b, c] operator folds', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { (2 in [1, 2, 3]) ? 1 : 0 }
                    }''')],
        // List.of(...).get(literal_i) folds to the literal element.
        [group: 'P38 factory', name: 'List.of(...).get(0) folds to first element', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 10 })
                        static int f() { List.of(10, 20, 30).get(0) }
                    }''')],
        // [...][i] bracket-access on a Groovy list literal also folds.
        [group: 'P38 factory', name: '[a, b, c][i] bracket fold for constant i', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 20 })
                        static int f() { [10, 20, 30][1] }
                    }''')],
        // Set.of factory: .size and .contains the same way (uniqueness of args not enforced —
        // dedup-aware sizing is a known limit).
        [group: 'P38 factory', name: 'Set.of(args).size folds', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 3 })
                        static int f() { Set.of(1, 2, 3).size() }
                    }''')],
        // Map.of factory: keys/values via containsKey / containsValue.
        [group: 'P38 factory', name: 'Map.of(...).containsKey folds', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { Map.of("a", 1, "b", 2).containsKey("a") ? 1 : 0 }
                    }''')],
        [group: 'P38 factory', name: 'Map.of(...).get(k) ite-chain folds', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 2 })
                        static int f() { Map.of("a", 1, "b", 2).get("b") }
                    }''')],

        // ---------- Phase 38c: Set.of dedup check + transparent immutable wrappers ----------
        // Set.of with literal duplicates would throw IllegalArgumentException at runtime. We
        // refuse the fold rather than claim a wrong size. The test verifies the SKIP — without
        // a fold, the contract about size on Set.of(1, 1, 1) doesn't translate, so the
        // verifier emits a "postcondition outside fragment" diagnostic. (We could also refute,
        // but a skip is consistent with "honest unsoundness".)
        [group: 'P38c immutable', name: 'Set.of with literal duplicates skips the fold',
         expect: 'outside fragment',
         src: tc('''class C {
                        @Ensures({ result == 3 })
                        static int f() { Set.of(1, 1, 1).size() }
                    }''')],
        // Sanity: Set.of with literal-distinct args still folds the same as before.
        [group: 'P38c immutable', name: 'Set.of with distinct literals still folds', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 3 })
                        static int f() { Set.of(1, 2, 3).size() }
                    }''')],
        // Collections.unmodifiableList wraps a list-factory transparently; subsequent .size()
        // / .contains() / [i] operations fold as if the wrapper weren't there.
        [group: 'P38c immutable', name: 'Collections.unmodifiableList wraps factory transparently', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 3 })
                        static int f() { Collections.unmodifiableList(List.of(1, 2, 3)).size() }
                    }''')],
        [group: 'P38c immutable', name: 'unmodifiableList(...).contains folds', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() {
                            Collections.unmodifiableList(List.of(10, 20, 30)).contains(20) ? 1 : 0
                        }
                    }''')],
        // Groovy's .asImmutable() is the same idea via the GDK.
        [group: 'P38c immutable', name: '.asImmutable() unwraps for .size()', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 3 })
                        static int f() { [10, 20, 30].asImmutable().size() }
                    }''')],
        // Set.of wrapped by Collections.unmodifiableSet folds the same way.
        [group: 'P38c immutable', name: 'Collections.unmodifiableSet wraps Set.of', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 3 })
                        static int f() { Collections.unmodifiableSet(Set.of(1, 2, 3)).size() }
                    }''')],
        // Bracket access through a wrapper: unwrap, then fold the inner factory's i-th element.
        [group: 'P38c immutable', name: 'wrapped factory bracket-index folds', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 20 })
                        static int f() {
                            Collections.unmodifiableList([10, 20, 30])[1]
                        }
                    }''')],
        // Composes with factory-through-assignment (Phase 38b): wrap a local factory.
        [group: 'P38c immutable', name: 'wrap a local factory through assignment', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 3 })
                        static int f() {
                            List<Integer> xs = List.of(1, 2, 3)
                            xs.asImmutable().size()
                        }
                    }''')],

        // ---------- HumanEval port — strlen (Verus task 023) ----------
        // The Verus original (https://github.com/secure-foundations/human-eval-verus, gpt/023)
        // is spec-free; Verus only checks implicit overflow. groovy-verify ports the same body
        // and *adds the spec the original lacks*: result == xs.size(). Verifies cleanly with a
        // loop invariant carrying count == i across iterations and a decreases measure for
        // termination — exactly the shape any auto-active verifier needs for a counter loop.
        [group: 'HumanEval port', name: 'strlen (Verus 023) with @Ensures(result == size)', ok: true,
         src: tc('''class C {
                        @Requires({ xs != null })
                        @Ensures({ result == xs.size() })
                        static int strlen(List<Character> xs) {
                            int count = 0
                            int i = 0
                            @Invariant({ 0 <= i && i <= xs.size() && count == i })
                            @Decreases({ xs.size() - i })
                            while (i < xs.size()) {
                                count = count + 1
                                i = i + 1
                            }
                            return count
                        }
                    }''')],
        // ---------- HumanEval port — get_positive (Verus task 030) ----------
        // The Verus original is spec-free. groovy-verify adds the natural spec — the result list
        // has at most as many elements as the input — verifying through the empty-factory init,
        // the conditional add, and a returned-list result. Closes the empty-factory + mutate gap
        // (the factory record is invalidated on add) and the returned-list-oracle gap (result's
        // size/array are aliased to the local's threaded state).
        [group: 'HumanEval port', name: 'get_positive (Verus 030): result.size() <= xs.size()', ok: true,
         src: tc('''class C {
                        @Requires({ xs != null })
                        @Ensures({ result.size() <= xs.size() })
                        static List<Integer> getPositive(List<Integer> xs) {
                            List<Integer> positive = []
                            int i = 0
                            @Invariant({ positive != null && 0 <= i && i <= xs.size() && positive.size() <= i })
                            @Decreases({ xs.size() - i })
                            while (i < xs.size()) {
                                int x = xs[i]
                                if (x > 0) {
                                    positive.add(x)
                                }
                                i = i + 1
                            }
                            return positive
                        }
                    }''')],

        // ---------- Phase 46a: string predicates as uninterpreted Bool functions ----------
        // startsWith on a String parameter — proves a precondition that names the predicate.
        // The receiver routing kicks in via scalarTypes (s: String parameter).
        [group: 'P46a string preds', name: 'startsWith on String param: contract assumption flows', ok: true,
         src: tc('''class C {
                        @Requires({ s != null && s.startsWith("foo") })
                        @Ensures({ result == 1 })
                        static int hasFooPrefix(String s) { s.startsWith("foo") ? 1 : 0 }
                    }''')],
        // Distinct predicates aren't equated — startsWith vs endsWith are independent functions.
        [group: 'P46a string preds', name: 'startsWith and endsWith are independent',
         expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Requires({ s != null && s.startsWith("foo") })
                        @Ensures({ result == 1 })
                        static int f(String s) { s.endsWith("bar") ? 1 : 0 }
                    }''')],
        // contains/isEmpty route through the same dispatch — disambiguated from list semantics
        // by the scalarTypes check (which sees s: String, not List).
        [group: 'P46a string preds', name: 'String contains routes to string predicate (not list existential)', ok: true,
         src: tc('''class C {
                        @Requires({ s != null && s.contains("admin") })
                        @Ensures({ result == 1 })
                        static int f(String s) { s.contains("admin") ? 1 : 0 }
                    }''')],
        [group: 'P46a string preds', name: 'String isEmpty as unary predicate', ok: true,
         src: tc('''class C {
                        @Requires({ s != null && s.isEmpty() })
                        @Ensures({ result == 1 })
                        static int f(String s) { s.isEmpty() ? 1 : 0 }
                    }''')],
        // Routing on List<String>[i] — xs[i].startsWith(p) for List<String> xs.
        [group: 'P46a string preds', name: 'startsWith on xs[i] for List<String>', ok: true,
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() > 0 && xs[0] != null && xs[0].startsWith("foo") })
                        @Ensures({ result == 1 })
                        static int f(List<String> xs) { xs[0].startsWith("foo") ? 1 : 0 }
                    }''')],

        // ---------- Phase 46b: string length oracle with literal pinning ----------
        // Literal pinning: "hello".length() == 5 folds via the mint-time pin.
        [group: 'P46b string length', name: 'literal length pinned', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 5 })
                        static int f() { "hello".length() }
                    }''')],
        // GDK alias size() on a String routes to length too — Groovy treats them as synonyms.
        [group: 'P46b string length', name: 'String size() == length()', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 5 })
                        static int f() { "hello".size() }
                    }''')],
        // Wrong length refutes — the pinning is exact.
        [group: 'P46b string length', name: 'wrong literal length refutes',
         expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Ensures({ result == 4 })
                        static int f() { "hello".length() }
                    }''')],
        // Length on a String parameter is non-negative (axiom 1) — even with no other constraint,
        // s.length() >= 0 holds. This is the load-bearing axiom for length-based reasoning.
        [group: 'P46c string axioms', name: 'string length non-negativity', ok: true,
         src: tc('''class C {
                        @Requires({ s != null })
                        @Ensures({ result >= 0 })
                        static int f(String s) { s.length() }
                    }''')],
        // s.isEmpty() lowered to length(s) == 0 — both expressions resolve to the same term.
        [group: 'P46b string length', name: 'isEmpty <=> length == 0', ok: true,
         src: tc('''class C {
                        @Requires({ s != null && s.isEmpty() })
                        @Ensures({ result == 0 })
                        static int f(String s) { s.length() }
                    }''')],
        // Length-prefix bound (axiom 2): s.startsWith("hello") implies s.length() >= 5.
        [group: 'P46c string axioms', name: 'startsWith implies length bound', ok: true,
         src: tc('''class C {
                        @Requires({ s != null && s.startsWith("hello") })
                        @Ensures({ result >= 5 })
                        static int f(String s) { s.length() }
                    }''')],
        // Headline application of axiom 2: a string of length 4 *cannot* start with "hello" —
        // the verifier proves the negation outright, not just leaves it open.
        [group: 'P46c string axioms', name: 'too-short string never starts with longer prefix', ok: true,
         src: tc('''class C {
                        @Requires({ s != null && s.length() == 4 })
                        @Ensures({ !result })
                        static boolean f(String s) { s.startsWith("hello") }
                    }''')],
        // Soundness: claiming the opposite (a 4-char string starts with "hello") is refutable —
        // the axiom rules it out, so trying to ensure it succeeds is unverifiable.
        [group: 'P46c string axioms', name: 'too-short string cannot be claimed to start with longer prefix',
         expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Requires({ s != null && s.length() == 4 })
                        @Ensures({ result })
                        static boolean f(String s) { s.startsWith("hello") }
                    }''')],
        // Length-suffix bound (axiom 3): mirror of axiom 2 for endsWith.
        [group: 'P46c string axioms', name: 'endsWith implies length bound', ok: true,
         src: tc('''class C {
                        @Requires({ s != null && s.endsWith("world") })
                        @Ensures({ result >= 5 })
                        static int f(String s) { s.length() }
                    }''')],

        // ---------- Phase 46e: charAt with per-position literal pinning + bounds ----------
        // Literal pinning: "hello".charAt(0) folds to 104 ('h' codepoint) via the mint pin. The
        // explicit (int) cast bridges Groovy's char-vs-int type distinction at the return.
        [group: 'P46e charAt', name: 'literal charAt at position 0', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 104 })
                        static int f() { (int) "hello".charAt(0) }
                    }''')],
        [group: 'P46e charAt', name: 'literal charAt at last position', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 111 })
                        static int f() { (int) "hello".charAt(4) }
                    }''')],
        // Wrong codepoint refutes — per-position pinning is exact.
        [group: 'P46e charAt', name: 'wrong literal charAt refutes',
         expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Ensures({ result == 65 })
                        static int f() { (int) "hello".charAt(0) }
                    }''')],
        // Bounds check: an out-of-bounds charAt index refutes with the IndexBounds diagnostic.
        [group: 'P46e charAt', name: 'out-of-bounds charAt refutes',
         expect: 'Possible IndexOutOfBoundsException',
         src: tc('''class C {
                        @Requires({ s != null && s.length() > 0 })
                        static int f(String s) { (int) s.charAt(s.length()) }
                    }''')],
        // Bounds check: a guarded charAt verifies.
        [group: 'P46e charAt', name: 'guarded charAt verifies', ok: true,
         src: tc('''class C {
                        @Requires({ s != null && s.length() > 0 })
                        static int f(String s) { (int) s.charAt(0) }
                    }''')],
        // Symbolic charAt as a sentinel — equality through the uninterpreted function.
        [group: 'P46e charAt', name: 'charAt sentinel echoes assumption', ok: true,
         src: tc('''class C {
                        @Requires({ s != null && s.length() > 0 && s.charAt(0) == 65 })
                        @Ensures({ result == 65 })
                        static int f(String s) { (int) s.charAt(0) }
                    }''')],

        // ---------- Phase 47: Z3 string theory adoption ----------
        // The big-ticket structural fact: charAt across a prefix relationship. With the
        // uninterpreted approach (Phase 46a-e), startsWith was opaque to charAt — there was
        // no axiom relating them. With Z3's native seq theory, prefix-of structurally implies
        // that every position before the prefix length has equal characters in both strings.
        // This is the headline win of the theory adoption.
        [group: 'P47 string theory', name: 'prefixof structurally implies equal chars', ok: true,
         src: tc('''class C {
                        @Requires({ s != null && t != null && s.startsWith(t) &&
                                    t.length() > 0 })
                        @Ensures({ result == 1 })
                        static int f(String s, String t) {
                            s.charAt(0) == t.charAt(0) ? 1 : 0
                        }
                    }''')],
        // Distinct literals: theory-distinct via seq theory, no pairwise cascade needed.
        [group: 'P47 string theory', name: 'distinct literals are theory-distinct', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { "foo" != "bar" ? 1 : 0 }
                    }''')],
        // Concatenation: literal + literal folds, and length composes.
        [group: 'P47 string theory', name: 'literal concat folds', ok: true,
         src: tc('''class C {
                        @Ensures({ result == "foobar" })
                        static String f() { "foo" + "bar" }
                    }''')],
        [group: 'P47 string theory', name: 'concat method form folds', ok: true,
         src: tc('''class C {
                        @Ensures({ result == "foobar" })
                        static String f() { "foo".concat("bar") }
                    }''')],
        // Concat length composes structurally: |s + "x"| = |s| + 1.
        [group: 'P47 string theory', name: 'concat length composes', ok: true,
         src: tc('''class C {
                        @Requires({ s != null })
                        @Ensures({ result == s.length() + 1 })
                        static int f(String s) { (s + "x").length() }
                    }''')],
        // Substring: literal substring folds.
        [group: 'P47 string theory', name: 'literal substring folds', ok: true,
         src: tc('''class C {
                        @Ensures({ result == "ell" })
                        static String f() { "hello".substring(1, 4) }
                    }''')],
        // Substring single-arg form.
        [group: 'P47 string theory', name: 'literal substring single-arg folds', ok: true,
         src: tc('''class C {
                        @Ensures({ result == "llo" })
                        static String f() { "hello".substring(2) }
                    }''')],
        // Substring bounds: out-of-bounds end refutes.
        [group: 'P47 string theory', name: 'substring out-of-bounds end refutes',
         expect: 'Possible IndexOutOfBoundsException',
         src: tc('''class C {
                        @Requires({ s != null })
                        static String f(String s) { s.substring(0, s.length() + 1) }
                    }''')],
        // Substring bounds: negative begin refutes.
        [group: 'P47 string theory', name: 'substring negative begin refutes',
         expect: 'Possible IndexOutOfBoundsException',
         src: tc('''class C {
                        @Requires({ s != null })
                        static String f(String s) { s.substring(-1, 2) }
                    }''')],
        // Substring length identity: |substring(s, a, b)| = b - a when in bounds.
        [group: 'P47 string theory', name: 'substring length identity', ok: true,
         src: tc('''class C {
                        @Requires({ s != null && s.length() >= 5 })
                        @Ensures({ result == 3 })
                        static int f(String s) { s.substring(1, 4).length() }
                    }''')],
        // Cross-string: two strings sharing a prefix have equal chars there.
        [group: 'P47 string theory', name: 'prefix sharing gives charAt equality at i==1', ok: true,
         src: tc('''class C {
                        @Requires({ s != null && t != null && s.startsWith("ab") && t.startsWith("ab") })
                        @Ensures({ result == 1 })
                        static int f(String s, String t) {
                            s.charAt(1) == t.charAt(1) ? 1 : 0
                        }
                    }''')],
        // Refute: structurally-equal-at-prefix doesn't imply equal at a position past the prefix.
        [group: 'P47 string theory', name: 'past-prefix charAt not structurally tied',
         expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Requires({ s != null && t != null && s.startsWith("ab") && t.startsWith("ab")
                                    && s.length() > 2 && t.length() > 2 })
                        @Ensures({ result == 1 })
                        static int f(String s, String t) {
                            s.charAt(2) == t.charAt(2) ? 1 : 0
                        }
                    }''')],
        // s contains t implies t.length() <= s.length() — a theory consequence.
        [group: 'P47 string theory', name: 'contains implies length bound', ok: true,
         src: tc('''class C {
                        @Requires({ s != null && t != null && s.contains(t) })
                        @Ensures({ result >= t.length() })
                        static int f(String s, String t) { s.length() }
                    }''')],

        // ---------- Phase 47b: replace + indexOf ----------
        // Literal replace folds.
        [group: 'P47b replace/indexOf', name: 'literal replace folds (single occurrence)', ok: true,
         src: tc('''class C {
                        @Ensures({ result == "hePlo" })
                        static String f() { "hello".replace("l", "P") }
                    }''')],
        // Replace identity: replacing a non-occurring substring is a no-op (requires a
        // {@code !contains} precondition so the verifier knows the substring isn't present).
        [group: 'P47b replace/indexOf', name: 'replace non-occurring is no-op', ok: true,
         src: tc('''class C {
                        @Requires({ s != null && !s.contains("XYZQ") })
                        @Ensures({ result == s })
                        static String f(String s) { s.replace("XYZQ", "A") }
                    }''')],
        // indexOf literal: position is exact.
        [group: 'P47b replace/indexOf', name: 'literal indexOf folds', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 2 })
                        static int f() { "hello".indexOf("l") }
                    }''')],
        // indexOf with fromIndex: skipping past first occurrence finds the second.
        [group: 'P47b replace/indexOf', name: 'indexOf from-index finds later occurrence', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 3 })
                        static int f() { "hello".indexOf("l", 3) }
                    }''')],
        // indexOf not-found returns -1.
        [group: 'P47b replace/indexOf', name: 'indexOf returns -1 when absent', ok: true,
         src: tc('''class C {
                        @Ensures({ result == -1 })
                        static int f() { "hello".indexOf("X") }
                    }''')],
        // Cross-string indexOf bound: indexOf result is always >= -1.
        [group: 'P47b replace/indexOf', name: 'indexOf result is always >= -1', ok: true,
         src: tc('''class C {
                        @Requires({ s != null && t != null })
                        @Ensures({ result >= -1 })
                        static int f(String s, String t) { s.indexOf(t) }
                    }''')],

        // ---------- Phase 47c: matches with regex parser ----------
        // Literal-only regex: matches iff string equals the literal.
        [group: 'P47c regex', name: 'literal regex matches exact string', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { "abc".matches("abc") ? 1 : 0 }
                    }''')],
        [group: 'P47c regex', name: 'literal regex refutes wrong string',
         expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { "abc".matches("xyz") ? 1 : 0 }
                    }''')],
        // {@code .} matches any single character.
        [group: 'P47c regex', name: 'any-char dot matches single position', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { "abc".matches("a.c") ? 1 : 0 }
                    }''')],
        // Quantifier: {@code a*} matches zero or more 'a's.
        [group: 'P47c regex', name: 'star quantifier matches zero occurrences', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { "".matches("a*") ? 1 : 0 }
                    }''')],
        [group: 'P47c regex', name: 'plus quantifier requires one occurrence', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 0 })
                        static int f() { "".matches("a+") ? 1 : 0 }
                    }''')],
        // Character range: digits.
        [group: 'P47c regex', name: 'digit range matches numeric string', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { "123".matches("[0-9]+") ? 1 : 0 }
                    }''')],
        [group: 'P47c regex', name: 'digit range rejects alphabetic string', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 0 })
                        static int f() { "abc".matches("[0-9]+") ? 1 : 0 }
                    }''')],
        // Character set + range: alphanumeric.
        [group: 'P47c regex', name: 'alphanumeric class matches mixed', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { "abc123".matches("[a-zA-Z0-9]+") ? 1 : 0 }
                    }''')],
        // Alternation.
        [group: 'P47c regex', name: 'alternation matches either branch', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { "yes".matches("yes|no") ? 1 : 0 }
                    }''')],
        // Symbolic matches: assumed precondition flows through.
        [group: 'P47c regex', name: 'symbolic matches assumption echoes', ok: true,
         src: tc('''class C {
                        @Requires({ s != null && s.matches("[0-9]+") })
                        @Ensures({ result == 1 })
                        static int f(String s) { s.matches("[0-9]+") ? 1 : 0 }
                    }''')],
        // Unsupported feature: word-boundary {@code \b} isn't a single-character regex; the
        // parser bails out and the verifier emits an honest skip diagnostic.
        [group: 'P47c regex', name: 'unsupported regex feature honest-skips',
         expect: 'Skipped verification of postcondition',
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { "abc".matches("\\\\babc\\\\b") ? 1 : 0 }
                    }''')],

        // ---------- Phase 47d: regex feature expansion ----------
        // Predefined classes: \d, \w, \s.
        [group: 'P47d regex extras', name: '\\\\d+ matches digits', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { "123".matches("\\\\d+") ? 1 : 0 }
                    }''')],
        [group: 'P47d regex extras', name: '\\\\d+ rejects letters',
         expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { "abc".matches("\\\\d+") ? 1 : 0 }
                    }''')],
        [group: 'P47d regex extras', name: '\\\\w+ matches alphanumeric+underscore', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { "abc_123".matches("\\\\w+") ? 1 : 0 }
                    }''')],
        [group: 'P47d regex extras', name: '\\\\s+ matches whitespace', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { "   ".matches("\\\\s+") ? 1 : 0 }
                    }''')],
        // Negated predefined: \D = non-digit.
        [group: 'P47d regex extras', name: '\\\\D+ rejects digits', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 0 })
                        static int f() { "123".matches("\\\\D+") ? 1 : 0 }
                    }''')],
        // Negated character class.
        [group: 'P47d regex extras', name: '[^0-9]+ matches non-digits', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { "abc".matches("[^0-9]+") ? 1 : 0 }
                    }''')],
        [group: 'P47d regex extras', name: '[^0-9]+ rejects digits',
         expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { "123".matches("[^0-9]+") ? 1 : 0 }
                    }''')],
        // Anchors as no-op (matches is whole-string anchored).
        [group: 'P47d regex extras', name: 'anchors are redundant no-ops', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { "abc".matches("^abc\\$") ? 1 : 0 }
                    }''')],
        // Quantified range: a{3} matches exactly three.
        [group: 'P47d regex extras', name: 'a{3} matches exactly three', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { "aaa".matches("a{3}") ? 1 : 0 }
                    }''')],
        [group: 'P47d regex extras', name: 'a{3} rejects two',
         expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { "aa".matches("a{3}") ? 1 : 0 }
                    }''')],
        // {n,m} range.
        [group: 'P47d regex extras', name: 'a{2,4} matches three', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { "aaa".matches("a{2,4}") ? 1 : 0 }
                    }''')],
        [group: 'P47d regex extras', name: 'a{2,4} rejects five',
         expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { "aaaaa".matches("a{2,4}") ? 1 : 0 }
                    }''')],
        // {n,} unbounded.
        [group: 'P47d regex extras', name: 'a{2,} matches three', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { "aaa".matches("a{2,}") ? 1 : 0 }
                    }''')],

        // ---------- Phase 47e: Integer ↔ String conversion ----------
        // Integer.toString folds for non-negative literals (Z3 semantics: int.to.str(n) is
        // the decimal repr for n >= 0).
        [group: 'P47e int/string', name: 'Integer.toString folds for non-negative literal', ok: true,
         src: tc('''class C {
                        @Ensures({ result == "5" })
                        static String f() { Integer.toString(5) }
                    }''')],
        // String.valueOf(int) — same lowering, useful Groovy idiom.
        [group: 'P47e int/string', name: 'String.valueOf(int) folds', ok: true,
         src: tc('''class C {
                        @Ensures({ result == "42" })
                        static String f() { String.valueOf(42) }
                    }''')],
        // Integer.parseInt — round-trips for digit strings.
        [group: 'P47e int/string', name: 'Integer.parseInt folds for digit string', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 123 })
                        static int f() { Integer.parseInt("123") }
                    }''')],
        // Length composes: Integer.toString(n) for n >= 0 has at least one character.
        // (Z3 knows int.to.str(n) is "" iff n < 0, else has len >= 1 digit count.)
        // parseInt of a non-numeric literal now refutes loudly (Phase 54): Java throws
        // NumberFormatException, so the well-formedness obligation flags it (was: silently == -1).
        [group: 'P47e int/string', name: 'parseInt of non-numeric refutes (NumberFormatException)',
         expect: 'NumberFormatException',
         src: tc('''class C {
                        static int f() { Integer.parseInt("abc") }
                    }''')],
        // Refute wrong toString result.
        [group: 'P47e int/string', name: 'Integer.toString wrong-value refutes',
         expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Ensures({ result == "6" })
                        static String f() { Integer.toString(5) }
                    }''')],
        // Symbolic round-trip: parseInt(toString(n)) == n for non-negative n. (Z3 verifies.)
        [group: 'P47e int/string', name: 'parseInt of toString round-trips for non-negative', ok: true,
         src: tc('''class C {
                        @Requires({ n >= 0 })
                        @Ensures({ result == n })
                        static int f(int n) { Integer.parseInt(Integer.toString(n)) }
                    }''')],

        // ---------- Phase 47f: replaceAll + lastIndexOf as uninterpreted ----------
        // replaceAll on a non-occurring substring is a no-op (axiom 1).
        [group: 'P47f weak ops', name: 'replaceAll non-occurring is no-op', ok: true,
         src: tc('''class C {
                        @Requires({ s != null && !s.contains("XYZ") })
                        @Ensures({ result == s })
                        static String f(String s) { s.replaceAll("XYZ", "A") }
                    }''')],
        // replaceAll preserves length when old and new have equal length (axiom 2).
        [group: 'P47f weak ops', name: 'replaceAll preserves length under equal-length swap', ok: true,
         src: tc('''class C {
                        @Requires({ s != null })
                        @Ensures({ result == s.length() })
                        static int f(String s) { s.replaceAll("a", "b").length() }
                    }''')],
        // Soundness: replaceAll content beyond the axioms isn't claimable. Unequal-length
        // replacement doesn't preserve length, so claiming it does refutes.
        [group: 'P47f weak ops', name: 'replaceAll length under unequal-length swap not provable',
         expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Requires({ s != null })
                        @Ensures({ result == s.length() })
                        static int f(String s) { s.replaceAll("a", "bc").length() }
                    }''')],
        // lastIndexOf result is always >= -1.
        [group: 'P47f weak ops', name: 'lastIndexOf >= -1', ok: true,
         src: tc('''class C {
                        @Requires({ s != null && t != null })
                        @Ensures({ result >= -1 })
                        static int f(String s, String t) { s.lastIndexOf(t) }
                    }''')],
        // lastIndexOf is -1 when sub doesn't occur.
        [group: 'P47f weak ops', name: 'lastIndexOf -1 when absent', ok: true,
         src: tc('''class C {
                        @Requires({ s != null && t != null && !s.contains(t) })
                        @Ensures({ result == -1 })
                        static int f(String s, String t) { s.lastIndexOf(t) }
                    }''')],

        // ---------- Phase 47g: case folding (toUpperCase / toLowerCase / equalsIgnoreCase) ----------
        // Literal pinning at mint: "Hello".toUpperCase() folds to "HELLO".
        [group: 'P47g case', name: 'literal toUpperCase folds', ok: true,
         src: tc('''class C {
                        @Ensures({ result == "HELLO" })
                        static String f() { "Hello".toUpperCase() }
                    }''')],
        [group: 'P47g case', name: 'literal toLowerCase folds', ok: true,
         src: tc('''class C {
                        @Ensures({ result == "hello" })
                        static String f() { "HELLO".toLowerCase() }
                    }''')],
        // Wrong-case literal refutes.
        [group: 'P47g case', name: 'wrong-case literal refutes',
         expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Ensures({ result == "hello" })
                        static String f() { "Hello".toUpperCase() }
                    }''')],
        // Length-preservation for literal arguments still folds via the mint pin.
        [group: 'P47g case', name: 'toUpperCase preserves length (literal)', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 5 })
                        static int f() { "hello".toUpperCase().length() }
                    }''')],
        // equalsIgnoreCase via toLower equivalence.
        [group: 'P47g case', name: 'equalsIgnoreCase literals folds', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { "Hello".equalsIgnoreCase("HELLO") ? 1 : 0 }
                    }''')],
        [group: 'P47g case', name: 'equalsIgnoreCase distinguishes content',
         expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { "Hello".equalsIgnoreCase("World") ? 1 : 0 }
                    }''')],
        // Reflexive: s.equalsIgnoreCase(s) is true — toLower applied to the same argument is
        // pointwise-equal regardless of axioms (Z3 sees the two terms as syntactically identical).
        [group: 'P47g case', name: 'equalsIgnoreCase is reflexive', ok: true,
         src: tc('''class C {
                        @Requires({ s != null })
                        @Ensures({ result == 1 })
                        static int f(String s) { s.equalsIgnoreCase(s) ? 1 : 0 }
                    }''')],
        // Symbolic: a precondition that names the lowered form connects to the dispatch
        // by syntactic identity — toLower(s) on the precondition side is the same term as
        // toLower(s) inside the equalsIgnoreCase lowering.
        [group: 'P47g case', name: 'equalsIgnoreCase symmetric to toLower equality', ok: true,
         src: tc('''class C {
                        @Requires({ s != null && t != null && s.toLowerCase() == t.toLowerCase() })
                        @Ensures({ result == 1 })
                        static int f(String s, String t) { s.equalsIgnoreCase(t) ? 1 : 0 }
                    }''')],

        // ---------- Phase 47h: GString interpolation ----------
        // Single String interpolation: "hello $name" with literal name folds to the
        // concrete concatenated string.
        [group: 'P47h gstring', name: 'GString with String literal interpolation folds', ok: true,
         src: tc('''class C {
                        @Ensures({ result == "hello world" })
                        static String f() { String name = "world"; "hello $name" }
                    }''')],
        // Single int interpolation: "x = $x" routes the int through intToString.
        [group: 'P47h gstring', name: 'GString with int literal interpolation folds', ok: true,
         src: tc('''class C {
                        @Ensures({ result == "x = 5" })
                        static String f() { int x = 5; "x = $x" }
                    }''')],
        // Mixed: multiple interpolations, mixed types.
        [group: 'P47h gstring', name: 'GString with multiple interpolations', ok: true,
         src: tc('''class C {
                        @Ensures({ result == "a=1, b=hi" })
                        static String f() {
                            int a = 1
                            String b = "hi"
                            "a=$a, b=$b"
                        }
                    }''')],
        // Length of a GString — sums static parts with int.toString length.
        [group: 'P47h gstring', name: 'GString length composes', ok: true,
         src: tc('''class C {
                        @Requires({ n >= 0 })
                        @Ensures({ result == 4 + Integer.toString(n).length() })
                        static int f(int n) { "n = $n".length() }
                    }''')],
        // Symbolic String parameter: "hello $name" length is "hello ".length + name.length.
        [group: 'P47h gstring', name: 'GString length with String param', ok: true,
         src: tc('''class C {
                        @Requires({ name != null })
                        @Ensures({ result == 6 + name.length() })
                        static int f(String name) { "hello $name".length() }
                    }''')],
        // GString as comparison RHS: matches a String literal at runtime.
        [group: 'P47h gstring', name: 'GString equals literal String', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() {
                            String name = "Alice"
                            "hi $name" == "hi Alice" ? 1 : 0
                        }
                    }''')],
        // Refute: wrong interpolated value.
        [group: 'P47h gstring', name: 'GString refutes wrong interpolation',
         expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Ensures({ result == "hello Bob" })
                        static String f() { String name = "Alice"; "hello $name" }
                    }''')],
        // GString with ${...} block-form interpolation (computed expression).
        [group: 'P47h gstring', name: 'GString with block-form expression', ok: true,
         src: tc('''class C {
                        @Ensures({ result == "sum=3" })
                        static String f() { int a = 1; int b = 2; "sum=${a + b}" }
                    }''')],
        // GString chained with .startsWith — the result is a String-typed receiver.
        [group: 'P47h gstring', name: 'GString routes through string-receiver dispatch', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() {
                            String name = "Alice"
                            "hi $name".startsWith("hi") ? 1 : 0
                        }
                    }''')],
        // Showcase: idLength under a prefix-constrained input. Verifies via the seq theory's
        // structural fact (startsWith → length(prefix) <= length(s)) composed with substring's
        // length identity.
        [group: 'P47h gstring', name: 'showcase: idLength via startsWith + substring', ok: true,
         src: tc('''class C {
                        @Requires({ s != null && s.startsWith("user:") })
                        @Ensures({ result == s.length() - 5 })
                        static int idLength(String s) { s.substring(5).length() }
                    }''')],
        // Showcase 2: GString + regex + structural concat facts. Verifies via four
        // theory consequences in one method: regex membership preserved through the
        // precondition, GString folds to chained str.++, prefix-of-concat with the literal
        // first operand, suffix-of-concat with the second operand.
        [group: 'P47h gstring', name: 'showcase: greet via gstring + regex + concat facts', ok: true,
         src: tc('''class C {
                        @Requires({ name != null && name.matches("[a-zA-Z]+") })
                        @Ensures({ result.startsWith("Hi, ") && result.endsWith(name) })
                        static String greet(String name) { "Hi, $name" }
                    }''')],

        // ---------- Phase 49 (Slice A): early-return in loop prefix ----------
        // The headline shape: an early-return guard before the loop. The prefix exit's
        // @Ensures verifies on its own path (assumes the guard); the loop's establishment /
        // use checks fire on the no-exit path (assumes ¬guard).
        [group: 'P49 prefix-exits', name: 'single prefix early-return verifies', ok: true,
         src: tc('''class C {
                        @Requires({ n >= 0 })
                        @Ensures({ result >= 0 })
                        static int f(int n) {
                            if (n == 0) return 7
                            int i = 0
                            @Invariant({ 0 <= i && i <= n })
                            @Decreases({ n - i })
                            while (i < n) { i = i + 1 }
                            return i
                        }
                    }''')],
        // Stacked early-returns: each is verified independently with prior guards negated.
        [group: 'P49 prefix-exits', name: 'multiple stacked prefix early-returns', ok: true,
         src: tc('''class C {
                        @Requires({ n >= 0 })
                        @Ensures({ result >= 0 })
                        static int f(int n) {
                            if (n == 0) return 1
                            if (n == 1) return 2
                            int i = 0
                            @Invariant({ 0 <= i && i <= n })
                            @Decreases({ n - i })
                            while (i < n) { i = i + 1 }
                            return i
                        }
                    }''')],
        // Soundness: an early-return whose value violates the postcondition refutes.
        [group: 'P49 prefix-exits', name: 'early-return postcondition violation refutes',
         expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Requires({ n >= 0 })
                        @Ensures({ result >= 0 })
                        static int f(int n) {
                            if (n == 0) return -1
                            int i = 0
                            @Invariant({ 0 <= i && i <= n })
                            @Decreases({ n - i })
                            while (i < n) { i = i + 1 }
                            return i
                        }
                    }''')],
        // Loop establishment USES the negated guard: the invariant after the prefix needs to
        // hold on the "no early-exit" path. Here the invariant assumes n >= 1, which only
        // holds when the early-exit didn't fire (n != 0).
        [group: 'P49 prefix-exits', name: 'loop invariant uses ¬prefix-guard', ok: true,
         src: tc('''class C {
                        @Requires({ n >= 0 })
                        @Ensures({ result >= 1 })
                        static int f(int n) {
                            if (n == 0) return 1
                            int i = 1
                            @Invariant({ 1 <= i && i <= n })
                            @Decreases({ n - i })
                            while (i < n) { i = i + 1 }
                            return i
                        }
                    }''')],
        // Prior statements + early-return: the prior assignment runs, then the exit's @Ensures
        // is verified with that state.
        [group: 'P49 prefix-exits', name: 'prior assignment + early-return', ok: true,
         src: tc('''class C {
                        @Requires({ n >= 0 })
                        @Ensures({ result >= 0 })
                        static int f(int n) {
                            int x = n + 1
                            if (x == 1) return 0
                            int i = 0
                            @Invariant({ 0 <= i && i <= n })
                            @Decreases({ n - i })
                            while (i < n) { i = i + 1 }
                            return i
                        }
                    }''')],

        // ---------- Phase 49b (Slice B): early-return INSIDE a loop body ----------
        // The in-body return path: its @Ensures verifies under invariant ∧ guard ∧
        // ¬prior-in-body-guards ∧ this-guard, with result bound to the exit value.
        // The loop's preservation / progress fire on the "no exit fired" path
        // (¬each-in-body-guard assumed during the body walk).
        [group: 'P49b in-body exits', name: 'single in-body early-return verifies', ok: true,
         src: tc('''class C {
                        @Requires({ n >= 0 })
                        @Ensures({ result >= 0 })
                        static int f(int n) {
                            int i = 0
                            @Invariant({ 0 <= i && i <= n })
                            @Decreases({ n - i })
                            while (i < n) {
                                if (i == 5) return 42
                                i = i + 1
                            }
                            return i
                        }
                    }''')],
        // Soundness: an in-body return whose value violates the postcondition refutes.
        [group: 'P49b in-body exits', name: 'in-body return postcondition violation refutes',
         expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Requires({ n >= 0 })
                        @Ensures({ result >= 0 })
                        static int f(int n) {
                            int i = 0
                            @Invariant({ 0 <= i && i <= n })
                            @Decreases({ n - i })
                            while (i < n) {
                                if (i == 5) return -1
                                i = i + 1
                            }
                            return i
                        }
                    }''')],
        // Preservation under in-body exit: the body's normal-continuation path keeps the
        // invariant. The {@code i++} still happens on the no-exit path.
        [group: 'P49b in-body exits', name: 'preservation holds on no-exit body path', ok: true,
         src: tc('''class C {
                        @Requires({ xs != null })
                        @Ensures({ result >= -1 })
                        static int firstNegativeIndex(List<Integer> xs) {
                            int i = 0
                            @Invariant({ 0 <= i && i <= xs.size() })
                            @Decreases({ xs.size() - i })
                            while (i < xs.size()) {
                                if (xs[i] < 0) return i
                                i = i + 1
                            }
                            return -1
                        }
                    }''')],
        // Multiple in-body exits: each verified independently; ¬prior-guards assumed for later ones.
        [group: 'P49b in-body exits', name: 'multiple stacked in-body returns', ok: true,
         src: tc('''class C {
                        @Requires({ n >= 0 })
                        @Ensures({ result >= 0 })
                        static int f(int n) {
                            int i = 0
                            @Invariant({ 0 <= i && i <= n })
                            @Decreases({ n - i })
                            while (i < n) {
                                if (i == 3) return 100
                                if (i == 7) return 200
                                i = i + 1
                            }
                            return i
                        }
                    }''')],

        // ---------- HumanEval port — is_prime (Verus task 039) ----------
        // The Verus original combines three pieces this checker previously couldn't do:
        // (1) the {@code while (i * i <= num)} NIA loop bound — closed by Phase 48;
        // (2) prefix early-returns ({@code if (num <= 1) return 0;} etc.) — closed by Phase 49a;
        // (3) the in-body early-return ({@code if (num % i == 0) return 0;} inside the loop)
        // — closed by Phase 49b. The port is now structurally identical to the Verus source.
        [group: 'HumanEval port', name: 'is_prime (Verus 039) — full Verus-shape port', ok: true,
         src: tc('''class C {
                        @Requires({ num >= 0 })
                        static int isPrime(int num) {
                            if (num <= 1) return 0
                            if (num <= 3) return 1
                            if (num % 2 == 0 || num % 3 == 0) return 0
                            int i = 5
                            @Invariant({ i >= 5 })
                            while (i * i <= num) {
                                if (num % i == 0 || num % (i + 2) == 0) return 0
                                i = i + 6
                            }
                            return 1
                        }
                    }''')],

        // ---------- HumanEval port — get_positive (Verus task 030, stronger spec) ----------
        // The Verus original has no postcondition. The first port (above) added the natural
        // size-bound spec. This stronger port matches what a Verus user would naturally write
        // *if they wrote a spec*: every result element is positive. Requires a per-element
        // bounded-universal invariant via {@code Forall.range} (the verus-style explicit form
        // the encoder's quantifier path understands); the GDK {@code (0..<n).every} sugar
        // doesn't yet route through that path for a mutating local's size.
        [group: 'HumanEval port', name: 'get_positive (Verus 030, stronger): every result element is positive', ok: true,
         src: tc('''class C {
                        @Requires({ xs != null })
                        @Ensures({ Forall.range(0, result.size(), { int k -> result[k] > 0 }) })
                        static List<Integer> getPositive(List<Integer> xs) {
                            List<Integer> positive = []
                            int i = 0
                            @Invariant({ positive != null && 0 <= i && i <= xs.size() &&
                                         Forall.range(0, positive.size(), { int k -> positive[k] > 0 }) })
                            @Decreases({ xs.size() - i })
                            while (i < xs.size()) {
                                int x = xs[i]
                                if (x > 0) {
                                    positive.add(x)
                                }
                                i = i + 1
                            }
                            return positive
                        }
                    }''')],

        // ---------- HumanEval port — filter_by_prefix (Verus 029, stronger spec) ----------
        // The Verus original's postcondition is {@code forall i. strings.contains(result[i])
        // && result[i].starts_with(prefix)}. Phase 47 native string theory + Phase 46d in-loop
        // path facts + the bounded universal invariant make this reachable. Each accumulated
        // element provably satisfies startsWith(prefix); the membership clause
        // ({@code strings.contains(result[i])}) lifts via the existing list-contains existential.
        [group: 'HumanEval port', name: 'filter_by_prefix (Verus 029, stronger): every result starts with prefix', ok: true,
         src: tc('''class C {
                        @Requires({ xs != null && prefix != null })
                        @Ensures({ Forall.range(0, result.size(), { int k -> result[k].startsWith(prefix) }) })
                        static List<String> filterByPrefix(List<String> xs, String prefix) {
                            List<String> result = []
                            int i = 0
                            @Invariant({ result != null && 0 <= i && i <= xs.size() &&
                                         Forall.range(0, result.size(), { int k -> result[k].startsWith(prefix) }) })
                            @Decreases({ xs.size() - i })
                            while (i < xs.size()) {
                                if (xs[i] != null && xs[i].startsWith(prefix)) {
                                    result.add(xs[i])
                                }
                                i = i + 1
                            }
                            return result
                        }
                    }''')],

        // ---------- Phase 48: NIA — variable multiplication + div/mod ----------
        // Commutativity is a Z3 theory consequence — no axiom needed.
        [group: 'P48 NIA', name: 'multiplication commutativity', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f(int a, int b) { (a * b == b * a) ? 1 : 0 }
                    }''')],
        // Sign reasoning: positive × positive = positive.
        [group: 'P48 NIA', name: 'positive product is positive', ok: true,
         src: tc('''class C {
                        @Requires({ a > 0 && b > 0 })
                        @Ensures({ result > 0 })
                        static int f(int a, int b) { a * b }
                    }''')],
        // Squaring is non-negative — Z3 NIA handles this.
        [group: 'P48 NIA', name: 'square is non-negative', ok: true,
         src: tc('''class C {
                        @Ensures({ result >= 0 })
                        static int f(int i) { i * i }
                    }''')],
        // Bounded squaring: i in [0, 10] gives i*i in [0, 100].
        [group: 'P48 NIA', name: 'bounded square stays bounded', ok: true,
         src: tc('''class C {
                        @Requires({ 0 <= i && i <= 10 })
                        @Ensures({ result <= 100 })
                        static int f(int i) { i * i }
                    }''')],
        // Refute: unbounded square can exceed any specific bound.
        [group: 'P48 NIA', name: 'unbounded square can exceed 100',
         expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Ensures({ result <= 100 })
                        static int f(int i) { i * i }
                    }''')],
        // Two-variable multiplication with bounds.
        [group: 'P48 NIA', name: 'bounded variable product', ok: true,
         src: tc('''class C {
                        @Requires({ 0 <= a && a < 100 && 0 <= b && b < 100 })
                        @Ensures({ result < 10000 })
                        static int f(int a, int b) { a * b }
                    }''')],
        // Division by variable. Groovy's {@code /} on ints promotes to BigDecimal, so the
        // test casts back to int — same dance the existing Phase 8a tests use. The verifier
        // collects {@code DivideSite} for the {@code b != 0} check; the value goes through
        // {@code intDiv}.
        [group: 'P48 NIA', name: 'division floor behaviour', ok: true,
         src: tc('''class C {
                        @Requires({ b > 0 && a >= 0 })
                        @Ensures({ result * b <= a })
                        static int f(int a, int b) { (int)(a / b) }
                    }''')],
        // Modulo bound: a % b is in [0, b) for non-negative a and positive b.
        [group: 'P48 NIA', name: 'modulo result in [0, b)', ok: true,
         src: tc('''class C {
                        @Requires({ a >= 0 && b > 0 })
                        @Ensures({ result >= 0 && result < b })
                        static int f(int a, int b) { a % b }
                    }''')],
        // Division identity, Groovy-faithful: a.intdiv(b) * b + (a % b) == a, for ALL b != 0
        // (intdiv truncates, % is the sign-of-dividend remainder — the pair Groovy guarantees).
        // NB: the BigDecimal form `(a / b) * b + a % b` does NOT equal a in Groovy
        // ((5/2)*2 + 5%2 == 6), so the identity must use intdiv, not `/`.
        [group: 'P48 NIA', name: 'division identity holds', ok: true,
         src: tc('''class C {
                        @Requires({ b != 0 })
                        @Ensures({ result == a })
                        static int f(int a, int b) { a.intdiv(b) * b + (a % b) }
                    }''')],
        // Soundness: division by zero is still caught — implicit DivideSite obligation.
        [group: 'P48 NIA', name: 'division by zero refutes',
         expect: 'Possible ArithmeticException: Division by zero',
         src: tc('''class C {
                        static int f(int a, int b) { (int)(a / b) }
                    }''')],
        // Even-number predicate via modulo: n % 2 == 0 holds for the even branch.
        [group: 'P48 NIA', name: 'even predicate via modulo', ok: true,
         src: tc('''class C {
                        @Requires({ n >= 0 && n % 2 == 0 })
                        @Ensures({ result == 1 })
                        static int f(int n) { (n % 2 == 0) ? 1 : 0 }
                    }''')],

        // ---------- Phase 50: Groovy-faithful division / modulo semantics ----------
        // `%` operator is the sign-of-dividend remainder: -5 % 2 == -1 (NOT the Euclidean +1).
        [group: 'P50 groovy div/mod', name: 'percent is sign-of-dividend remainder', ok: true,
         src: tc('''class C {
                        @Requires({ a == -5 })
                        @Ensures({ result == -1 })
                        static int f(int a) { a % 2 }
                    }''')],
        // Soundness regression guard: the old Euclidean `mkMod` wrongly "verified" this
        // (`a % 3 >= 0`); with sign-of-dividend semantics it correctly refutes (a = -7 → -1).
        [group: 'P50 groovy div/mod', name: 'negative modulo can be negative (refutes)',
         expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Ensures({ result >= 0 })
                        static int f(int a) { a % 3 }
                    }''')],
        // `intdiv()` is truncate-toward-zero integer division.
        [group: 'P50 groovy div/mod', name: 'intdiv truncates toward zero', ok: true,
         src: tc('''class C {
                        @Requires({ a == -7 })
                        @Ensures({ result == -3 })
                        static int f(int a) { a.intdiv(2) }
                    }''')],
        // `(int)(a / b)` is the other truncating-int-div idiom (BigDecimal division then narrow).
        [group: 'P50 groovy div/mod', name: 'int-cast of division truncates', ok: true,
         src: tc('''class C {
                        @Requires({ a == 5 && b == 2 })
                        @Ensures({ result == 2 })
                        static int f(int a, int b) { (int)(a / b) }
                    }''')],
        // `.mod()` is BigInteger.mod — always non-negative (differs from `%` / `.remainder()`).
        [group: 'P50 groovy div/mod', name: 'mod is non-negative', ok: true,
         src: tc('''class C {
                        @Requires({ a == -5 })
                        @Ensures({ result == 1 })
                        static int f(int a) { a.mod(2) }
                    }''')],
        // `.remainder()` matches the `%` operator (sign of dividend).
        [group: 'P50 groovy div/mod', name: 'remainder is sign-of-dividend', ok: true,
         src: tc('''class C {
                        @Requires({ a == -5 })
                        @Ensures({ result == -1 })
                        static int f(int a) { a.remainder(2) }
                    }''')],
        // `.mod()` throws unless the modulus is positive — a Groovy-specific implicit obligation.
        [group: 'P50 groovy div/mod', name: 'mod requires positive modulus (refutes)',
         expect: 'modulus not positive',
         src: tc('class C { static int f(int a, int b) { a.mod(b) } }')],
        [group: 'P50 groovy div/mod', name: 'mod with positive divisor verified', ok: true,
         src: tc('''class C {
                        @Requires({ b > 0 })
                        @Ensures({ result >= 0 })
                        static int f(int a, int b) { a.mod(b) }
                    }''')],
        // The bare `/` operator yields a BigDecimal — outside the integer fragment, skipped loudly.
        [group: 'P50 groovy div/mod', name: 'bare division is BigDecimal (skipped)',
         expect: 'Skipped verification of postcondition',
         src: tc('''class C {
                        @Ensures({ result == 2 })
                        static int f(int a, int b) { a / b }
                    }''')],
        // intdiv divide-by-zero is still caught.
        [group: 'P50 groovy div/mod', name: 'intdiv by zero refutes',
         expect: 'Division by zero',
         src: tc('class C { static int f(int a, int b) { a.intdiv(b) } }')],

        // ---------- Phase 51: numeric sum aggregation over an Int list (xs[lo..<hi].sum()) ----------
        [group: 'P51 sum', name: 'range sum unfolds to elements', ok: true,
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() >= 2 })
                        @Ensures({ xs[0..<2].sum() == xs[0] + xs[1] })
                        static void f(List<Integer> xs) { }
                    }''')],
        [group: 'P51 sum', name: 'prefix-extension step law holds', ok: true,
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() >= 2 })
                        @Ensures({ xs[0..<2].sum() == xs[0..<1].sum() + xs[1] })
                        static void f(List<Integer> xs) { }
                    }''')],
        // The canonical loop-invariant proof: a running total equals the prefix sum at each step,
        // so the returned value equals the whole-list sum. Non-empty per the GDK `[].sum()==null` limit.
        [group: 'P51 sum', name: 'running total equals list sum', ok: true,
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() > 0 })
                        @Ensures({ result == xs.sum() })
                        static int total(List<Integer> xs) {
                            int s = xs[0]
                            int i = 1
                            @Invariant({ 1 <= i && i <= xs.size() && s == xs[0..<i].sum() })
                            @Decreases({ xs.size() - i })
                            while (i < xs.size()) {
                                s += xs[i]
                                i++
                            }
                            return s
                        }
                    }''')],
        // Duck-typed String `sum()` IS concatenation (`['a','b','c'].sum() == 'abc'`): a String-element
        // list lowers to the `strConcat$` monoid analogue, and a range sum unfolds to the element concat.
        [group: 'P51 sum', name: 'string-list range sum concatenates', ok: true,
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() >= 2 })
                        @Ensures({ xs[0..<2].sum() == xs[0] + xs[1] })
                        static void f(List<String> xs) { }
                    }''')],
        // The canonical loop-invariant proof, String monoid: a running concatenation equals the
        // whole-list `sum()` (`s == xs[0..<i].sum()` carried across the loop with `str.++`).
        [group: 'P51 sum', name: 'running concatenation equals list sum', ok: true,
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() > 0 })
                        @Ensures({ result == xs.sum() })
                        static String concatAll(List<String> xs) {
                            String s = xs[0]
                            int i = 1
                            @Invariant({ 1 <= i && i <= xs.size() && s == xs[0..<i].sum() })
                            @Decreases({ xs.size() - i })
                            while (i < xs.size()) {
                                s = s + xs[i]
                                i = i + 1
                            }
                            return s
                        }
                    }''')],

        // ---------- HumanEval 3 (below_zero): running balance ever negative ----------
        // The FULL biconditional spec — result ⟺ some prefix sum is negative — verifies: the early
        // return witnesses the existential (`any`), and the invariant "no prefix negative so far"
        // (`every`) carries the converse to the `return false` path. Uses `sum(0)` (runtime-safe: 0
        // for the empty prefix, vs `[].sum() == null`) and an `(int)` cast — but NOT for the
        // generics-erasure reason the others had: the seeded GDK `sum(Iterable, initialValue)` overload is
        // declared to return `Object` by signature (unlike the bare `sum()`), so the `< 0` comparison needs
        // it even with GROOVY-12071's restored closure generics. The proof logic is groovy-verify's sum
        // aggregation + bounded ∀/∃.
        [group: 'P52 below_zero', name: 'below_zero full biconditional spec', ok: true,
         src: tc('''class C {
                        @Requires({ operations != null })
                        @Ensures({ result == (0..operations.size()).any { ((int) operations[0..<it].sum(0)) < 0 } })
                        static boolean belowZero(List<Integer> operations) {
                            int s = 0
                            int i = 0
                            @Invariant({ 0 <= i && i <= operations.size() &&
                                         s == operations[0..<i].sum(0) &&
                                         (0..i).every { ((int) operations[0..<it].sum(0)) >= 0 } })
                            @Decreases({ operations.size() - i })
                            while (i < operations.size()) {
                                s = s + operations[i]
                                if (s < 0) return true
                                i = i + 1
                            }
                            return false
                        }
                    }''')],

        // ---------- Phase 53: product aggregation via the inject(1){a,x->a*x} fold ----------
        // A literal-bounded range product unfolds via the step axiom to the element product.
        [group: 'P53 product', name: 'range product unfolds to elements', ok: true,
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() >= 2 })
                        @Ensures({ xs[0..<2].inject(1) { a, x -> a * x } == xs[0] * xs[1] })
                        static void f(List<Integer> xs) { }
                    }''')],
        // The canonical loop-invariant proof: a running product equals the prefix product at each
        // step, so the returned value equals the whole-list product (the inject fold).
        [group: 'P53 product', name: 'running product equals list product', ok: true,
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() > 0 })
                        @Ensures({ result == xs.inject(1) { a, x -> a * x } })
                        static int product(List<Integer> xs) {
                            int p = xs[0]
                            int i = 1
                            @Invariant({ 1 <= i && i <= xs.size() &&
                                         p == xs[0..<i].inject(1) { a, x -> a * x } })
                            @Decreases({ xs.size() - i })
                            while (i < xs.size()) {
                                p = p * xs[i]
                                i = i + 1
                            }
                            return p
                        }
                    }''')],
        // inject(0){a,x->a+x} is recognised as a sum fold too (same machinery, `+` instead of `*`).
        [group: 'P53 product', name: 'inject sum fold unfolds', ok: true,
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() >= 2 })
                        @Ensures({ xs[0..<2].inject(0) { a, x -> a + x } == xs[0] + xs[1] })
                        static void f(List<Integer> xs) { }
                    }''')],
        // HumanEval 8 (sum_product) shape: compute the sum AND the product in one loop, each proven
        // against its aggregate. (This variant returns `s + p` to expose both in one int; the faithful
        // `return [sum, product]` version is in the P78 group, now that list returns are modelled.)
        [group: 'P53 product', name: 'sum_product: both aggregations in one loop', ok: true,
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() > 0 })
                        @Ensures({ result == xs.sum() + xs.inject(1) { a, x -> a * x } })
                        static int sumPlusProduct(List<Integer> xs) {
                            int s = xs[0]
                            int p = xs[0]
                            int i = 1
                            @Invariant({ 1 <= i && i <= xs.size() &&
                                         s == xs[0..<i].sum() &&
                                         p == xs[0..<i].inject(1) { a, x -> a * x } })
                            @Decreases({ xs.size() - i })
                            while (i < xs.size()) {
                                s = s + xs[i]
                                p = p * xs[i]
                                i = i + 1
                            }
                            return s + p
                        }
                    }''')],

        // ---------- Phase 83: maps as named tuples (m.key / m['key'] on a returned map literal) ----------
        // A returned map literal binds `result` as a map factory (Phase 78); the property form `result.key`
        // folds to the value at that key (subscript `result['key']` already worked).
        [group: 'P83 named-map', name: 'map return: result.key property access', ok: true,
         src: tc('''class C {
                        @Ensures({ result.sum == 3 && result.product == 2 })
                        static Map<String, Integer> m() { [sum: 3, product: 2] }
                    }''')],
        [group: 'P83 named-map', name: 'map return: subscript form', ok: true,
         src: tc('''class C {
                        @Ensures({ result['sum'] == 3 && result['product'] == 2 })
                        static Map<String, Integer> m() { [sum: 3, product: 2] }
                    }''')],
        [group: 'P83 named-map', name: 'map return: wrong value refutes', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Ensures({ result.sum == 99 })
                        static Map<String, Integer> m() { [sum: 3, product: 2] }
                    }''')],
        // The faithful HumanEval 008 (sum_product) as a NAMED-tuple map — the user's example.
        [group: 'P83 named-map', name: 'sum_product as a named-tuple map', ok: true,
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() > 0 })
                        @Ensures({ result.sum == xs.sum() && result.product == xs.inject(1) { a, x -> a * x } })
                        static Map<String, Integer> sumProduct(List<Integer> xs) {
                            int s = xs[0]
                            int p = xs[0]
                            int i = 1
                            @Invariant({ 1 <= i && i <= xs.size() &&
                                         s == xs[0..<i].sum() &&
                                         p == xs[0..<i].inject(1) { a, x -> a * x } })
                            @Decreases({ xs.size() - i })
                            while (i < xs.size()) {
                                s = s + xs[i]
                                p = p * xs[i]
                                i = i + 1
                            }
                            return [sum: s, product: p]
                        }
                    }''')],

        // ---------- Phase 84: map PARAMETERS with .key access ----------
        // `m.key` (property) on a map param routes to the value array — `m.sum` ≡ `m['sum']`. The caller's
        // map, so each key is a fresh entity in the value sort (consistent: same key → same value).
        [group: 'P84 map params', name: 'map param: m.sum property == precondition', ok: true,
         src: tc('''class C {
                        @Requires({ m.sum == 3 })
                        @Ensures({ result == 3 })
                        static int f(Map<String, Integer> m) { m.sum }
                    }''')],
        [group: 'P84 map params', name: 'map param: subscript form still works', ok: true,
         src: tc('''class C {
                        @Requires({ m['sum'] == 3 })
                        @Ensures({ result == 3 })
                        static int f(Map<String, Integer> m) { m['sum'] }
                    }''')],
        // Key arithmetic lives in the body (contract closures erase the value generic to Object, so `m.x +
        // m.y` won't compile there — the same @TypeChecked limit as tuple slots / List<Double>).
        [group: 'P84 map params', name: 'map param: keys in body arithmetic', ok: true,
         src: tc('''class C {
                        @Requires({ m.x >= 5 && m.y >= 5 })
                        @Ensures({ result >= 10 })
                        static int f(Map<String, Integer> m) { m.x + m.y }
                    }''')],
        [group: 'P84 map params', name: 'map param: wrong value refutes', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Requires({ m.sum == 3 })
                        @Ensures({ result == 4 })
                        static int f(Map<String, Integer> m) { m.sum }
                    }''')],

        // Regression (Phase 84 fix): a property access on a RAW `Map` (non-String / unknown key sort) must
        // skip loudly, NOT crash Z3 with a key-domain sort mismatch. (Named-argument maps land here: raw
        // `Map`, Object values — at odds with @TypeChecked, so not verifiable; the point is it can't crash.)
        [group: 'P84 map params', name: 'raw Map property skips, no crash', expect: 'outside fragment',
         src: tc('''class C {
                        @Requires({ m.foo == 0 })
                        @Ensures({ result == 0 })
                        static int f(Map m) { 0 }
                    }''')],

        // ---------- Phase 85: compound assignment operators (+= -= *= /= %=) ----------
        // A statement-level desugar `s += e` → `s = s + e`, applied in both the straight-line and loop
        // body processors — so the same variable / field / array-element assignment paths handle it.
        // (No overlap with contracts: contract closures are pure predicates and never contain assignments.)
        [group: 'P85 compound assign', name: 'sumProduct loop body with += *=', ok: true,
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() > 0 })
                        @Ensures({ result == xs.sum() + xs.inject(1) { a, x -> a * x } })
                        static int sumProduct(List<Integer> xs) {
                            int s = xs[0]
                            int p = xs[0]
                            int i = 1
                            @Invariant({ 1 <= i && i <= xs.size() &&
                                         s == xs[0..<i].sum() && p == xs[0..<i].inject(1) { a, x -> a * x } })
                            @Decreases({ xs.size() - i })
                            while (i < xs.size()) { s += xs[i]; p *= xs[i]; i += 1 }
                            return s + p
                        }
                    }''')],
        [group: 'P85 compound assign', name: 'straight-line += then *=', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 6 })
                        static int f() { int s = 1; s += 2; s *= 2; s }
                    }''')],
        [group: 'P85 compound assign', name: 'straight-line -= symbolic', ok: true,
         src: tc('''class C {
                        @Requires({ x >= 3 })
                        @Ensures({ result == x - 3 })
                        static int f(int x) { int s = x; s -= 3; s }
                    }''')],
        [group: 'P85 compound assign', name: 'wrong compound result refutes', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Ensures({ result == 5 })
                        static int f() { int s = 1; s += 2; s }
                    }''')],
        // Array-element compound assignment desugars to an array store.
        [group: 'P85 compound assign', name: 'array element a[i] += 1', ok: true,
         src: tc('''class C {
                        int[] a
                        @Requires({ a != null && 0 <= i && i < a.length })
                        @Ensures({ a[i] == old.a[i] + 1 })
                        void bump(int i) { a[i] += 1 }
                    }''')],

        // ---------- Phase 86: pre/post increment & decrement (++ / --) as statements ----------
        // `i++` / `++i` / `i--` / `--i` desugar to `i = i ± 1` (pre/post is irrelevant as a statement),
        // in both straight-line and loop-body positions (the for-loop *update* slot already handled them).
        [group: 'P86 inc/dec', name: 'straight-line i++', ok: true,
         src: tc('class C { @Ensures({ result == 6 }) static int f() { int s = 5; s++; s } }')],
        [group: 'P86 inc/dec', name: 'straight-line ++i (prefix)', ok: true,
         src: tc('class C { @Ensures({ result == 6 }) static int f() { int s = 5; ++s; s } }')],
        [group: 'P86 inc/dec', name: 'straight-line i--', ok: true,
         src: tc('class C { @Ensures({ result == 4 }) static int f() { int s = 5; s--; s } }')],
        [group: 'P86 inc/dec', name: 'wrong inc result refutes', expect: 'Cannot prove postcondition',
         src: tc('class C { @Ensures({ result == 5 }) static int f() { int s = 5; s++; s } }')],
        // The idiomatic loop counter: `i++` in the while body.
        [group: 'P86 inc/dec', name: 'while body i++ counter', ok: true,
         src: tc('''class C {
                        @Requires({ n >= 0 })
                        @Ensures({ result == n })
                        static int count(int n) {
                            int c = 0
                            int i = 0
                            @Invariant({ 0 <= i && i <= n && c == i })
                            @Decreases({ n - i })
                            while (i < n) { c++; i++ }
                            c
                        }
                    }''')],
        // Array-element increment desugars to an array store.
        [group: 'P86 inc/dec', name: 'array element a[i]++', ok: true,
         src: tc('''class C {
                        int[] a
                        @Requires({ a != null && 0 <= i && i < a.length })
                        @Ensures({ a[i] == old.a[i] + 1 })
                        void bump(int i) { a[i]++ }
                    }''')],

        // ---------- Phase 78: list-literal returns + constant-index result[k] ----------
        // A method may now return a list literal and have @Ensures reference its elements by constant
        // index: `result` is bound as a factory container, so result.size()/result[k] fold.
        [group: 'P78 list return', name: 'return [1,2]: result[0]==1 && result[1]==2', ok: true,
         src: tc('''class C {
                        @Ensures({ result[0] == 1 && result[1] == 2 && result.size() == 2 })
                        static List<Integer> pair() { [1, 2] }
                    }''')],
        // The faithful HumanEval 008 (sum_product): return BOTH aggregates as a list, each element proven
        // against its aggregate — what previously had to collapse to `s + p` for lack of tuple/list returns.
        [group: 'P78 list return', name: 'sum_product returns [sum, product]', ok: true,
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() > 0 })
                        @Ensures({ result[0] == xs.sum() && result[1] == xs.inject(1) { a, x -> a * x } })
                        static List<Integer> sumProduct(List<Integer> xs) {
                            int s = xs[0]
                            int p = xs[0]
                            int i = 1
                            @Invariant({ 1 <= i && i <= xs.size() &&
                                         s == xs[0..<i].sum() &&
                                         p == xs[0..<i].inject(1) { a, x -> a * x } })
                            @Decreases({ xs.size() - i })
                            while (i < xs.size()) {
                                s = s + xs[i]
                                p = p * xs[i]
                                i = i + 1
                            }
                            return [s, p]
                        }
                    }''')],
        // A false element claim refutes (result[1] is 2, not 1).
        [group: 'P78 list return', name: 'return [1,2]: wrong element claim refutes', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Ensures({ result[1] == 1 })
                        static List<Integer> pair() { [1, 2] }
                    }''')],

        // The SAME returns through a declared `int[]` type (not List). Groovy implicitly coerces the body's
        // list literal `[s, p]` to int[], and the result-binding keys off the return EXPRESSION (a
        // ListExpression), so `result` binds as a list factory exactly as the List<Integer> form does —
        // result[k] / result.length fold, independent of the declared array type. No code beyond Phase 78
        // was needed; these lock the int[]-return shape in (it previously worked only untested).
        [group: 'P78 int[] return', name: '[a,b] coerced to int[]: result[k] + length', ok: true,
         src: tc('''class C {
                        @Ensures({ result.length == 2 && result[0] == a && result[1] == b })
                        static int[] pair(int a, int b) { [a, b] }
                    }''')],
        // Crisp refute: the size pin (factory entry count) makes a wrong `.length` UNSAT. Kept axiom-free
        // (no aggregation) so the refute is a clean counterexample, not the refute-hostile timeout the
        // inject/sum axioms produce (the gcd/fib aggregation-helper property: prove-friendly, refute-hostile).
        [group: 'P78 int[] return', name: 'int[] return: wrong length refutes', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Ensures({ result.length == 3 })
                        static int[] pair(int a, int b) { [a, b] }
                    }''')],
        // Flagship: HumanEval 008 sum_product with an int[] return — the List<Integer> sibling above, now
        // array-typed. Both aggregates proven element-wise off the loop invariant (sum + inject product).
        [group: 'P78 int[] return', name: 'sum_product returns int[] [sum, product]', ok: true,
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() > 0 })
                        @Ensures({ result[0] == xs.sum() && result[1] == xs.inject(1) { a, x -> a * x } })
                        static int[] sumProduct(List<Integer> xs) {
                            int s = xs[0], p = xs[0], i = 1
                            @Invariant({ 1 <= i && i <= xs.size() &&
                                         s == xs[0..<i].sum() && p == xs[0..<i].inject(1) { a, x -> a * x } })
                            @Decreases({ xs.size() - i })
                            while (i < xs.size()) { s += xs[i]; p *= xs[i]; i += 1 }
                            [s, p]
                        }
                    }''')],
        // The CONSTRUCTED array-literal form `new int[]{...}` (an ArrayExpression with an initializer) — the
        // array dual of a list literal. Recognised as a fixed-arity list-kind factory over its initializer
        // expressions, so result[k] / result.length fold exactly as the coerced `[a,b]` form does.
        [group: 'P78 int[] return', name: 'new int[]{a,b} return: result[k] + length', ok: true,
         src: tc('''class C {
                        @Ensures({ result.length == 2 && result[0] == a && result[1] == b })
                        static int[] pair(int a, int b) { new int[]{a, b} }
                    }''')],
        // Crisp refute (int elements, no aggregation axiom): result[0] is a, not b.
        [group: 'P78 int[] return', name: 'new int[]{a,b} return: wrong element refutes', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Ensures({ result[0] == b })
                        static int[] pair(int a, int b) { new int[]{a, b} }
                    }''')],
        // A body local bound to `new int[]{...}` records as a factory too (tryRecordFactoryAssign on the
        // local), so the returned local's elements/length fold without any array store.
        [group: 'P78 int[] return', name: 'new int[]{...} local, returned', ok: true,
         src: tc('''class C {
                        @Ensures({ result.length == 3 && result[0] == x && result[2] == x })
                        static int[] triple(int x) { int[] r = new int[]{x, x, x}; r }
                    }''')],

        // ---------- Phase 79: Tuple / TupleN — fixed-arity typed products ----------
        // A `Tuple.tuple(a, b)` / `new TupleN(a, b)` is modelled as a fixed-arity factory (on the Phase-78
        // foundation), so a returned tuple binds `result` and its slots fold: `.v1`/`.vN`, `.first`/`.second`,
        // `.getVN()`, constant-index `[k]`, and `.size()`. Heterogeneous slots translate in their own sort.
        [group: 'P79 tuples', name: 'return Tuple.tuple(10,20): .v1/.v2', ok: true,
         src: tc('''class C {
                        @Ensures({ result.v1 == 10 && result.v2 == 20 })
                        static Tuple2<Integer, Integer> pair() { Tuple.tuple(10, 20) }
                    }''')],
        [group: 'P79 tuples', name: 'tuple accessors: [k], first/second, size', ok: true,
         src: tc('''class C {
                        @Ensures({ result[0] == 10 && result.first == 10 && result.second == 20 &&
                                   result.getV2() == 20 && result.size() == 2 })
                        static Tuple2<Integer, Integer> pair() { Tuple.tuple(10, 20) }
                    }''')],
        // new TupleN constructor form, heterogeneous slots (Integer + String) each in their own sort.
        [group: 'P79 tuples', name: 'new Tuple2(1, "hi"): heterogeneous slots', ok: true,
         src: tc('''class C {
                        @Ensures({ result.v1 == 1 && result.v2 == "hi" })
                        static Tuple2<Integer, String> pair() { new Tuple2<Integer, String>(1, "hi") }
                    }''')],
        // The faithful HumanEval 008 (sum_product) as a TYPED tuple return.
        [group: 'P79 tuples', name: 'sum_product returns Tuple2(sum, product)', ok: true,
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() > 0 })
                        @Ensures({ result.v1 == xs.sum() && result.v2 == xs.inject(1) { a, x -> a * x } })
                        static Tuple2<Integer, Integer> sumProduct(List<Integer> xs) {
                            int s = xs[0]
                            int p = xs[0]
                            int i = 1
                            @Invariant({ 1 <= i && i <= xs.size() &&
                                         s == xs[0..<i].sum() &&
                                         p == xs[0..<i].inject(1) { a, x -> a * x } })
                            @Decreases({ xs.size() - i })
                            while (i < xs.size()) { s += xs[i]; p *= xs[i]; i += 1 }
                            return Tuple.tuple(s, p)
                        }
                    }''')],
        // A false slot claim refutes (.v1 is 10, not 20).
        [group: 'P79 tuples', name: 'tuple wrong slot claim refutes', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Ensures({ result.v1 == 20 })
                        static Tuple2<Integer, Integer> pair() { Tuple.tuple(10, 20) }
                    }''')],
        // Multiple assignment `def (a, b) = …` desugars to a temp + constant-index slot reads.
        [group: 'P79 tuples', name: 'multiple assignment from a tuple', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 30 })
                        static int m() {
                            def (a, b) = Tuple.tuple(10, 20)
                            a + b
                        }
                    }''')],
        [group: 'P79 tuples', name: 'multiple assignment from a list literal', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 3 })
                        static int m() {
                            def (a, b) = [1, 2]
                            a + b
                        }
                    }''')],
        [group: 'P79 tuples', name: 'multiple assignment wrong sum refutes', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Ensures({ result == 99 })
                        static int m() {
                            def (a, b) = [1, 2]
                            a + b
                        }
                    }''')],

        // ---------- Phase 80: tuple PARAMETERS with .vN access ----------
        // A tuple parameter's slots are the caller's components — each `t.vN`/`t[k]` mints a fresh typed
        // entity `t$vN` in the slot's sort (like a Phase-45 object field). `.size()` folds to the arity.
        // Slot access flows to the body's return (arithmetic on slots lives in the body, where generics
        // survive — in the *contract* closure @TypeChecked erases the slot generic to Object, so contracts
        // use comparisons on slots, not arithmetic).
        [group: 'P80 tuple params', name: 'tuple param: result == t.v1', ok: true,
         src: tc('''class C {
                        @Ensures({ result == t.v1 })
                        static int firstOf(Tuple2<Integer, Integer> t) { t.v1 }
                    }''')],
        [group: 'P80 tuple params', name: 'tuple param: first/second + size', ok: true,
         src: tc('''class C {
                        @Requires({ t.first >= 0 && t.second >= 0 })
                        @Ensures({ result >= 0 && t.size() == 2 })
                        static int sum(Tuple2<Integer, Integer> t) { t.first + t.second }
                    }''')],
        // Heterogeneous tuple parameter: v1 Int, v2 String — each a distinct entity in its own sort.
        [group: 'P80 tuple params', name: 'tuple param: heterogeneous Int + String', ok: true,
         src: tc('''class C {
                        @Requires({ t.v2 == "hi" })
                        @Ensures({ result == t.v1 })
                        static int f(Tuple2<Integer, String> t) { t.v1 }
                    }''')],
        // Constant-index access on a tuple parameter.
        [group: 'P80 tuple params', name: 'tuple param: constant index t[0]', ok: true,
         src: tc('''class C {
                        @Ensures({ result == t[0] })
                        static int first(Tuple2<Integer, Integer> t) { t.v1 }
                    }''')],
        // Refute: v1 >= 0 does not give v1 > 0.
        [group: 'P80 tuple params', name: 'tuple param: v1>=0 does not prove v1>0', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Requires({ t.v1 >= 0 })
                        @Ensures({ result > 0 })
                        static int f(Tuple2<Integer, Integer> t) { t.v1 }
                    }''')],

        // ---------- Phase 81: component-wise tuple / list == ----------
        // `a == b` over two fixed-arity products folds to the conjunction of pairwise component equalities
        // (and `!=` its negation); a length mismatch is false (Groovy's list/tuple equality).
        [group: 'P81 tuple eq', name: 'equal constructed tuples', ok: true,
         src: tc('''class C {
                        @Ensures({ Tuple.tuple(1, 2) == Tuple.tuple(1, 2) })
                        static void m() { }
                    }''')],
        [group: 'P81 tuple eq', name: 'unequal tuples refute', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Ensures({ Tuple.tuple(1, 2) == Tuple.tuple(1, 3) })
                        static void m() { }
                    }''')],
        [group: 'P81 tuple eq', name: 'unequal tuples !=', ok: true,
         src: tc('''class C {
                        @Ensures({ Tuple.tuple(1, 2) != Tuple.tuple(1, 3) })
                        static void m() { }
                    }''')],
        // Two tuple parameters: equal components ⇒ equal tuples.
        [group: 'P81 tuple eq', name: 'two params: equal components ⇒ a == b', ok: true,
         src: tc('''class C {
                        @Requires({ a.v1 == b.v1 && a.v2 == b.v2 })
                        @Ensures({ a == b })
                        static void check(Tuple2<Integer, Integer> a, Tuple2<Integer, Integer> b) { }
                    }''')],
        // Tuple parameter vs a constructed tuple.
        [group: 'P81 tuple eq', name: 'param == constructed tuple', ok: true,
         src: tc('''class C {
                        @Requires({ t.v1 == 5 && t.v2 == 7 })
                        @Ensures({ t == Tuple.tuple(5, 7) })
                        static void check(Tuple2<Integer, Integer> t) { }
                    }''')],
        // Different arity ⇒ not equal.
        [group: 'P81 tuple eq', name: 'different arity refutes', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Ensures({ Tuple.tuple(1, 2) == Tuple.tuple(1, 2, 3) })
                        static void m() { }
                    }''')],
        // Bonus: the same fold gives list-literal equality.
        [group: 'P81 tuple eq', name: 'list literal equality', ok: true,
         src: tc('''class C {
                        @Ensures({ [1, 2, 3] == [1, 2, 3] })
                        static void m() { }
                    }''')],

        // ---------- Phase 82: nested tuples ----------
        // Constructed/returned nested tuple — slot resolution recurses through the factory containers. Nested
        // access lives in the BODY: a *contract* closure erases the nested generic to Object (`result.v1.v2`
        // → Object.v2) under @TypeChecked, the same erasure as slot arithmetic / List<Double> elements.
        [group: 'P82 nested', name: 'constructed nested: .v1.v2 == 2 (body)', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 2 })
                        static int m() { Tuple.tuple(Tuple.tuple(1, 2), 3).v1.v2 }
                    }''')],
        [group: 'P82 nested', name: 'constructed nested via local', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 2 })
                        static int m() {
                            def t = Tuple.tuple(Tuple.tuple(1, 2), 3)
                            t.v1.v2
                        }
                    }''')],
        [group: 'P82 nested', name: 'constructed nested: .v1.v1 == 1 (body)', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int m() { Tuple.tuple(Tuple.tuple(1, 2), 3).v1.v1 }
                    }''')],
        // Nested tuple PARAMETER — t.v1.v2 flattens to a fresh entity t$v1$v2.
        [group: 'P82 nested', name: 'nested param: body access verifies', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 0 })
                        static int f(Tuple2<Tuple2<Integer, Integer>, Integer> t) {
                            int x = t.v1.v2
                            x - x
                        }
                    }''')],
        [group: 'P82 nested', name: 'nested param: unconstrained slot refutes', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Ensures({ result == 5 })
                        static int f(Tuple2<Tuple2<Integer, Integer>, Integer> t) { t.v1.v2 }
                    }''')],

        // ---------- Phase 54: sign-faithful Integer.toString / parseInt ----------
        // toString of a negative int is non-empty ("-7"); the old raw `intToString` modelled it as ""
        // and silently *verified* result.isEmpty() — now fixed.
        [group: 'P54 int-string signs', name: 'negative toString is non-empty', ok: true,
         src: tc('''class C {
                        @Requires({ n < 0 })
                        @Ensures({ !result.isEmpty() })
                        static String f(int n) { Integer.toString(n) }
                    }''')],
        [group: 'P54 int-string signs', name: 'negative toString isEmpty now refutes',
         expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Requires({ n < 0 })
                        @Ensures({ result.isEmpty() })
                        static String f(int n) { Integer.toString(n) }
                    }''')],
        // toString(-7) == "-7" exactly.
        [group: 'P54 int-string signs', name: 'toString of a specific negative', ok: true,
         src: tc('''class C {
                        @Requires({ n == -7 })
                        @Ensures({ result == "-7" })
                        static String f(int n) { Integer.toString(n) }
                    }''')],
        // Round-trip now holds for ALL n, not just n >= 0 (the old gap needed a non-negative guard).
        [group: 'P54 int-string signs', name: 'parseInt(toString(n)) == n for negative n', ok: true,
         src: tc('''class C {
                        @Requires({ n < 0 })
                        @Ensures({ result == n })
                        static int f(int n) { Integer.parseInt(Integer.toString(n)) }
                    }''')],
        // Loud obligation: parseInt of an *unconstrained* String might throw → refuted (the engine
        // no longer silently models malformed input as -1).
        [group: 'P54 int-string signs', name: 'parseInt of arbitrary string refutes (NFE)',
         expect: 'NumberFormatException',
         src: tc('''class C {
                        @Requires({ s != null })
                        static int f(String s) { Integer.parseInt(s) }
                    }''')],
        // ...and parseInt(toString(n)) is *provably* well-formed → no NumberFormatException fires.
        [group: 'P54 int-string signs', name: 'parseInt of toString is well-formed', ok: true,
         src: tc('''class C {
                        @Ensures({ result == n })
                        static int f(int n) { Integer.parseInt(Integer.toString(n)) }
                    }''')],

        // ---------- HumanEval 055 (fib): Fibonacci generation via the Fib.of(i) helper (Phase 55) ----------
        // `fibIter` below IS HumanEval task 055 (`fib`, the n-th Fibonacci number) with the spec the Verus
        // corpus omits — our `Fib.of` indexing matches HumanEval's (Fib.of(10)==55, Fib.of(8)==21). It also
        // underpins task 039's prime_fib (whose *outer* search is the deliberate non-target).
        // A literal index unfolds through the step axiom to a concrete value (0,1,1,2,3,5).
        [group: 'P55 fib', name: 'Fib.of(5) == 5', ok: true,
         src: tc('''class C {
                        @Ensures({ Fib.of(5) == 5 })
                        static void f() { }
                    }''')],
        // Non-vacuousness anchor (positive): the step law holds at a literal index. (Refuting a *false*
        // fib claim is the known weak direction — Z3 can't model the ∀ step axiom, so it returns honest
        // UNKNOWN rather than a counterexample.)
        [group: 'P55 fib', name: 'Fib step law at 6 holds', ok: true,
         src: tc('''class C {
                        @Ensures({ Fib.of(6) == Fib.of(5) + Fib.of(4) })
                        static void f() { }
                    }''')],
        // The textbook proof: an iterative Fibonacci provably equals the recursive definition. The
        // invariant carries the two-term recurrence (a == fib(i), b == fib(i+1)); the step axiom
        // re-establishes it across `b = a + b`. Terminates (`n - i`), unlike the outer prime_fib search.
        // (Bare `Fib.of` inside @Invariant resolves the import since GROOVY-12072 — no `verification.` FQN.)
        [group: 'P55 fib', name: 'iterative Fibonacci equals Fib.of(n)', ok: true,
         src: tc('''class C {
                        @Requires({ n >= 0 })
                        @Ensures({ result == Fib.of(n) })
                        static int fibIter(int n) {
                            int a = 0
                            int b = 1
                            int i = 0
                            @Invariant({ 0 <= i && i <= n &&
                                         a == Fib.of(i) && b == Fib.of(i + 1) })
                            @Decreases({ n - i })
                            while (i < n) {
                                int t = a + b
                                a = b
                                b = t
                                i = i + 1
                            }
                            return a
                        }
                    }''')],

        // ---------- HumanEval 063 (fibfib): tribonacci via the Trib.of(i) helper ----------
        // The three-term sibling of 055. `Trib.of` indexing matches HumanEval's fibfib (Trib.of(5)==4,
        // Trib.of(8)==24); a literal index unfolds through the step axiom (0,0,1,1,2,4,7,13,24).
        [group: 'P63 fibfib', name: 'Trib.of(8) == 24', ok: true,
         src: tc('''class C {
                        @Ensures({ Trib.of(8) == 24 })
                        static void f() { }
                    }''')],
        // Step law at a literal index (positive non-vacuousness anchor; refuting a false claim is the weak direction).
        [group: 'P63 fibfib', name: 'Trib step law at 7 holds', ok: true,
         src: tc('''class C {
                        @Ensures({ Trib.of(7) == Trib.of(6) + Trib.of(5) + Trib.of(4) })
                        static void f() { }
                    }''')],
        // The textbook proof: an iterative fibfib provably equals the recursive definition. A 3-wide
        // rolling window (a==trib(i), b==trib(i+1), c==trib(i+2)); the step axiom re-establishes it across
        // `c = a + b + c` (e-matching trib(i+3) == trib(i+2)+trib(i+1)+trib(i)). Terminates (`n - i`).
        [group: 'P63 fibfib', name: 'iterative fibfib equals Trib.of(n)', ok: true,
         src: tc('''class C {
                        @Requires({ n >= 0 })
                        @Ensures({ result == Trib.of(n) })
                        static int fibfib(int n) {
                            int a = 0
                            int b = 0
                            int c = 1
                            int i = 0
                            @Invariant({ 0 <= i && i <= n &&
                                         a == Trib.of(i) &&
                                         b == Trib.of(i + 1) &&
                                         c == Trib.of(i + 2) })
                            @Decreases({ n - i })
                            while (i < n) {
                                int t = a + b + c
                                a = b
                                b = c
                                c = t
                                i = i + 1
                            }
                            return a
                        }
                    }''')],

        // ---------- HumanEval 013 (greatest_common_divisor): Euclid via the Gcd.of(a, b) helper ----------
        // The two-argument sibling of 055/063. `Gcd.of` is Euclid; a literal pair unfolds through the step
        // axiom down to the base (gcd(12,8) → gcd(8,4) → gcd(4,0) → 4).
        [group: 'HE013 gcd', name: 'Gcd.of(12, 8) == 4', ok: true,
         src: tc('''class C {
                        @Ensures({ Gcd.of(12, 8) == 4 })
                        static int g() { 4 }
                    }''')],
        // The Euclid recurrence itself — the step axiom restated as a postcondition (proves directly).
        [group: 'HE013 gcd', name: 'Gcd.of(a, b) == Gcd.of(b, a % b) when b != 0', ok: true,
         src: tc('''class C {
                        @Requires({ b != 0 })
                        @Ensures({ Gcd.of(a, b) == Gcd.of(b, a % b) })
                        static void rel(int a, int b) { }
                    }''')],
        // Iterative Euclid equals Gcd.of(a, b): the invariant `Gcd.of(x, y) == Gcd.of(a, b)` is preserved by
        // `t = x % y; x = y; y = t` (step axiom, b != 0 from the guard), and at exit (y == 0) the base axiom
        // gives x == Gcd.of(a, b). Terminates: `y` strictly decreases (x % y ∈ [0, y) for x >= 0, y > 0).
        [group: 'HE013 gcd', name: 'iterative Euclid equals Gcd.of(a, b)', ok: true,
         src: tc('''class C {
                        @Requires({ a >= 0 && b >= 0 })
                        @Ensures({ result == Gcd.of(a, b) })
                        static int gcd(int a, int b) {
                            int x = a
                            int y = b
                            @Invariant({ x >= 0 && y >= 0 &&
                                         Gcd.of(x, y) == Gcd.of(a, b) })
                            @Decreases({ y })
                            while (y != 0) {
                                int t = x % y
                                x = y
                                y = t
                            }
                            return x
                        }
                    }''')],
        // Without a non-negativity precondition the Euclid loop's bounds invariant `x >= 0 && y >= 0`
        // (the part that drives @Decreases via `x % y ∈ [0, y)`) can't be established on entry — a negative
        // input is a crisp counterexample. (A *value* refutation like `Gcd.of(12,8)==5` instead soft-fails
        // with "could not decide / timeout": the recursive step axiom is prove-friendly via e-matching but
        // refute-hostile — finding a SAT model under an infinitely-instantiable axiom defeats MBQI. The
        // verifier still rejects it; it just can't produce a counterexample. Same trade-off as fib/trib.)
        [group: 'HE013 gcd', name: 'Euclid loop bounds need a non-negativity precondition',
         src: tc('''class C {
                        static int gcd(int a, int b) {
                            int x = a
                            int y = b
                            @Invariant({ x >= 0 && y >= 0 })
                            @Decreases({ y })
                            while (y != 0) {
                                int t = x % y
                                x = y
                                y = t
                            }
                            return x
                        }
                    }'''),
         expect: 'Cannot prove loop invariant holds on entry'],

        // ---------- HumanEval 045 (triangle_area): scalar IEEE-754 FP (Phase 73) ----------
        // triangle_area(a, h) = a * h / 2. With `double` inputs this is the FP fragment: the formula
        // proves, the doctest value 7.5 is exact, and `result >= 0` for positive sides is real FP sign
        // reasoning (a*h/2 is positive-or-+0, never NaN) — not just the formula restated.
        [group: 'HE045 triangle_area', name: 'doctest: area(5,3) == 7.5 (exact in FP)', ok: true,
         src: tc('class C { @Ensures({ result == 7.5d }) static double area() { 5.0d * 3.0d / 2.0d } }')],
        // The formula `result == a*h/2` is NOT trivially true in IEEE-754: if an input is NaN/∞ the result
        // is NaN, and NaN != NaN — so even `x == x` fails. With a finiteness guard it holds and proves.
        [group: 'HE045 triangle_area', name: 'formula: finite sides ⇒ result == a * h / 2', ok: true,
         src: tc('class C { @Requires({ Double.isFinite(a) && Double.isFinite(h) }) @Ensures({ result == a * h / 2.0d }) static double area(double a, double h) { a * h / 2.0d } }')],
        [group: 'HE045 triangle_area', name: 'positive sides ⇒ area >= 0 (FP sign reasoning)', ok: true,
         src: tc('class C { @Requires({ a > 0.0d && h > 0.0d }) @Ensures({ result >= 0.0d }) static double area(double a, double h) { a * h / 2.0d } }')],
        // Honest FP subtlety: area is NOT provably *strictly* positive — tiny positive sides underflow
        // a*h to +0.0, so `result > 0` refutes. A real IEEE-754 fact, false in exact arithmetic.
        [group: 'HE045 triangle_area', name: 'positive sides do NOT guarantee area > 0 (FP underflow)', expect: 'Cannot prove postcondition',
         src: tc('class C { @Requires({ a > 0.0d && h > 0.0d }) @Ensures({ result > 0.0d }) static double area(double a, double h) { a * h / 2.0d } }')],

        // ---------- HumanEval 35 (max_element): the witnessed extremum ----------
        // The spec is BOTH universal and existential: the result is >= every element AND is *equal to*
        // one of them (the "witness"). The invariant carries both as the running max grows.
        [group: 'P56 max', name: 'max_element is a witnessed extremum', ok: true,
         src: tc('''class C {
                        @Requires({ a != null && a.length > 0 })
                        @Ensures({ (0..<a.length).every { a[it] <= result } &&
                                   (0..<a.length).any { a[it] == result } })
                        static int maxElement(int[] a) {
                            int m = a[0]
                            int i = 1
                            @Invariant({ 1 <= i && i <= a.length &&
                                         (0..<i).every { a[it] <= m } &&
                                         (0..<i).any { a[it] == m } })
                            @Decreases({ a.length - i })
                            while (i < a.length) {
                                if (a[i] > m) m = a[i]
                                i = i + 1
                            }
                            return m
                        }
                    }''')],
        // min — the symmetric witnessed extremum (result <= every element, and is one of them).
        [group: 'P56 max', name: 'min_element is a witnessed extremum', ok: true,
         src: tc('''class C {
                        @Requires({ a != null && a.length > 0 })
                        @Ensures({ (0..<a.length).every { result <= a[it] } &&
                                   (0..<a.length).any { a[it] == result } })
                        static int minElement(int[] a) {
                            int m = a[0]
                            int i = 1
                            @Invariant({ 1 <= i && i <= a.length &&
                                         (0..<i).every { m <= a[it] } &&
                                         (0..<i).any { a[it] == m } })
                            @Decreases({ a.length - i })
                            while (i < a.length) {
                                if (a[i] < m) m = a[i]
                                i = i + 1
                            }
                            return m
                        }
                    }''')],
        // Soundness anchor: returning the first element isn't the max — the universal clause refutes
        // (some later element can exceed it). The existential witness alone isn't enough.
        [group: 'P56 max', name: 'returning a[0] is not the max (refutes)',
         expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Requires({ a != null && a.length > 0 })
                        @Ensures({ (0..<a.length).every { a[it] <= result } &&
                                   (0..<a.length).any { a[it] == result } })
                        static int badMax(int[] a) { a[0] }
                    }''')],

        // ---------- Phase 57: logical implication — `==>` operator and `.implies()` method ----------
        // The `==>` operator (Groovy 5) is a BinaryExpression lowered to `implies(a, b) = !a || b`.
        // Modus ponens: from `(a>=0) ==> (b>=0)` and `a>=0`, derive `b>=0`.
        // The two premises read naturally as two @Requires (conjoined automatically since Phase 66 —
        // this once needed a single combined @Requires, before repeated annotations were captured).
        [group: 'P57 implies', name: 'modus ponens via ==> operator', ok: true,
         src: tc('''class C {
                        @Requires({ (a >= 0) ==> (b >= 0) })
                        @Requires({ a >= 0 })
                        @Ensures({ result >= 0 })
                        static int f(int a, int b) { b }
                    }''')],
        // The `.implies()` method form (DGM Boolean.implies) lowers the same way.
        [group: 'P57 implies', name: 'modus ponens via .implies() method', ok: true,
         src: tc('''class C {
                        @Requires({ (a >= 0).implies(b >= 0) && a >= 0 })
                        @Ensures({ result >= 0 })
                        static int f(int a, int b) { b }
                    }''')],
        // Soundness: the implication alone (without the antecedent) doesn't give the consequent.
        [group: 'P57 implies', name: 'implication without antecedent refutes',
         expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Requires({ (a >= 0) ==> (b >= 0) })
                        @Ensures({ result >= 0 })
                        static int f(int a, int b) { b }
                    }''')],
        // Simplification showcase: the array-element frame reads as an implication — every index
        // OTHER than j is unchanged — `it != j ==> a[it] == old.a[it]` (vs `it == j || …`).
        [group: 'P57 implies', name: 'array frame via ==> implication', ok: true,
         src: tc('''class C {
                       int[] a
                       @Requires({ 0 <= j && j < a.length })
                       @Ensures({ (0..<a.length).every { it != j ==> a[it] == old.a[it] } })
                       void set(int j, int v) { a[j] = v }
                   }''')],

        // ---------- Phase 58: spaceship operator `<=>` (three-way Int comparison) ----------
        // `a <=> b` is a correct three-way comparator: its sign matches the direct comparison.
        [group: 'P58 spaceship', name: 'spaceship is a correct three-way comparator', ok: true,
         src: tc('''class C {
                        @Ensures({ (result < 0) == (a < b) && (result == 0) == (a == b) &&
                                   (result > 0) == (a > b) })
                        static int cmp(int a, int b) { a <=> b }
                    }''')],
        // For a < b the spaceship is exactly -1 (Integer.compareTo semantics).
        [group: 'P58 spaceship', name: 'spaceship of a<b is -1', ok: true,
         src: tc('''class C {
                        @Requires({ a < b })
                        @Ensures({ result == -1 })
                        static int cmp(int a, int b) { a <=> b }
                    }''')],
        // Soundness: unconstrained, the spaceship isn't always 1.
        [group: 'P58 spaceship', name: 'spaceship is not always 1 (refutes)',
         expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int cmp(int a, int b) { a <=> b }
                    }''')],

        // ---------- `!in` operator (negated membership; `x !in s` ≡ `!(x in s)`) ----------
        // It lowers to the identical `not(member)` term as `!(x in s)` — recognised in contracts.
        [group: 'P16 sets', name: '!in is negated membership', ok: true,
         src: tc('''class C {
                        @Requires({ x !in s })
                        @Ensures({ !(x in s) })
                        static int f(Set<Integer> s, int x) { 0 }
                    }''')],
        [group: 'P16 sets', name: '!in does not imply membership (refutes)',
         expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Requires({ x !in s })
                        @Ensures({ x in s })
                        static int f(Set<Integer> s, int x) { 0 }
                    }''')],

        // The earlier P37 "in-body if (xs[i] != null) guard verifies" test covered the
        // straight-line case. Phase 46d extends the same path-fact mechanism to the loop body:
        // dischargeRegion recurses into an in-region if-statement, asserting the cond in the
        // then-branch and !cond in the else-branch, then descends through &&/||/ternary
        // operands so the right operand is discharged under the short-circuit guard.
        [group: 'P46d in-loop guards', name: 'in-loop if (xs[i] != null) discharges deref obligation', ok: true,
         src: tc('''class C {
                        @Requires({ xs != null })
                        static int f(List<String> xs) {
                            int n = 0
                            int i = 0
                            @Invariant({ 0 <= i && i <= xs.size() && n >= 0 })
                            @Decreases({ xs.size() - i })
                            while (i < xs.size()) {
                                if (xs[i] != null) {
                                    n = n + xs[i].length()
                                }
                                i = i + 1
                            }
                            return n
                        }
                    }''')],
        // && short-circuit inside the if-cond — the natural way to write a guarded deref.
        [group: 'P46d in-loop guards', name: 'in-loop && short-circuit discharges deref obligation', ok: true,
         src: tc('''class C {
                        @Requires({ xs != null && p != null })
                        static int f(List<String> xs, String p) {
                            int n = 0
                            int i = 0
                            @Invariant({ 0 <= i && i <= xs.size() && n >= 0 })
                            @Decreases({ xs.size() - i })
                            while (i < xs.size()) {
                                if (xs[i] != null && xs[i].startsWith(p)) {
                                    n = n + 1
                                }
                                i = i + 1
                            }
                            return n
                        }
                    }''')],
        // Soundness: removing the null guard refutes — the obligation is still real, the
        // path-fact mechanism only DISCHARGES the obligation when the guard establishes it.
        [group: 'P46d in-loop guards', name: 'in-loop unguarded deref refutes',
         expect: 'Possible NullPointerException',
         src: tc('''class C {
                        @Requires({ xs != null })
                        static int f(List<String> xs) {
                            int n = 0
                            int i = 0
                            @Invariant({ 0 <= i && i <= xs.size() && n >= 0 })
                            @Decreases({ xs.size() - i })
                            while (i < xs.size()) {
                                n = n + xs[i].length()
                                i = i + 1
                            }
                            return n
                        }
                    }''')],

        // ---------- HumanEval port — filter_by_prefix (Verus task 029) ----------
        // The Verus original is spec-free (only implicit overflow). groovy-verify ports the same
        // body and adds the natural size-bound spec: result.size() <= xs.size(). startsWith routes
        // through the P46a uninterpreted predicate; the spec doesn't try to relate startsWith to
        // string content, just that the conditional filter doesn't add more than it iterates —
        // the same invariant shape as get_positive (Verus 030), with startsWith(xs[i], prefix)
        // substituted for xs[i] > 0.
        [group: 'HumanEval port', name: 'filter_by_prefix (Verus 029): result.size() <= xs.size()', ok: true,
         src: tc('''class C {
                        @Requires({ xs != null && prefix != null })
                        @Ensures({ result.size() <= xs.size() })
                        static List<String> filterByPrefix(List<String> xs, String prefix) {
                            List<String> result = []
                            int i = 0
                            @Invariant({ result != null && 0 <= i && i <= xs.size() && result.size() <= i })
                            @Decreases({ xs.size() - i })
                            while (i < xs.size()) {
                                if (xs[i] != null && xs[i].startsWith(prefix)) {
                                    result.add(xs[i])
                                }
                                i = i + 1
                            }
                            return result
                        }
                    }''')],

        // ---------- HumanEval port — char-list reverse ----------
        // A char-list reverse: result.size() == xs.size(). Sits in the supported fragment without
        // any string-content machinery — the algorithm shape (read from one end, build the other)
        // is identical to a true String reverse, on the List<Character> API. The invariant carries
        // {@code r.size() == xs.size() - 1 - i}, which is preserved by each {@code r.add(xs[i])}
        // step and resolves at loop exit (i = -1) to {@code r.size() == xs.size()}. Demonstrates
        // that "reverse-shaped" proofs are reachable today; a String-typed reverse with character
        // content reasoning is the deferred Z3-string-theory phase.
        [group: 'HumanEval port', name: 'char-list reverse: result.size() == xs.size()', ok: true,
         src: tc('''class C {
                        @Requires({ xs != null })
                        @Ensures({ result.size() == xs.size() })
                        static List<Character> reverseList(List<Character> xs) {
                            List<Character> r = []
                            int i = xs.size() - 1
                            @Invariant({ r != null && -1 <= i && i < xs.size() && r.size() == xs.size() - 1 - i })
                            @Decreases({ i + 1 })
                            while (i >= 0) {
                                r.add(xs[i])
                                i = i - 1
                            }
                            return r
                        }
                    }''')],

        // ---------- Phase 38c-3: keySet / values projections on map factories ----------
        // Map.of(...).keySet() returns a set factory of the keys; .contains folds via disjunction.
        [group: 'P38c projection', name: 'Map.of(...).keySet().contains folds', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { Map.of("a", 1, "b", 2).keySet().contains("a") ? 1 : 0 }
                    }''')],
        // Soundness: a key not in the map doesn't appear in the keySet projection.
        [group: 'P38c projection', name: 'Map.of(...).keySet().contains refutes for absent key',
         expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { Map.of("a", 1, "b", 2).keySet().contains("z") ? 1 : 0 }
                    }''')],
        // Map.of(...).values() returns a list factory of the values; .contains folds.
        [group: 'P38c projection', name: 'Map.of(...).values().contains folds', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() { Map.of("a", 10, "b", 20).values().contains(20) ? 1 : 0 }
                    }''')],
        // .size() on a keySet projection folds to the literal key count.
        [group: 'P38c projection', name: 'keySet().size() folds', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 2 })
                        static int f() { Map.of("a", 1, "b", 2).keySet().size() }
                    }''')],

        // ---------- Phase 38c-4: non-constant-i ite-chain for factory list indexing ----------
        // Symbolic i in range: the ite-chain returns one of the literal elements; the disjunctive
        // @Ensures covers all three branches.
        [group: 'P38c symbolic i', name: 'List.of(...)[i] for symbolic i in range', ok: true,
         src: tc('''class C {
                        @Requires({ 0 <= i && i < 3 })
                        @Ensures({ result == 10 || result == 20 || result == 30 })
                        static int f(int i) { [10, 20, 30][i] }
                    }''')],
        // Soundness anchor: without the @Requires constraint on i, the ite-chain's default branch
        // (an unconstrained int) makes the @Ensures refute.
        [group: 'P38c symbolic i', name: 'List.of(...)[i] without bound refutes',
         expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Ensures({ result == 10 || result == 20 || result == 30 })
                        static int f(int i) { [10, 20, 30][i] }
                    }''')],
        // Composes with factory-through-assignment: local factory, symbolic index, bounded by
        // the (pinned) size oracle from Phase 38b.
        [group: 'P38c symbolic i', name: 'xs = List.of(...); xs[i] for symbolic i in range', ok: true,
         src: tc('''class C {
                        @Requires({ 0 <= i && i < 3 })
                        @Ensures({ result == 10 || result == 20 || result == 30 })
                        static int f(int i) {
                            List<Integer> xs = List.of(10, 20, 30)
                            xs[i]
                        }
                    }''')],

        // ---------- Phase 38b: factory through assignment ----------
        // The Phase 38 known limit closed: a local bound to a factory carries the fold across the
        // variable boundary. xs = List.of(args); xs.size() now folds the same as the inline form.
        [group: 'P38b factory local', name: 'xs = List.of(...); xs.size() folds', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 3 })
                        static int f() {
                            List<Integer> xs = List.of(1, 2, 3)
                            xs.size()
                        }
                    }''')],
        // Soundness anchor: the wrong literal refutes.
        [group: 'P38b factory local', name: 'xs = List.of(...); xs.size() wrong literal refutes',
         expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Ensures({ result == 4 })
                        static int f() {
                            List<Integer> xs = List.of(1, 2, 3)
                            xs.size()
                        }
                    }''')],
        // Groovy list literal through assignment: bracket-indexed access folds via the recorded factory.
        [group: 'P38b factory local', name: 'xs = [a, b, c]; xs[1] folds', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 20 })
                        static int f() {
                            List<Integer> xs = [10, 20, 30]
                            xs[1]
                        }
                    }''')],
        // .contains through assignment: disjunction over recorded elements.
        [group: 'P38b factory local', name: 'xs = List.of(...); xs.contains folds', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() {
                            List<Integer> xs = List.of(1, 2, 3)
                            xs.contains(2) ? 1 : 0
                        }
                    }''')],
        // `x in xs` operator through assignment.
        [group: 'P38b factory local', name: 'x in xs operator across assignment', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() {
                            List<Integer> xs = [1, 2, 3]
                            (2 in xs) ? 1 : 0
                        }
                    }''')],
        // Map factory through assignment: containsKey + get fold both lift across the variable.
        [group: 'P38b factory local', name: 'm = Map.of(...); m.containsKey + m.get fold', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 2 })
                        static int f() {
                            Map<String, Integer> m = Map.of("a", 1, "b", 2)
                            m.containsKey("b") ? m.get("b") : 0
                        }
                    }''')],
        // Set factory through assignment: .size folds.
        [group: 'P38b factory local', name: 's = Set.of(...); s.size folds', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 3 })
                        static int f() {
                            Set<Integer> s = Set.of(1, 2, 3)
                            s.size()
                        }
                    }''')],

        // ---------- Phase 39: common non-mutating list/map idioms ----------
        // xs.get(i) is sugar for xs[i] — both lower to (select xs i).
        [group: 'P39 idioms', name: 'xs.get(i) === xs[i]', ok: true,
         src: tc('''class C {
                        @Requires({ xs != null && 0 <= i && i < xs.size() })
                        @Ensures({ result == xs[i] })
                        static int f(List<Integer> xs, int i) { xs.get(i) }
                    }''')],
        // xs.first() === xs[0]; needs the precondition to discharge the bounds check.
        [group: 'P39 idioms', name: 'xs.first() === xs[0]', ok: true,
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() > 0 })
                        @Ensures({ result == xs[0] })
                        static int f(List<Integer> xs) { xs.first() }
                    }''')],
        // xs.head() — Groovy idiomatic alias for first().
        [group: 'P39 idioms', name: 'xs.head() === xs[0]', ok: true,
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() > 0 })
                        @Ensures({ result == xs[0] })
                        static int f(List<Integer> xs) { xs.head() }
                    }''')],
        // xs.last() === xs[size-1].
        [group: 'P39 idioms', name: 'xs.last() === xs[size-1]', ok: true,
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() > 0 })
                        @Ensures({ result == xs[xs.size() - 1] })
                        static int f(List<Integer> xs) { xs.last() }
                    }''')],
        // Implicit-bounds refute: xs.first() without a size guard refutes — Phase 39 synthesises an
        // IndexSite(xs, 0) so the bounds check fires the same way it does on xs[0].
        [group: 'P39 idioms', name: 'xs.first() without size guard refutes',
         expect: 'IndexOutOfBoundsException',
         src: tc('''class C {
                        @Requires({ xs != null })
                        static int f(List<Integer> xs) { xs.first() }
                    }''')],
        // Map.getOrDefault: ite over containsKey, lowered to value-or-default.
        [group: 'P39 idioms', name: 'm.getOrDefault picks the value when present', ok: true,
         src: tc('''class C {
                        @Requires({ m != null && m.containsKey("k") && m["k"] == 42 })
                        @Ensures({ result == 42 })
                        static int f(Map<String, Integer> m) { m.getOrDefault("k", 0) }
                    }''')],
        // Map.getOrDefault: returns default when key absent.
        [group: 'P39 idioms', name: 'm.getOrDefault picks default when key absent', ok: true,
         src: tc('''class C {
                        @Requires({ m != null && !m.containsKey("k") })
                        @Ensures({ result == 99 })
                        static int f(Map<String, Integer> m) { m.getOrDefault("k", 99) }
                    }''')],
        // xs.set(i, v) statement: mutates same as xs[i] = v. Use List<Integer> since arrays
        // don't have a .set() method on the Groovy/Java type system.
        [group: 'P39 idioms', name: 'xs.set(i, v) statement === xs[i] = v', ok: true,
         src: tc('''class C {
                        List<Integer> a
                        @Requires({ a != null && 0 <= k && k < a.size() })
                        @Modifies({ this.a })
                        @Ensures({ a[k] == v })
                        void put(int k, int v) { a.set(k, v) }
                    }''')],
        // xs.set frame: only the assigned index changes; other indices preserved by @Modifies.
        [group: 'P39 idioms', name: 'xs.set(i, v) preserves other indices', ok: true,
         src: tc('''class C {
                        List<Integer> a
                        @Requires({ a != null && 0 <= k && k < a.size() && j != k && 0 <= j && j < a.size() })
                        @Modifies({ this.a })
                        @Ensures({ a[j] == old.a[j] })
                        void put(int k, int v, int j) { a.set(k, v) }
                    }''')],
        // Factory fold: list literal .first() folds to the first arg.
        [group: 'P39 idioms', name: '[a, b, c].first() folds to literal', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 10 })
                        static int f() { [10, 20, 30].first() }
                    }''')],
        // Factory fold: list literal .last() folds to the last arg.
        [group: 'P39 idioms', name: '[a, b, c].last() folds to literal', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 30 })
                        static int f() { [10, 20, 30].last() }
                    }''')],

        // ---------- Phase 40: size-changing list mutation ----------
        // Append: xs.add(v) grows size by 1; the new last element is v.
        [group: 'P40 list mutation', name: 'xs.add(v): size grows by 1', ok: true,
         src: tc('''class C {
                        List<Integer> xs
                        @Requires({ xs != null })
                        @Modifies({ this.xs })
                        @Ensures({ xs.size() == old.xs.size() + 1 })
                        void push(int v) { xs.add(v) }
                    }''')],
        // Append: the appended value lives at the new last index.
        [group: 'P40 list mutation', name: 'xs.add(v): new last element is v', ok: true,
         src: tc('''class C {
                        List<Integer> xs
                        @Requires({ xs != null })
                        @Modifies({ this.xs })
                        @Ensures({ xs[old.xs.size()] == v })
                        void push(int v) { xs.add(v) }
                    }''')],
        // Soundness: claiming size grew by 2 from a single add refutes.
        [group: 'P40 list mutation', name: 'xs.add(v): wrong delta refutes',
         expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        List<Integer> xs
                        @Requires({ xs != null })
                        @Modifies({ this.xs })
                        @Ensures({ xs.size() == old.xs.size() + 2 })
                        void push(int v) { xs.add(v) }
                    }''')],
        // Frame: a non-modified element at index j < oldSize is unchanged.
        [group: 'P40 list mutation', name: 'xs.add(v) preserves earlier elements', ok: true,
         src: tc('''class C {
                        List<Integer> xs
                        @Requires({ xs != null && 0 <= j && j < xs.size() })
                        @Modifies({ this.xs })
                        @Ensures({ xs[j] == old.xs[j] })
                        void push(int v, int j) { xs.add(v) }
                    }''')],
        // Two adds chain: size grows by 2 (the expression composition lets the encoder track
        // sequential mutations without SSA naming).
        [group: 'P40 list mutation', name: 'two adds: size grows by 2', ok: true,
         src: tc('''class C {
                        List<Integer> xs
                        @Requires({ xs != null })
                        @Modifies({ this.xs })
                        @Ensures({ xs.size() == old.xs.size() + 2 })
                        void pushTwo(int a, int b) { xs.add(a); xs.add(b) }
                    }''')],
        // Clear: size goes to 0.
        [group: 'P40 list mutation', name: 'xs.clear() drops size to 0', ok: true,
         src: tc('''class C {
                        List<Integer> xs
                        @Requires({ xs != null })
                        @Modifies({ this.xs })
                        @Ensures({ xs.size() == 0 })
                        void reset() { xs.clear() }
                    }''')],
        // removeLast: with a guard, size shrinks by 1.
        [group: 'P40 list mutation', name: 'xs.removeLast() with guard: size shrinks by 1', ok: true,
         src: tc('''class C {
                        List<Integer> xs
                        @Requires({ xs != null && xs.size() > 0 })
                        @Modifies({ this.xs })
                        @Ensures({ xs.size() == old.xs.size() - 1 })
                        void popOne() { xs.removeLast() }
                    }''')],
        // pop is the Groovy alias for removeLast.
        [group: 'P40 list mutation', name: 'xs.pop() with guard: size shrinks by 1', ok: true,
         src: tc('''class C {
                        List<Integer> xs
                        @Requires({ xs != null && xs.size() > 0 })
                        @Modifies({ this.xs })
                        @Ensures({ xs.size() == old.xs.size() - 1 })
                        void popOne() { xs.pop() }
                    }''')],
        // Soundness: pop without a size guard refutes via the synthesised IndexSite obligation
        // ("0 < xs.size()") — same diagnostic shape as the bracket form would produce. Uses a
        // List parameter (rather than field) because the ObligationCollector's realVar check
        // currently only fires on parameter-resolved VariableExpressions; field-resolved access
        // is a known limit (the body-replay path still threads the mutation, but the implicit
        // bounds check at the call site is parameter-only).
        [group: 'P40 list mutation', name: 'xs.removeLast() without guard refutes',
         expect: 'IndexOutOfBoundsException',
         src: tc('''class C {
                        static void popOne(List<Integer> xs) { xs.removeLast() }
                    }''')],
        // Push-then-pop returns to the original size — composes both mutations.
        [group: 'P40 list mutation', name: 'add then removeLast: size restored', ok: true,
         src: tc('''class C {
                        List<Integer> xs
                        @Requires({ xs != null })
                        @Modifies({ this.xs })
                        @Ensures({ xs.size() == old.xs.size() })
                        void roundTrip(int v) { xs.add(v); xs.removeLast() }
                    }''')],
        // README Stack example anchor — push-pop preserves both size and count (the headline
        // Phase 41 win, narrated as a Stack class in the README "Lists — mutation" beat).
        [group: 'P40 list mutation', name: 'README Stack: roundTrip preserves count', ok: true,
         src: tc('''class Stack {
                        List<Integer> xs
                        @Requires({ xs != null })
                        @Modifies({ this.xs })
                        @Ensures({ xs.count(v) == old.xs.count(v) })
                        void roundTrip(int v) { xs.add(v); xs.removeLast() }
                    }''')],

        // ---------- Phase 41: bounded count tracking for lists ----------
        // Append of a matching element raises xs.count(v) by exactly one — the bounded-count
        // analogue of the per-store count law, asserted on the boundary slot oldSize.
        [group: 'P41 list bcount', name: 'xs.add(v) raises xs.count(v) by 1', ok: true,
         src: tc('''class C {
                        List<Integer> xs
                        @Requires({ xs != null })
                        @Modifies({ this.xs })
                        @Ensures({ xs.count(v) == old.xs.count(v) + 1 })
                        void push(int v) { xs.add(v) }
                    }''')],
        // Append of a non-matching element preserves the count.
        [group: 'P41 list bcount', name: 'xs.add(v) leaves xs.count(w) unchanged when v != w', ok: true,
         src: tc('''class C {
                        List<Integer> xs
                        @Requires({ xs != null && v != w })
                        @Modifies({ this.xs })
                        @Ensures({ xs.count(w) == old.xs.count(w) })
                        void push(int v, int w) { xs.add(v) }
                    }''')],
        // Soundness: claiming the wrong delta refutes — the bcount law is precise.
        [group: 'P41 list bcount', name: 'xs.add(v) wrong delta refutes',
         expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        List<Integer> xs
                        @Requires({ xs != null })
                        @Modifies({ this.xs })
                        @Ensures({ xs.count(v) == old.xs.count(v) + 2 })
                        void push(int v) { xs.add(v) }
                    }''')],
        // removeLast undoes the matching element's contribution.
        [group: 'P41 list bcount', name: 'removeLast of a matching tail decreases count by 1', ok: true,
         src: tc('''class C {
                        List<Integer> xs
                        @Requires({ xs != null && xs.size() > 0 && xs[xs.size() - 1] == v })
                        @Modifies({ this.xs })
                        @Ensures({ xs.count(v) == old.xs.count(v) - 1 })
                        void popOne(int v) { xs.removeLast() }
                    }''')],
        // Push-then-pop round-trips count — the headline win from Phase 41 (today it would
        // refute because the unbounded count grows by 1 on the push and doesn't shrink back).
        [group: 'P41 list bcount', name: 'push-then-pop preserves count', ok: true,
         src: tc('''class C {
                        List<Integer> xs
                        @Requires({ xs != null })
                        @Modifies({ this.xs })
                        @Ensures({ xs.count(v) == old.xs.count(v) })
                        void roundTrip(int v) { xs.add(v); xs.removeLast() }
                    }''')],
        // clear zeros every tracked count (the bcount-over-empty-range axiom asserted at clear time).
        [group: 'P41 list bcount', name: 'clear drops xs.count(v) to 0', ok: true,
         src: tc('''class C {
                        List<Integer> xs
                        @Requires({ xs != null })
                        @Modifies({ this.xs })
                        @Ensures({ xs.count(v) == 0 })
                        void reset(int v) { xs.clear() }
                    }''')],
        // Regression check: existing per-store count law on int[] arrays continues to use the
        // unbounded count (the permutation sort proofs rely on this). No change in behaviour.
        [group: 'P41 list bcount', name: 'int[] count law unchanged (regression anchor)', ok: true,
         src: tc('''class C {
                        int[] a
                        @Requires({ 0 <= k && k < a.length })
                        @Modifies({ this.a })
                        @Ensures({ a.count(v) == old.a.count(v) - (old.a[k] == v ? 1 : 0) + (newV == v ? 1 : 0) })
                        void put(int k, int newV, int v) { a[k] = newV }
                    }''')],

        // ---------- Phase 42: LemmaCall replay in implicit-obligation pass ----------
        // After xs.add(v), the implicit bounds check on xs[0] sees the new size — pre-Phase-42
        // the implicit pass didn't replay LemmaCalls so it would over-refute. The body-replay
        // and implicit-obligation passes now agree.
        [group: 'P42 mutation replay', name: 'add then in-bounds read passes implicit bounds', ok: true,
         src: tc('''class C {
                        @Requires({ xs != null })
                        static int firstAfterPush(List<Integer> xs, int v) {
                            xs.add(v)
                            xs[0]
                        }
                    }''')],
        // Same pattern but with xs.size() as the index — exercises the size oracle threading
        // through the implicit pass.
        [group: 'P42 mutation replay', name: 'add then xs[size-1] read passes bounds', ok: true,
         src: tc('''class C {
                        @Requires({ xs != null })
                        static int lastAfterPush(List<Integer> xs, int v) {
                            xs.add(v)
                            xs[xs.size() - 1]
                        }
                    }''')],
        // Two adds chain through the implicit pass too: after add(a); add(b), xs[1] is in bounds.
        [group: 'P42 mutation replay', name: 'two adds then xs[1] read passes bounds', ok: true,
         src: tc('''class C {
                        @Requires({ xs != null })
                        static int secondAfterPushTwo(List<Integer> xs, int a, int b) {
                            xs.add(a)
                            xs.add(b)
                            xs[1]
                        }
                    }''')],
        // Source-order preserved: a mutation BEFORE a guarded branch lets the branch's implicit
        // obligations see the post-mutation state.
        [group: 'P42 mutation replay', name: 'add then guarded read inside branch', ok: true,
         src: tc('''class C {
                        @Requires({ xs != null })
                        static int guardedAfterPush(List<Integer> xs, int v) {
                            xs.add(v)
                            if (xs.size() > 0) return xs[0]
                            return -1
                        }
                    }''')],
        // Soundness anchor: after removeLast, xs[oldSize-1] is out of bounds — the implicit pass
        // must see the size shrunk. Pre-Phase-42 it would have passed (size oracle unchanged from
        // the implicit-pass POV); post-Phase-42 it correctly refutes.
        [group: 'P42 mutation replay', name: 'removeLast then read at old-last refutes',
         expect: 'IndexOutOfBoundsException',
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() > 0 })
                        static int popThenRead(List<Integer> xs) {
                            int n = xs.size()
                            xs.removeLast()
                            xs[n - 1]
                        }
                    }''')],
        // Mutation effect on a downstream containsKey check.
        [group: 'P42 mutation replay', name: 'm.put then containsKey passes implicit check', ok: true,
         src: tc('''class C {
                        @Requires({ m != null })
                        @Ensures({ result == 1 })
                        static int putThenCheck(Map<String, Integer> m) {
                            m.put("k", 42)
                            m.containsKey("k") ? 1 : 0
                        }
                    }''')],

        // ---------- Phase 43: field-receiver bounds synthesis for runtime-throwing list shapes ----------
        // Soundness anchor: an unguarded removeLast on an instance FIELD refutes the same way
        // it does on a parameter. Pre-Phase-43 the synth only fired on parameter receivers, so
        // a field's pop-on-empty silently passed the implicit pass.
        [group: 'P43 field bounds', name: 'field removeLast without size guard refutes',
         expect: 'IndexOutOfBoundsException',
         src: tc('''class C {
                        List<Integer> xs
                        void popOne() { xs.removeLast() }
                    }''')],
        // Verify with size guard — the synthesised IndexSite discharges via the @Requires.
        [group: 'P43 field bounds', name: 'field removeLast with size guard verifies', ok: true,
         src: tc('''class C {
                        List<Integer> xs
                        @Requires({ xs != null && xs.size() > 0 })
                        @Modifies({ this.xs })
                        void popOne() { xs.removeLast() }
                    }''')],
        // Field xs.first() / xs.head() / xs.get(i) shapes also synthesise IndexSites — same
        // bounds check fires for the field as for a parameter.
        [group: 'P43 field bounds', name: 'field xs.first() without size guard refutes',
         expect: 'IndexOutOfBoundsException',
         src: tc('''class C {
                        List<Integer> xs
                        int headEl() { xs.first() }
                    }''')],
        [group: 'P43 field bounds', name: 'field xs.get(i) without bounds guard refutes',
         expect: 'IndexOutOfBoundsException',
         src: tc('''class C {
                        List<Integer> xs
                        int at(int i) { xs.get(i) }
                    }''')],
        // Soundness preserved: pop a known non-empty field, then read xs[0] — the IndexSite
        // fires at the read but discharges via the (post-pop) size oracle from Phase 42's replay.
        [group: 'P43 field bounds', name: 'field pop preserves implicit check downstream', ok: true,
         src: tc('''class C {
                        List<Integer> xs
                        @Requires({ xs != null && xs.size() > 1 })
                        @Modifies({ this.xs })
                        @Ensures({ xs.size() == old.xs.size() - 1 })
                        int popThenRead() { xs.removeLast(); xs[0] }
                    }''')],
        // Regression anchor: existing field-mutation calls that don't synthesise IndexSites
        // (xs.add, s.add, m.put) still verify without an explicit nullity guard.
        [group: 'P43 field bounds', name: 'field xs.add(v) unchanged (regression anchor)', ok: true,
         src: tc('''class C {
                        List<Integer> xs
                        @Modifies({ this.xs })
                        @Ensures({ xs.size() == old.xs.size() + 1 })
                        void push(int v) { xs.add(v) }
                    }''')],

        // ---------- Phase 44: opt-in 32-bit integer overflow checks (@CheckOverflow) ----------
        // Bounded inputs let the overflow obligation discharge.
        [group: 'P44 overflow', name: 'addition with bounded inputs verifies', ok: true,
         src: tc('''class C {
                        @CheckOverflow
                        @Requires({ a >= 0 && a < 1000 && b >= 0 && b < 1000 })
                        static int add(int a, int b) { a + b }
                    }''')],
        // Unguarded increment refutes — Z3 picks n = Integer.MAX_VALUE and the addition overflows.
        [group: 'P44 overflow', name: 'unguarded increment refutes',
         expect: 'addition overflows 32-bit signed range',
         src: tc('''class C {
                        @CheckOverflow
                        static int incr(int n) { n + 1 }
                    }''')],
        // Bound the input to make the increment safe. {@code Integer.MAX_VALUE} folds to the
        // literal 2147483647 via the JDK-range-constant peephole, so users can write the natural
        // spelling rather than the magic number.
        [group: 'P44 overflow', name: 'increment with Integer.MAX_VALUE bound verifies', ok: true,
         src: tc('''class C {
                        @CheckOverflow
                        @Requires({ n < Integer.MAX_VALUE })
                        static int incr(int n) { n + 1 }
                    }''')],
        // Same for Integer.MIN_VALUE on the negation side.
        [group: 'P44 overflow', name: 'subtraction with Integer.MIN_VALUE bound verifies', ok: true,
         src: tc('''class C {
                        @CheckOverflow
                        @Requires({ a > Integer.MIN_VALUE && b == 1 })
                        static int dec(int a, int b) { a - b }
                    }''')],
        // Unary minus overflow — -Integer.MIN_VALUE = 2147483648, one past INT_MAX.
        [group: 'P44 overflow', name: 'unary minus on unbounded int refutes',
         expect: 'negation overflows 32-bit signed range',
         src: tc('''class C {
                        @CheckOverflow
                        static int neg(int a) { -a }
                    }''')],
        // Guard against the only failing value (INT_MIN); negation then verifies.
        [group: 'P44 overflow', name: 'unary minus with guard verifies', ok: true,
         src: tc('''class C {
                        @CheckOverflow
                        @Requires({ a > Integer.MIN_VALUE })
                        static int neg(int a) { -a }
                    }''')],
        // Division overflow — the only arithmetic case where / overflows is INT_MIN / -1.
        // Unguarded refutes; Z3 picks the specific failure pair. Groovy promotes int/int to
        // BigDecimal at the source level, so the explicit (int) cast keeps the method's int
        // return type — but the inner BinaryExpression a/b is what the collector picks up.
        [group: 'P44 overflow', name: 'unguarded division refutes on INT_MIN / -1',
         expect: 'division overflows 32-bit signed range',
         src: tc('''class C {
                        @CheckOverflow
                        @Requires({ b != 0 })
                        static int div(int a, int b) { (int)(a / b) }
                    }''')],
        // Guard against either pair member; division verifies.
        [group: 'P44 overflow', name: 'division with guard verifies', ok: true,
         src: tc('''class C {
                        @CheckOverflow
                        @Requires({ b != 0 && !(a == Integer.MIN_VALUE && b == -1) })
                        static int div(int a, int b) { (int)(a / b) }
                    }''')],
        // % is unaffected — Java spec: Integer.MIN_VALUE % -1 == 0. (% returns int directly so no cast.)
        [group: 'P44 overflow', name: 'modulo never flagged for INT_MIN/-1', ok: true,
         src: tc('''class C {
                        @CheckOverflow
                        @Requires({ b != 0 })
                        static int mod(int a, int b) { a % b }
                    }''')],

        // ---------- Phase 45: cross-class @Invariant call-site assumption ----------
        // Headline: a class-typed parameter c carries Counter's invariant into the calling method.
        // Reading c.count under that invariant yields result >= 0 without any caller-side guard.
        [group: 'P45 cross-class', name: 'foreign invariant assumed at entry: c.count >= 0', ok: true,
         src: tc('''@Invariant({ count >= 0 && count <= max })
                    class Counter { int count, max }
                    @TypeChecked(extensions = 'verification.VerifyChecker')
                    class Client {
                        @Requires({ c != null })
                        @Ensures({ result >= 0 })
                        static int read(Counter c) { c.count }
                    }''')],
        // Sub-fields independent: c.count and c.max are distinct SMT entities (receiver-qualified).
        [group: 'P45 cross-class', name: 'foreign invariant: c.count <= c.max verifies', ok: true,
         src: tc('''@Invariant({ count >= 0 && count <= max })
                    class Counter { int count, max }
                    @TypeChecked(extensions = 'verification.VerifyChecker')
                    class Client {
                        @Requires({ c != null })
                        @Ensures({ result <= c.max })
                        static int read(Counter c) { c.count }
                    }''')],
        // Soundness anchor: claiming c.count > 0 isn't supported by the invariant (allows 0).
        [group: 'P45 cross-class', name: 'foreign invariant: stronger claim refutes',
         expect: 'Cannot prove postcondition',
         src: tc('''@Invariant({ count >= 0 && count <= max })
                    class Counter { int count, max }
                    @TypeChecked(extensions = 'verification.VerifyChecker')
                    class Client {
                        @Requires({ c != null })
                        @Ensures({ result > 0 })
                        static int read(Counter c) { c.count }
                    }''')],
        // Two class-typed receivers carry separate invariants and don't conflate.
        [group: 'P45 cross-class', name: 'two foreign receivers: invariants independent', ok: true,
         src: tc('''@Invariant({ count >= 0 })
                    class Counter { int count }
                    @TypeChecked(extensions = 'verification.VerifyChecker')
                    class Client {
                        @Requires({ a != null && b != null })
                        @Ensures({ result >= 0 })
                        static int sum(Counter a, Counter b) { a.count + b.count }
                    }''')],
        // Cross-class call effect: c.someVoid() havocs c's fields but reasserts the invariant,
        // so c.count >= 0 still holds afterwards.
        [group: 'P45 cross-class', name: 'after cross-class call: invariant still holds', ok: true,
         src: tc('''@Invariant({ count >= 0 && count <= max })
                    class Counter {
                        int count, max
                        @Requires({ count < max })
                        void incr() { count = count + 1 }
                    }
                    @TypeChecked(extensions = 'verification.VerifyChecker')
                    class Client {
                        @Requires({ c != null && c.count < c.max })
                        @Ensures({ result >= 0 })
                        static int useCounter(Counter c) {
                            c.incr()
                            c.count
                        }
                    }''')],
        // Cross-class @Requires discharge: caller must establish the callee's precondition under
        // receiver context. With c.count < c.max in the caller's @Requires, incr()'s @Requires
        // is discharged at the call site.
        [group: 'P45 cross-class', name: 'cross-class @Requires discharges from receiver context', ok: true,
         src: tc('''@Invariant({ count >= 0 && count <= max })
                    class Counter {
                        int count, max
                        @Requires({ count < max })
                        void incr() { count = count + 1 }
                    }
                    @TypeChecked(extensions = 'verification.VerifyChecker')
                    class Client {
                        @Requires({ c != null && c.count < c.max })
                        static int callIt(Counter c) {
                            c.incr()
                            0
                        }
                    }''')],
        // Soundness: without c.count < c.max in the caller's @Requires, the @Requires of
        // incr() can't be discharged — incr() is callable on a counter that's already at max.
        // The counterexample names the receiver-qualified fields: c$count = 0, c$max = 0.
        [group: 'P45 cross-class', name: 'cross-class @Requires without guard refutes',
         expect: 'Cannot prove precondition of incr',
         src: tc('''@Invariant({ count >= 0 && count <= max })
                    class Counter {
                        int count, max
                        @Requires({ count < max })
                        void incr() { count = count + 1 }
                    }
                    @TypeChecked(extensions = 'verification.VerifyChecker')
                    class Client {
                        @Requires({ c != null })
                        static int callIt(Counter c) {
                            c.incr()
                            0
                        }
                    }''')],
        // Subtraction overflow: a - b could underflow Integer.MIN_VALUE.
        [group: 'P44 overflow', name: 'unguarded subtraction refutes',
         expect: 'subtraction overflows 32-bit signed range',
         src: tc('''class C {
                        @CheckOverflow
                        static int sub(int a, int b) { a - b }
                    }''')],
        // Multiplication: a * b can overflow even for small magnitudes (50000 * 50000 = 2.5e9 > INT_MAX).
        [group: 'P44 overflow', name: 'multiplication with tight bounds verifies', ok: true,
         src: tc('''class C {
                        @CheckOverflow
                        @Requires({ a >= 0 && a < 10000 && b >= 0 && b < 10000 })
                        static int mul(int a, int b) { a * b }
                    }''')],
        [group: 'P44 overflow', name: 'multiplication with loose bounds refutes',
         expect: 'multiplication overflows 32-bit signed range',
         src: tc('''class C {
                        @CheckOverflow
                        @Requires({ a >= 0 && a < 100000 && b >= 0 && b < 100000 })
                        static int mul(int a, int b) { a * b }
                    }''')],
        // Sub-expression aware: (a+1)*(a+1) emits two obligations — inner add and outer mul.
        // The outer mul refutes for a near sqrt(INT_MAX) ≈ 46341.
        [group: 'P44 overflow', name: 'sub-expression: nested op refutes',
         expect: 'multiplication overflows 32-bit signed range',
         src: tc('''class C {
                        @CheckOverflow
                        @Requires({ a >= 0 && a < 1_000_000 })
                        static int sq1(int a) { (a + 1) * (a + 1) }
                    }''')],
        // Class-level @CheckOverflow propagates to every method.
        [group: 'P44 overflow', name: 'class-level @CheckOverflow propagates',
         expect: 'addition overflows 32-bit signed range',
         src: tc('''@CheckOverflow
                    class C {
                        static int incr(int n) { n + 1 }
                    }''')],
        // Regression anchor: without @CheckOverflow, the same method verifies as math-int.
        // This guards the default-math-int experience for all existing code.
        [group: 'P44 overflow', name: 'no @CheckOverflow: math-int default unchanged', ok: true,
         src: tc('''class C {
                        @Ensures({ result == a + b })
                        static int add(int a, int b) { a + b }
                    }''')],
        // Phase 44c — implicit size upper bound. A method that indexes xs[i + 1] for i in
        // [0, xs.size()-1) can't overflow into a wrap-around index, because xs.size() ≤ INT_MAX
        // is asserted on the size oracle. Verified WITHOUT @CheckOverflow — this closes a
        // small soundness gap unconditionally.
        [group: 'P44 overflow', name: 'index arithmetic never overflows (implicit size bound)', ok: true,
         src: tc('''class C {
                        @Requires({ 0 <= i && i + 1 < a.length })
                        static int pair(int[] a, int i) { a[i] + a[i + 1] }
                    }''')],

        // README Counter example — confirm the constructor-refute diagnostic shape used in docs.
        [group: 'README counter', name: 'Counter without @Requires refutes at construction',
         expect: 'Cannot prove class invariant',
         src: tc('''@groovy.contracts.Invariant({ count >= 0 && count <= max })
                    class Counter {
                        int count, max
                        Counter(int m) { max = m }
                        @Requires({ count < max })
                        void increment() { count = count + 1 }
                    }''')],

        // ---------- Phase 28: enum.values().length folds to a ground int ----------
        // Body context (post-resolution ClassExpression): the method returns the count, the
        // @Ensures matches the folded literal.
        [group: 'P28 enum.values', name: 'body returns Color.values().length, verifies', ok: true,
         src: tc('''class C {
                        enum Color { RED, BLUE, GREEN }
                        @Ensures({ result == 3 })
                        static int numColors() { Color.values().length }
                    }''')],
        // Soundness: wrong expected count refutes.
        [group: 'P28 enum.values', name: 'wrong count refuted',
         expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        enum Color { RED, BLUE, GREEN }
                        @Ensures({ result == 4 })
                        static int numColors() { Color.values().length }
                    }''')],
        // .size() form folds the same way as .length — in both body and contract positions.
        [group: 'P28 enum.values', name: 'size() form folds in body', ok: true,
         src: tc('''class C {
                        enum Color { RED, BLUE, GREEN }
                        @Ensures({ result == 3 })
                        static int numColors() { Color.values().size() }
                    }''')],
        [group: 'P28 enum.values', name: 'size() form folds in contract', ok: true,
         src: tc('''class C {
                        enum Color { RED, BLUE, GREEN }
                        @Requires({ k < Color.values().size() })
                        @Ensures({ k <= 2 })
                        static int safe(int k) { k }
                    }''')],
        // Contract-side use (re-parsed VariableExpression receiver). Looks the enum up by name in
        // the enumDomainSizes map populated by VerifyChecker, folds to 3.
        [group: 'P28 enum.values', name: '@Requires uses folded count', ok: true,
         src: tc('''class C {
                        enum Color { RED, BLUE, GREEN }
                        @Requires({ k < Color.values().length })
                        @Ensures({ k <= 2 })
                        static int safe(int k) { k }
                    }''')],
        // Bounded iteration over the enum domain: the upper bound folds to a literal, so the
        // every-quantifier's range is concrete.
        [group: 'P28 enum.values', name: 'bounded iteration over enum domain', ok: true,
         src: tc('''class C {
                        enum Color { RED, BLUE, GREEN }
                        @Requires({ (0..<Color.values().length).every { it >= 0 } })
                        @Ensures({ result == 3 })
                        static int numColors() { Color.values().length }
                    }''')],

        // ---------- Phase 16: finite sets (characteristic array + cardinality law) ----------
        // Membership assumed entails membership — `x in s` over a Set parameter (the read side).
        [group: 'P16 sets', name: 'membership assumed entails membership', ok: true,
         src: tc('class C { @Requires({ x in s }) @Ensures({ x in s }) static int f(Set<Integer> s, int x) { 0 } }')],
        // Not vacuous: with nothing assumed, membership cannot be proved.
        [group: 'P16 sets', name: 'unproven membership refuted', expect: 'Cannot prove postcondition',
         src: tc('class C { @Ensures({ x in s }) static int f(Set<Integer> s, int x) { 0 } }')],
        // `s.contains(x)` is the method spelling of the same membership.
        [group: 'P16 sets', name: 'contains is membership', ok: true,
         src: tc('class C { @Requires({ s.contains(x) }) @Ensures({ x in s }) static int f(Set<Integer> s, int x) { 0 } }')],
        // add makes the element a member — the post-state read rides Z3 array theory (store then select).
        [group: 'P16 sets', name: 'add makes element a member', ok: true,
         src: tc('''class C { Set<Integer> s
                        @Modifies({ this.s })
                        @Ensures({ x in s })
                        void put(int x) { s.add(x) }
                    }''')],
        // Cardinality law (headline): adding an element NOT already present grows the size by one.
        [group: 'P16 sets', name: 'add of new element grows size by one', ok: true,
         src: tc('''class C { Set<Integer> s
                        @Requires({ x !in s })
                        @Modifies({ this.s })
                        @Ensures({ s.size() == old.s.size() + 1 })
                        void put(int x) { s.add(x) }
                    }''')],
        // Soundness: without knowing x is new, the +1 cannot be claimed (x may already be present).
        [group: 'P16 sets', name: 'add without freshness refutes +1', expect: 'Cannot prove postcondition',
         src: tc('''class C { Set<Integer> s
                        @Modifies({ this.s })
                        @Ensures({ s.size() == old.s.size() + 1 })
                        void put(int x) { s.add(x) }
                    }''')],
        // Adding an element already present leaves the size unchanged.
        [group: 'P16 sets', name: 'add of present element keeps size', ok: true,
         src: tc('''class C { Set<Integer> s
                        @Requires({ x in s })
                        @Modifies({ this.s })
                        @Ensures({ s.size() == old.s.size() })
                        void put(int x) { s.add(x) }
                    }''')],
        // remove of a present element shrinks the size by one.
        [group: 'P16 sets', name: 'remove of present element shrinks size', ok: true,
         src: tc('''class C { Set<Integer> s
                        @Requires({ x in s })
                        @Modifies({ this.s })
                        @Ensures({ s.size() == old.s.size() - 1 })
                        void drop(int x) { s.remove(x) }
                    }''')],
        // An undeclared set mutation violates a pure (@Modifies({})) frame — caught like an array store.
        [group: 'P16 sets', name: 'undeclared set write refuted', expect: 'not in its @Modifies',
         src: tc('''class C { Set<Integer> s
                        @Modifies({ [] })
                        void touch(int x) { s.add(x) }
                    }''')],
        // A set operation needing an unbounded quantifier (containsAll/subset) is a loud skip, not a pass.
        [group: 'P16 sets', name: 'subset op outside fragment skipped', expect: 'Skipped verification of postcondition',
         src: tc('class C { @Requires({ s.containsAll(t) }) @Ensures({ s.containsAll(t) }) static int f(Set<Integer> s, Set<Integer> t) { 0 } }')],
        // The cardinality law wired into a recursive @Decreases measure: each call adds a *fresh* element
        // to `s` (the guard `x !in s` makes it fresh), so the measure `n - s.size()` strictly decreases —
        // a finite recursion over a bounded domain (the DFS-shaped termination argument), proved with no
        // quantifier. Termination + the recursion's own well-foundedness, end to end.
        [group: 'P16 sets', name: 'set-cardinality decreases measure', ok: true,
         src: tc('''class C { Set<Integer> s; int n
                        @Modifies({ this.s })
                        @Decreases({ n - s.size() })
                        void fill(int x) {
                            if (x !in s && s.size() < n) {
                                s.add(x)
                                fill(x + 1)
                            }
                        }
                    }''')],
        // Soundness: drop the freshness guard `x !in s` and the added element may already be present,
        // so `s.size()` need not grow — the measure does not provably decrease → termination refuted.
        [group: 'P16 sets', name: 'non-fresh add does not decrease measure', expect: 'recursion measure',
         src: tc('''class C { Set<Integer> s; int n
                        @Modifies({ this.s })
                        @Decreases({ n - s.size() })
                        void fill(int x) {
                            if (s.size() < n) {
                                s.add(x)
                                fill(x + 1)
                            }
                        }
                    }''')],

        // ---------- Phase 17: finite maps (value array + key-set) ----------
        // put then read: m.put(k, v) makes m[k] == v (value store, read back via array theory).
        [group: 'P17 maps', name: 'put then get value', ok: true,
         src: tc('''class C { Map<Integer,Integer> m
                        @Modifies({ this.m })
                        @Ensures({ m[k] == v })
                        void put(int k, int v) { m.put(k, v) }
                    }''')],
        // The subscript spelling m[k] = v is the same value store.
        [group: 'P17 maps', name: 'subscript store then read', ok: true,
         src: tc('''class C { Map<Integer,Integer> m
                        @Ensures({ m[k] == v })
                        void set(int k, int v) { m[k] = v }
                    }''')],
        // put adds the key to the domain — m.containsKey(k) holds afterwards.
        [group: 'P17 maps', name: 'put adds the key', ok: true,
         src: tc('''class C { Map<Integer,Integer> m
                        @Modifies({ this.m })
                        @Ensures({ m.containsKey(k) })
                        void put(int k, int v) { m.put(k, v) }
                    }''')],
        // Value frame: a put at key k leaves every other key's value unchanged (array theory, j != k).
        [group: 'P17 maps', name: 'put frames other keys', ok: true,
         src: tc('''class C { Map<Integer,Integer> m
                        @Requires({ j != k })
                        @Modifies({ this.m })
                        @Ensures({ m[j] == old.m[j] })
                        void put(int k, int v, int j) { m.put(k, v) }
                    }''')],
        // Key-set cardinality law: putting a NEW key grows the size by one.
        [group: 'P17 maps', name: 'put of new key grows size by one', ok: true,
         src: tc('''class C { Map<Integer,Integer> m
                        @Requires({ !m.containsKey(k) })
                        @Modifies({ this.m })
                        @Ensures({ m.size() == old.m.size() + 1 })
                        void put(int k, int v) { m.put(k, v) }
                    }''')],
        // Soundness: without knowing k is a new key, the +1 cannot be claimed (k may already be present).
        [group: 'P17 maps', name: 'put without fresh key refutes +1', expect: 'Cannot prove postcondition',
         src: tc('''class C { Map<Integer,Integer> m
                        @Modifies({ this.m })
                        @Ensures({ m.size() == old.m.size() + 1 })
                        void put(int k, int v) { m.put(k, v) }
                    }''')],
        // Key membership: `k in m` is m.containsKey(k); assumed entails itself.
        [group: 'P17 maps', name: 'key membership assumed entails', ok: true,
         src: tc('class C { @Requires({ k in m }) @Ensures({ m.containsKey(k) }) static int f(Map<Integer,Integer> m, int k) { 0 } }')],
        // The key-set cardinality law wired into a recursive @Decreases measure — DFS-shaped termination
        // over a map's key domain (each call inserts a fresh key, so `n - m.size()` strictly decreases).
        [group: 'P17 maps', name: 'map-size decreases measure', ok: true,
         src: tc('''class C { Map<Integer,Integer> m; int n
                        @Modifies({ this.m })
                        @Decreases({ n - m.size() })
                        void fill(int k) {
                            if (!m.containsKey(k) && m.size() < n) {
                                m.put(k, k)
                                fill(k + 1)
                            }
                        }
                    }''')],
        // Soundness: drop the fresh-key guard and the size need not grow → measure not decreasing → refuted.
        [group: 'P17 maps', name: 'non-fresh put does not decrease measure', expect: 'recursion measure',
         src: tc('''class C { Map<Integer,Integer> m; int n
                        @Modifies({ this.m })
                        @Decreases({ n - m.size() })
                        void fill(int k) {
                            if (m.size() < n) {
                                m.put(k, k)
                                fill(k + 1)
                            }
                        }
                    }''')],
        // An undeclared map put violates a pure (@Modifies({})) frame.
        [group: 'P17 maps', name: 'undeclared map write refuted', expect: 'not in its @Modifies',
         src: tc('''class C { Map<Integer,Integer> m
                        @Modifies({ [] })
                        void touch(int k, int v) { m.put(k, v) }
                    }''')],
        // A map operation needing an unbounded quantifier (containsValue) is a loud skip, not a pass.
        [group: 'P17 maps', name: 'containsValue outside fragment skipped', expect: 'Skipped verification of postcondition',
         src: tc('class C { @Requires({ m.containsValue(v) }) @Ensures({ m.containsValue(v) }) static int f(Map<Integer,Integer> m, int v) { 0 } }')],

        // ---------- Phase 18: reachability — a recursive graph traversal over a Set<Node> ----------
        // A DFS on a functional graph (`next` is a Map<Node,Node> successor) marking nodes in a Set.
        // Fuel-bounded so termination is a plain int measure; the reachability postcondition proves BOTH
        // halves the fragment can soundly express: (1) SOUNDNESS — visited only grows (every previously
        // visited node stays visited), a bounded universal over the node domain; (2) PROGRESS — the node
        // handed in ends visited (while fuel remained). Composes sets, maps, induction, caller-side set
        // framing (the recursive call havocs `visited` and reframes it from the callee's @Ensures), and
        // bounded quantifiers — no new machinery.
        [group: 'P18 reachability', name: 'fuel DFS: visited grows AND node covered', ok: true,
         src: tc('''class C {
                        Map<Integer,Integer> next
                        Set<Integer> visited
                        int n
                        @Requires({ 0 <= u && u < n && (0..<n).every { 0 <= next[it] && next[it] < n } })
                        @Modifies({ this.visited })
                        @Decreases({ fuel })
                        @Ensures({ (0..<n).every { (it in old.visited) ==> (it in visited) } &&
                                   (fuel <= 0 || (u in visited)) })
                        void visit(int u, int fuel) {
                            if (fuel > 0 && u !in visited) {
                                visited.add(u)
                                visit(next[u], fuel - 1)
                            }
                        }
                    }''')],
        // Soundness anchor: claiming the node is visited UNCONDITIONALLY (dropping the `fuel <= 0 ||`
        // guard) is false — when fuel runs out the base case adds nothing — so it refutes. This is the
        // honest boundary: progress is conditional on the termination budget.
        [group: 'P18 reachability', name: 'unconditional coverage refuted', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        Map<Integer,Integer> next
                        Set<Integer> visited
                        int n
                        @Requires({ 0 <= u && u < n && (0..<n).every { 0 <= next[it] && next[it] < n } })
                        @Modifies({ this.visited })
                        @Decreases({ fuel })
                        @Ensures({ u in visited })
                        void visit(int u, int fuel) {
                            if (fuel > 0 && u !in visited) {
                                visited.add(u)
                                visit(next[u], fuel - 1)
                            }
                        }
                    }''')],
        // The same SOUNDNESS half under the set-cardinality termination measure (`n - visited.size()`):
        // the visited-only-grows reachability postcondition, proved with the DFS-shaped cardinality
        // @Decreases rather than a fuel counter (the size guard supplies the measure's lower bound).
        [group: 'P18 reachability', name: 'cardinality DFS: visited only grows', ok: true,
         src: tc('''class C {
                        Map<Integer,Integer> next
                        Set<Integer> visited
                        int n
                        @Requires({ 0 <= u && u < n && (0..<n).every { 0 <= next[it] && next[it] < n } })
                        @Modifies({ this.visited })
                        @Decreases({ n - visited.size() })
                        @Ensures({ (0..<n).every { (it in old.visited) ==> (it in visited) } })
                        void visit(int u) {
                            if (u !in visited && visited.size() < n) {
                                visited.add(u)
                                visit(next[u])
                            }
                        }
                    }''')],
        // Soundness: a traversal that REMOVES a node breaks monotonic growth → refuted.
        [group: 'P18 reachability', name: 'removal breaks monotonic growth', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        Map<Integer,Integer> next
                        Set<Integer> visited
                        int n
                        @Requires({ 0 <= u && u < n && (0..<n).every { 0 <= next[it] && next[it] < n } })
                        @Modifies({ this.visited })
                        @Decreases({ fuel })
                        @Ensures({ (0..<n).every { (it in old.visited) ==> (it in visited) } })
                        void visit(int u, int fuel) {
                            if (fuel > 0 && (u in visited)) {
                                visited.remove(u)
                                visit(next[u], fuel - 1)
                            }
                        }
                    }''')],

        // ---------- Phase 19: the cardinality axiom — pigeonhole over a bounded domain ----------
        // Sets.boundedBy(s, n) ≜ s ⊆ [0,n): |s| <= n, and full iff it covers the domain. This is the
        // bridge the uninterpreted cardinality (Phase 16) lacked — relating |s| to actual membership.
        // FULL ⟹ MEMBER: a bounded set of size n contains every node of the domain (pigeonhole).
        [group: 'P19 cardinality', name: 'full bounded set covers the domain', ok: true,
         src: tc('''class C {
                        @Requires({ Sets.boundedBy(s, n) && s.size() == n && 0 <= u && u < n })
                        @Ensures({ u in s })
                        static int f(Set<Integer> s, int n, int u) { 0 }
                    }''')],
        // Soundness: without Sets.boundedBy there is no link from size to membership → cannot conclude u in s.
        [group: 'P19 cardinality', name: 'coverage needs the bound (refuted)', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Requires({ s.size() == n && 0 <= u && u < n })
                        @Ensures({ u in s })
                        static int f(Set<Integer> s, int n, int u) { 0 }
                    }''')],
        // The size bound itself: a domain-bounded set has at most n elements.
        [group: 'P19 cardinality', name: 'bounded set size is at most n', ok: true,
         src: tc('''class C {
                        @Requires({ Sets.boundedBy(s, n) })
                        @Ensures({ s.size() <= n })
                        static int f(Set<Integer> s, int n) { 0 }
                    }''')],
        // HOLE ⟹ NOT FULL: a bounded set missing a domain element has size < n — exactly the fact a
        // cardinality-terminating DFS needs at its coverage branch (an unvisited in-domain node ⟹ room remains).
        [group: 'P19 cardinality', name: 'a hole means the set is not full', ok: true,
         src: tc('''class C {
                        @Requires({ Sets.boundedBy(s, n) && 0 <= u && u < n && u !in s })
                        @Ensures({ s.size() < n })
                        static int f(Set<Integer> s, int n, int u) { 0 }
                    }''')],
        // Soundness: without the bound, a missing element says nothing about the (uninterpreted) size.
        [group: 'P19 cardinality', name: 'hole needs the bound (refuted)', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Requires({ 0 <= u && u < n && u !in s })
                        @Ensures({ s.size() < n })
                        static int f(Set<Integer> s, int n, int u) { 0 }
                    }''')],

        // ---------- Phase 20: bcount — the bounded-sum cardinality, properties earned by induction ----------
        // bcount(s, k) = Σ_{i<k} (i ∈ s ? 1 : 0): the genuine count of s's members in [0, k), written as
        // an ordinary recursive method. Its defining BOUND — 0 <= bcount(s,k) <= k — is the converse
        // counting the uninterpreted `card` lacked, and the framework proves it by its OWN induction
        // (@Decreases on k, self-@Ensures as the inductive hypothesis) — no built-in axiom.
        [group: 'P20 bcount', name: 'bound lemma: 0 <= bcount(s,k) <= k', ok: true,
         src: tc('''class C {
                        @Requires({ k >= 0 })
                        @Ensures({ 0 <= result && result <= k })
                        @Decreases({ k })
                        static int bcount(Set<Integer> s, int k) {
                            if (k == 0) return 0
                            int rest = bcount(s, k - 1)
                            return rest + ((k - 1) in s ? 1 : 0)
                        }
                    }''')],
        // FULL ⇒ COUNT = k: if every node of [0,k) is in s, the bounded count is exactly k. This ties the
        // count to actual membership (the direction `Sets.boundedBy`'s pigeonhole gives), proved by induction
        // — the recursion's @Requires `(0..<k-1).every{...}` follows from the caller's over [0,k).
        [group: 'P20 bcount', name: 'full domain ⇒ bcount(s,k) == k', ok: true,
         src: tc('''class C {
                        @Requires({ k >= 0 && (0..<k).every { it in s } })
                        @Ensures({ result == k })
                        @Decreases({ k })
                        static int bcount(Set<Integer> s, int k) {
                            if (k == 0) return 0
                            int rest = bcount(s, k - 1)
                            return rest + ((k - 1) in s ? 1 : 0)
                        }
                    }''')],
        // Soundness: the bound is earned, not assumed — a body that over-counts (rest + 2) breaks `<= k`.
        [group: 'P20 bcount', name: 'over-counting breaks the bound', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Requires({ k >= 0 })
                        @Ensures({ 0 <= result && result <= k })
                        @Decreases({ k })
                        static int bcount(Set<Integer> s, int k) {
                            if (k == 0) return 0
                            int rest = bcount(s, k - 1)
                            return rest + 2
                        }
                    }''')],

        // ---------- Phase 21: the bcount per-add law (Sets.boundedCount as a primitive) ----------
        // Sets.boundedCount(s, k) is the bounded count as a primitive, carrying its bound axiom and a per-mutation
        // law. Adding a FRESH, in-domain element raises the count by exactly one — the bcount analogue of
        // the per-store `count` law, now threading the count across a set mutation.
        [group: 'P21 bcount law', name: 'fresh in-domain add increments count', ok: true,
         src: tc('''class C { Set<Integer> s
                        @Requires({ 0 <= u && u < k && u !in s })
                        @Modifies({ this.s })
                        @Ensures({ Sets.boundedCount(s, k) == Sets.boundedCount(old.s, k) + 1 })
                        void put(int u, int k) { s.add(u) }
                    }''')],
        // Soundness: drop the freshness guard and the count need not grow (u may already be present).
        [group: 'P21 bcount law', name: 'non-fresh add refutes +1', expect: 'Cannot prove postcondition',
         src: tc('''class C { Set<Integer> s
                        @Requires({ 0 <= u && u < k })
                        @Modifies({ this.s })
                        @Ensures({ Sets.boundedCount(s, k) == Sets.boundedCount(old.s, k) + 1 })
                        void put(int u, int k) { s.add(u) }
                    }''')],
        // The domain guard matters: adding an element OUTSIDE [0,k) leaves the bounded count unchanged.
        [group: 'P21 bcount law', name: 'out-of-domain add keeps count', ok: true,
         src: tc('''class C { Set<Integer> s
                        @Requires({ u >= k })
                        @Modifies({ this.s })
                        @Ensures({ Sets.boundedCount(s, k) == Sets.boundedCount(old.s, k) })
                        void put(int u, int k) { s.add(u) }
                    }''')],
        // Remove of a present, in-domain element drops the bounded count by one.
        [group: 'P21 bcount law', name: 'in-domain remove decrements count', ok: true,
         src: tc('''class C { Set<Integer> s
                        @Requires({ 0 <= u && u < k && (u in s) })
                        @Modifies({ this.s })
                        @Ensures({ Sets.boundedCount(s, k) == Sets.boundedCount(old.s, k) - 1 })
                        void drop(int u, int k) { s.remove(u) }
                    }''')],
        // The bound axiom rides the primitive: a domain-bounded count never exceeds its bound.
        [group: 'P21 bcount law', name: 'primitive count carries its bound', ok: true,
         src: tc('''class C {
                        @Requires({ k >= 0 })
                        @Ensures({ 0 <= Sets.boundedCount(s, k) && Sets.boundedCount(s, k) <= k })
                        static int f(Set<Integer> s, int k) { 0 }
                    }''')],

        // ---------- Phase 22: the full-characterization axiom + end-to-end DFS coverage ----------
        // Sets.boundedCount(s,k) == k  ⟺  s covers [0,k). COUNT FULL ⇒ COVERS: a count of k over a k-slot domain
        // forces every node in — the converse of Phase 20's full ⇒ count, and the fact DFS needs.
        [group: 'P22 full-char', name: 'count == k ⇒ every domain node is in', ok: true,
         src: tc('''class C {
                        @Requires({ Sets.boundedCount(s, k) == k && 0 <= u && u < k })
                        @Ensures({ u in s })
                        static int f(Set<Integer> s, int k, int u) { 0 }
                    }''')],
        // COVERS ⇒ COUNT FULL: the other direction also holds from the primitive's axiom.
        [group: 'P22 full-char', name: 'covers domain ⇒ count == k', ok: true,
         src: tc('''class C {
                        @Requires({ k >= 0 && (0..<k).every { it in s } })
                        @Ensures({ Sets.boundedCount(s, k) == k })
                        static int f(Set<Integer> s, int k) { 0 }
                    }''')],
        // Soundness: full count says nothing about a node OUTSIDE the domain [0,k).
        [group: 'P22 full-char', name: 'coverage is only within the domain (refuted)', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Requires({ Sets.boundedCount(s, k) == k && u >= k })
                        @Ensures({ u in s })
                        static int f(Set<Integer> s, int k, int u) { 0 }
                    }''')],
        // THE CAPSTONE: a cardinality-terminating DFS proves UNCONDITIONAL coverage — the node handed in
        // ends visited, with no fuel bound. Termination is `n - Sets.boundedCount(visited, n)` (the per-add law
        // makes it strictly decrease on a fresh add); coverage closes because at the "set full" branch the
        // full-characterization forces the node in. Composes sets, maps, induction, set framing, bounded
        // quantifiers, the per-add law and the full-characterization into the DFS soundness property.
        [group: 'P22 full-char', name: 'DFS: unconditional coverage (start in visited)', ok: true,
         src: tc('''class C {
                        Map<Integer,Integer> next
                        Set<Integer> visited
                        int n
                        @Requires({ 0 <= u && u < n && (0..<n).every { 0 <= next[it] && next[it] < n } })
                        @Modifies({ this.visited })
                        @Decreases({ n - Sets.boundedCount(visited, n) })
                        @Ensures({ (u in visited) &&
                                   (0..<n).every { (it in old.visited) ==> (it in visited) } })
                        void visit(int u) {
                            if (u !in visited && Sets.boundedCount(visited, n) < n) {
                                visited.add(u)
                                visit(next[u])
                            }
                        }
                    }''')],
        // The honest boundary, made concrete: we prove the node itself is covered, NOT its successors —
        // claiming `next[u] in visited` refutes (a node visited earlier needn't have had its edge followed;
        // that is the closure/completeness gap, which needs the frontier/stack invariant).
        [group: 'P22 full-char', name: 'DFS: successor-covered is NOT proved (boundary)', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        Map<Integer,Integer> next
                        Set<Integer> visited
                        int n
                        @Requires({ 0 <= u && u < n && (0..<n).every { 0 <= next[it] && next[it] < n } })
                        @Modifies({ this.visited })
                        @Decreases({ n - Sets.boundedCount(visited, n) })
                        @Ensures({ next[u] in visited })
                        void visit(int u) {
                            if (u !in visited && Sets.boundedCount(visited, n) < n) {
                                visited.add(u)
                                visit(next[u])
                            }
                        }
                    }''')],

        // ---------- Phase 23: completeness — closure ⇒ reachable-covered, and the stack obstacle ----------
        // "visited is closed under next" — (0..<n).every { it∈visited ⟹ next[it]∈visited } — is the
        // completeness invariant. (b) closure ⇒ reachable-covered is provable; (a) DFS establishing closure
        // is the hard half (the stack). First, the one-step consequence: a closed set covers each successor.
        [group: 'P23 completeness', name: 'closure ⇒ successor covered (one step)', ok: true,
         src: tc('''class C {
                        Map<Integer,Integer> next
                        Set<Integer> visited
                        int n
                        @Requires({ 0 <= u && u < n && (u in visited) &&
                                    (0..<n).every { 0 <= next[it] && next[it] < n } &&
                                    (0..<n).every { (it in visited) ==> (next[it] in visited) } })
                        @Ensures({ next[u] in visited })
                        int f(int u) { 0 }
                    }''')],
        // (a) the obstacle, pinned cleanly via checkPath: simply MARKING a node breaks closure — the added
        // node's successor need not be visited yet. So closure is not preserved by a mark, which is exactly
        // why mark-then-recurse DFS cannot carry it as an invariant and completeness needs the frontier/stack
        // invariant (closure holds for everything *except nodes on the stack*). Refutes with a concrete u.
        [group: 'P23 completeness', name: 'marking a node breaks closure (boundary)', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        Map<Integer,Integer> next
                        Set<Integer> visited
                        int n
                        @Requires({ 0 <= u && u < n &&
                                    (0..<n).every { 0 <= next[it] && next[it] < n } &&
                                    (0..<n).every { (it in visited) ==> (next[it] in visited) } })
                        @Modifies({ this.visited })
                        @Ensures({ (0..<n).every { (it in visited) ==> (next[it] in visited) } })
                        void mark(int u) { visited.add(u) }
                    }''')],
        // Phase 24 (call-site soundness): a recursive closure-threading DFS now REFUTES at the recursive
        // call. After `visited.add(u)`, the callee's closure precondition is checked against the post-add
        // set (closure broken at u), not the entry set. Before the fix this passed *spuriously* (the
        // intervening mutation wasn't threaded, and the formal/caller `u` were conflated).
        [group: 'P24 call-site', name: 'closure precondition is checked post-mutation', expect: 'Cannot prove precondition',
         src: tc('''class C {
                        Map<Integer,Integer> next
                        Set<Integer> visited
                        int n
                        @Requires({ 0 <= u && u < n &&
                                    (0..<n).every { 0 <= next[it] && next[it] < n } &&
                                    (0..<n).every { (it in visited) ==> (next[it] in visited) } })
                        @Modifies({ this.visited })
                        @Decreases({ n - Sets.boundedCount(visited, n) })
                        @Ensures({ (0..<n).every { (it in visited) ==> (next[it] in visited) } })
                        void visit(int u) {
                            if (u !in visited && Sets.boundedCount(visited, n) < n) {
                                visited.add(u)
                                visit(next[u])
                            }
                        }
                    }''')],
        // A straight-line mutation before a call is threaded: needs(s, k) requires `k in s`, and
        // `s.add(k)` right before the call establishes it — verified only because the add is now replayed.
        [group: 'P24 call-site', name: 'mutation before call establishes precondition', ok: true,
         src: tc('''class C { Set<Integer> s
                        @Requires({ k in s })
                        void needs(int k) { }
                        @Modifies({ this.s })
                        void go(int k) { s.add(k); needs(k) }
                    }''')],
        // Soundness: without the add, the precondition isn't established → refuted (the threading is precise,
        // not vacuous).
        [group: 'P24 call-site', name: 'no mutation, precondition unmet', expect: 'Cannot prove precondition',
         src: tc('''class C { Set<Integer> s
                        @Requires({ k in s })
                        void needs(int k) { }
                        void go(int k) { needs(k) }
                    }''')],
        // Early-return narrowing: `if (k <= 0) return` before the call supplies `k > 0`, so callee's
        // @Requires({ k > 0 }) holds — a fact PathFacts (enclosing-if only) could not provide.
        [group: 'P24 call-site', name: 'early-return narrows the path', ok: true,
         src: tc('''class C {
                        @Requires({ k > 0 })
                        static int pos(int k) { k }
                        static int f(int k) {
                            if (k <= 0) return 0
                            return pos(k)
                        }
                    }''')],

        // ---------- Phase 25: recursive definitions in contracts (the defining-equation upgrade) ----------
        // A recursive contract-free function in a contract is now a shared symbol `f#(args)` carrying its
        // DEFINING EQUATION (bounded depth), so its definition is visible across a lemma boundary — where the
        // old inline-the-body unfolding produced unequal terms at different fuel depths and the induction
        // could not close. (1) COMPLETENESS, full: closure ⇒ EVERY node reachable from a visited node is
        // visited — the inductive `propagate` over the chain `chain(u,d)` (d-step successor) that previously
        // failed. This completes the (b) half flagged in Phase 23.
        [group: 'P25 recursive-defs', name: 'closure ⇒ d-step reachable covered (induction)', ok: true,
         src: tc('''class C {
                        Map<Integer,Integer> next
                        Set<Integer> visited
                        int n
                        int chain(int u, int d) { d <= 0 ? u : chain(next[u], d - 1) }
                        @Requires({ d >= 0 && 0 <= u && u < n && (u in visited) &&
                                    (0..<n).every { 0 <= next[it] && next[it] < n } &&
                                    (0..<n).every { (it in visited) ==> (next[it] in visited) } })
                        @Ensures({ chain(u, d) in visited })
                        @Decreases({ d })
                        void propagate(int u, int d) {
                            if (d > 0) propagate(next[u], d - 1)
                        }
                    }''')],
        // (2) bcount cross-lemma: a single-expression `bcount` referenced in a lemma's contract, whose bound
        // `0 <= bcount <= k` is proved by induction USING the defining equation (the cross-lemma use the
        // statement-form Phase-20 bcount couldn't support).
        [group: 'P25 recursive-defs', name: 'bcount bound via defining equation', ok: true,
         src: tc('''class C {
                        int bcount(Set<Integer> s, int k) { k <= 0 ? 0 : bcount(s, k - 1) + ((k - 1) in s ? 1 : 0) }
                        @Requires({ k >= 0 })
                        @Ensures({ 0 <= bcount(s, k) && bcount(s, k) <= k })
                        @Decreases({ k })
                        void bcountBound(Set<Integer> s, int k) {
                            if (k > 0) bcountBound(s, k - 1)
                        }
                    }''')],
        // Soundness: the definition is faithful, not vacuous — a too-tight bound (<= k-1) refutes.
        [group: 'P25 recursive-defs', name: 'wrong bcount bound refuted', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        int bcount(Set<Integer> s, int k) { k <= 0 ? 0 : bcount(s, k - 1) + ((k - 1) in s ? 1 : 0) }
                        @Requires({ k >= 0 })
                        @Ensures({ bcount(s, k) <= k - 1 })
                        @Decreases({ k })
                        void bcountBound(Set<Integer> s, int k) {
                            if (k > 0) bcountBound(s, k - 1)
                        }
                    }''')],

        // ---------- Phase 26: the frontier/stack invariant — DFS establishes closure ----------
        // The (a) half of completeness. The recursion stack is a Set ghost `onStack`, pushed before the
        // recursive call and popped after. The invariant is closed-EXCEPT-ON-STACK: every visited node is on
        // the stack OR its successor is visited. `visit` maintains it AND restores the stack (net zero), so
        // when the stack is empty the invariant *is* full closure. Mark-then-recurse: u is covered by being
        // on the stack until the recursion into next[u] returns (covering next[u]), then u is popped.
        [group: 'P26 frontier', name: 'DFS establishes closure (frontier/stack invariant)', ok: true,
         src: tc('''class C {
                        Map<Integer,Integer> next
                        Set<Integer> visited
                        Set<Integer> onStack
                        int n
                        @Requires({ 0 <= u && u < n &&
                                    (0..<n).every { 0 <= next[it] && next[it] < n } &&
                                    (0..<n).every { (it in visited) ==> (it in onStack || next[it] in visited) } &&
                                    (0..<n).every { (it in onStack) ==> (it in visited) } })
                        @Modifies({ [this.visited, this.onStack] })
                        @Decreases({ n - Sets.boundedCount(visited, n) })
                        @Ensures({ (u in visited) &&
                                   (0..<n).every { (it in visited) ==> (it in onStack || next[it] in visited) } &&
                                   (0..<n).every { (it in onStack) ==> (it in visited) } &&
                                   (0..<n).every { (it in onStack) == (it in old.onStack) } &&
                                   (0..<n).every { (it in old.visited) ==> (it in visited) } })
                        void visit(int u) {
                            if (u !in visited && Sets.boundedCount(visited, n) < n) {
                                visited.add(u)
                                onStack.add(u)
                                visit(next[u])
                                onStack.remove(u)
                            }
                        }
                        // The payoff: from an empty visited set and empty stack, one DFS leaves `visited`
                        // CLOSED under next — every visited node's successor is visited. When the stack is
                        // empty the closed-except-on-stack invariant *is* full closure. This is DFS
                        // *establishing* closure — the (a) half, the last piece of DFS completeness.
                        @Requires({ 0 <= start && start < n &&
                                    (0..<n).every { 0 <= next[it] && next[it] < n } &&
                                    (0..<n).every { it !in visited } &&
                                    (0..<n).every { it !in onStack } })
                        @Modifies({ [this.visited, this.onStack] })
                        @Ensures({ (0..<n).every { (it in visited) ==> (next[it] in visited) } })
                        void dfs(int start) {
                            visit(start)
                        }
                    }''')],

        // ---------- Phase 27: non-Int element domains — Set<String> ----------
        // Membership assumed entails the same membership at exit — the basic round-trip
        // confirming literal interning + element-sort routing work end-to-end for Strings.
        [group: 'P27 non-int domains', name: 'Set<String> contains literal round-trip', ok: true,
         src: tc('''class C {
                       @Requires({ s.contains("admin") })
                       @Ensures({ s.contains("admin") })
                       static int f(Set<String> s) { 0 }
                   }''')],
        // Soundness: two distinct String literals are NOT the same constant — `contains("admin")`
        // assumed does NOT entail `contains("guest")`. Refutes (lazy pairwise-distinct works).
        [group: 'P27 non-int domains', name: 'Set<String> distinct literals not collapsed',
         expect: 'Cannot prove postcondition',
         src: tc('''class C {
                       @Requires({ s.contains("admin") })
                       @Ensures({ s.contains("guest") })
                       static int f(Set<String> s) { 0 }
                   }''')],
        // Add-then-contains: the just-added literal is in the post-state, by Z3's array theory
        // alone (the per-mutation cardinality law isn't needed for this).
        [group: 'P27 non-int domains', name: 'Set<String> add then contains', ok: true,
         src: tc('''class C {
                       Set<String> tags
                       @Modifies({ this.tags })
                       @Ensures({ "admin" in tags })
                       void grant() { tags.add("admin") }
                   }''')],
        // String parameter — `x` is a `varOfSort(stringSort)`, the membership relates the same constant
        // assumed and proved. The parameter sort flows from the VariableExpression's declared type.
        [group: 'P27 non-int domains', name: 'Set<String> contains parameter', ok: true,
         src: tc('''class C {
                       @Requires({ s.contains(x) })
                       @Ensures({ s.contains(x) })
                       static int f(Set<String> s, String x) { 0 }
                   }''')],
        // Cardinality: a fresh-add raises size by one (the per-mutation card law works over String
        // sets — its only sort dependency is the array's, which Z3 handles polymorphically).
        [group: 'P27 non-int domains', name: 'Set<String> fresh add grows size by one', ok: true,
         src: tc('''class C {
                       Set<String> tags
                       @Requires({ !("admin" in tags) })
                       @Modifies({ this.tags })
                       @Ensures({ tags.size() == old.tags.size() + 1 })
                       void grant() { tags.add("admin") }
                   }''')],
        // Soundness anchor for size: WITHOUT the freshness guard, the +1 claim refutes
        // ("admin" might already be present, in which case add is a no-op).
        [group: 'P27 non-int domains', name: 'Set<String> non-fresh add size +1 refuted',
         expect: 'Cannot prove postcondition',
         src: tc('''class C {
                       Set<String> tags
                       @Modifies({ this.tags })
                       @Ensures({ tags.size() == old.tags.size() + 1 })
                       void grant() { tags.add("admin") }
                   }''')],

        // ---------- Phase 27: non-Int element domains — Set<Enum> ----------
        // Color is nested inside C so @TypeChecked applies to the outer (verified) class — tc()
        // annotates the FIRST class only.
        // Enum literal round-trip: `Color.RED` minted as a constant of the per-class Color!Sort,
        // assumed and proved across the method body.
        [group: 'P27 non-int domains', name: 'Set<Enum> contains literal round-trip', ok: true,
         src: tc('''class C {
                        enum Color { RED, BLUE, GREEN }
                        @Requires({ s.contains(Color.RED) })
                        @Ensures({ s.contains(Color.RED) })
                        static int f(Set<Color> s) { 0 }
                    }''')],
        // Soundness: distinct enum constants don't collapse — contains(RED) doesn't entail
        // contains(BLUE). Same pairwise-distinct mechanism as String literals, per enum sort.
        [group: 'P27 non-int domains', name: 'Set<Enum> distinct constants not collapsed',
         expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        enum Color { RED, BLUE, GREEN }
                        @Requires({ s.contains(Color.RED) })
                        @Ensures({ s.contains(Color.BLUE) })
                        static int f(Set<Color> s) { 0 }
                    }''')],
        // Add then contains: the just-added enum constant is in the post-state.
        [group: 'P27 non-int domains', name: 'Set<Enum> add then contains', ok: true,
         src: tc('''class C {
                        enum Color { RED, BLUE, GREEN }
                        Set<Color> palette
                        @Modifies({ this.palette })
                        @Ensures({ Color.RED in palette })
                        void useRed() { palette.add(Color.RED) }
                    }''')],
        // Cardinality: fresh-add raises size by one (per-mutation card law works for enum sorts
        // the same way it does for strings — array theory is polymorphic).
        [group: 'P27 non-int domains', name: 'Set<Enum> fresh add grows size by one', ok: true,
         src: tc('''class C {
                        enum Color { RED, BLUE, GREEN }
                        Set<Color> palette
                        @Requires({ !(Color.RED in palette) })
                        @Modifies({ this.palette })
                        @Ensures({ palette.size() == old.palette.size() + 1 })
                        void useRed() { palette.add(Color.RED) }
                    }''')],
        // Soundness: without the freshness guard, the +1 claim rightly refutes.
        [group: 'P27 non-int domains', name: 'Set<Enum> non-fresh add size +1 refuted',
         expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        enum Color { RED, BLUE, GREEN }
                        Set<Color> palette
                        @Modifies({ this.palette })
                        @Ensures({ palette.size() == old.palette.size() + 1 })
                        void useRed() { palette.add(Color.RED) }
                    }''')],

        // ---------- Phase 27: Map<String, Integer> ----------
        // Key membership round-trip: containsKey assumed entails the same key membership at exit.
        [group: 'P27 non-int domains', name: 'Map<String,Int> containsKey round-trip', ok: true,
         src: tc('''class C {
                        @Requires({ m.containsKey("admin") })
                        @Ensures({ m.containsKey("admin") })
                        static int f(Map<String,Integer> m) { 0 }
                    }''')],
        // Distinct String keys aren't conflated — containsKey("admin") doesn't entail containsKey("guest").
        [group: 'P27 non-int domains', name: 'Map<String,Int> distinct keys not conflated',
         expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Requires({ m.containsKey("admin") })
                        @Ensures({ m.containsKey("guest") })
                        static int f(Map<String,Integer> m) { 0 }
                    }''')],
        // put then get: the just-put value is what get returns.
        [group: 'P27 non-int domains', name: 'Map<String,Int> put then get', ok: true,
         src: tc('''class C {
                        Map<String,Integer> m
                        @Modifies({ this.m })
                        @Ensures({ m["admin"] == 5 && m.containsKey("admin") })
                        void grant() { m.put("admin", 5) }
                    }''')],
        // put with subscript spelling: m["k"] = v exercises the ArrayStore-step path.
        [group: 'P27 non-int domains', name: 'Map<String,Int> subscript put', ok: true,
         src: tc('''class C {
                        Map<String,Integer> m
                        @Modifies({ this.m })
                        @Ensures({ m["admin"] == 5 })
                        void grant() { m["admin"] = 5 }
                    }''')],
        // Frame: put on key "admin" leaves any other key's mapping unchanged (array theory does this).
        [group: 'P27 non-int domains', name: 'Map<String,Int> put frames other keys', ok: true,
         src: tc('''class C {
                        Map<String,Integer> m
                        @Requires({ m["other"] == 99 })
                        @Modifies({ this.m })
                        @Ensures({ m["other"] == 99 })
                        void grant() { m.put("admin", 5) }
                    }''')],

        // ---------- Phase 27: Map<String, String> ----------
        // Both keys and values are String — exercises String value-sort routing too.
        [group: 'P27 non-int domains', name: 'Map<String,String> put then get', ok: true,
         src: tc('''class C {
                        Map<String,String> roles
                        @Modifies({ this.roles })
                        @Ensures({ roles["bob"] == "admin" })
                        void promote() { roles["bob"] = "admin" }
                    }''')],
        // Distinct String values don't conflate either — the put guarantees "admin", not "guest".
        [group: 'P27 non-int domains', name: 'Map<String,String> wrong value refuted',
         expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        Map<String,String> roles
                        @Modifies({ this.roles })
                        @Ensures({ roles["bob"] == "guest" })
                        void promote() { roles["bob"] = "admin" }
                    }''')],

        // ---------- Phase 27: List<String> ----------
        // Read after store: subscript-store of a String element shows up on a later read.
        [group: 'P27 non-int domains', name: 'List<String> store then read', ok: true,
         src: tc('''class C {
                        @Requires({ 0 <= k && k < xs.size() })
                        @Ensures({ xs[k] == "admin" })
                        static int set(List<String> xs, int k) { xs[k] = "admin"; 0 }
                    }''')],
        // Soundness: storing one value can't be claimed as another.
        [group: 'P27 non-int domains', name: 'List<String> wrong stored value refuted',
         expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Requires({ 0 <= k && k < xs.size() })
                        @Ensures({ xs[k] == "guest" })
                        static int set(List<String> xs, int k) { xs[k] = "admin"; 0 }
                    }''')],
        // Index-bounds check still applies for non-Int element lists — same Phase-1 obligation.
        [group: 'P27 non-int domains', name: 'List<String> unguarded index refuted',
         expect: 'IndexOutOfBoundsException',
         src: tc('class C { static String g(List<String> xs, int i) { xs[i] } }')],

        // ---------- Phase 27: Map<Enum, V> ----------
        // Enum-keyed map: same routing as String-keyed but with the per-class enum sort.
        [group: 'P27 non-int domains', name: 'Map<Enum,Int> containsKey round-trip', ok: true,
         src: tc('''class C {
                        enum Color { RED, BLUE, GREEN }
                        @Requires({ m.containsKey(Color.RED) })
                        @Ensures({ m.containsKey(Color.RED) })
                        static int f(Map<Color,Integer> m) { 0 }
                    }''')],
        // Distinct enum keys don't conflate.
        [group: 'P27 non-int domains', name: 'Map<Enum,Int> distinct keys not conflated',
         expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        enum Color { RED, BLUE, GREEN }
                        @Requires({ m.containsKey(Color.RED) })
                        @Ensures({ m.containsKey(Color.BLUE) })
                        static int f(Map<Color,Integer> m) { 0 }
                    }''')],
        // put then get on an enum-keyed map.
        [group: 'P27 non-int domains', name: 'Map<Enum,Int> put then get', ok: true,
         src: tc('''class C {
                        enum Color { RED, BLUE, GREEN }
                        Map<Color,Integer> weights
                        @Modifies({ this.weights })
                        @Ensures({ weights[Color.RED] == 5 && weights.containsKey(Color.RED) })
                        void useRed() { weights.put(Color.RED, 5) }
                    }''')],
        // Subscript put spelling: weights[Color.RED] = 5 exercises the ArrayStore path.
        [group: 'P27 non-int domains', name: 'Map<Enum,Int> subscript put', ok: true,
         src: tc('''class C {
                        enum Color { RED, BLUE, GREEN }
                        Map<Color,Integer> weights
                        @Modifies({ this.weights })
                        @Ensures({ weights[Color.RED] == 5 })
                        void useRed() { weights[Color.RED] = 5 }
                    }''')],
        // Frame: a put on RED leaves a value at BLUE unchanged.
        [group: 'P27 non-int domains', name: 'Map<Enum,Int> put frames other key', ok: true,
         src: tc('''class C {
                        enum Color { RED, BLUE, GREEN }
                        Map<Color,Integer> weights
                        @Requires({ weights[Color.BLUE] == 99 })
                        @Modifies({ this.weights })
                        @Ensures({ weights[Color.BLUE] == 99 })
                        void useRed() { weights[Color.RED] = 5 }
                    }''')],

        // ---------- Phase 27: List<Enum> ----------
        // Store + read at an Int-indexed enum-element list.
        [group: 'P27 non-int domains', name: 'List<Enum> store then read', ok: true,
         src: tc('''class C {
                        enum Color { RED, BLUE, GREEN }
                        @Requires({ 0 <= k && k < xs.size() })
                        @Ensures({ xs[k] == Color.RED })
                        static int paint(List<Color> xs, int k) { xs[k] = Color.RED; 0 }
                    }''')],
        // Distinct enum stored value can't be claimed as another.
        [group: 'P27 non-int domains', name: 'List<Enum> wrong stored value refuted',
         expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        enum Color { RED, BLUE, GREEN }
                        @Requires({ 0 <= k && k < xs.size() })
                        @Ensures({ xs[k] == Color.BLUE })
                        static int paint(List<Color> xs, int k) { xs[k] = Color.RED; 0 }
                    }''')],

        // ---------- Phase 27: Sets.boundedBy / Sets.boundedCount honestly skip on non-Int element sets ----
        // Sets.boundedBy(s, n) means s ⊆ [0, n) — only defined for Int element domains. Applying it
        // to a Set<String> rightly produces a "skipped: outside fragment" diagnostic rather than
        // silently asserting a sort-mismatched bounded universal.
        [group: 'P27 non-int domains', name: 'Sets.boundedBy on Set<String> skipped',
         expect: 'outside fragment',
         src: tc('''class C {
                        @Requires({ Sets.boundedBy(s, 5) })
                        @Ensures({ s.size() <= 5 })
                        static int f(Set<String> s) { 0 }
                    }''')],
        // Sets.boundedCount on Set<Enum> with k that doesn't match the enum's domain size: still skips,
        // because without an enum ordering there's no meaning for "count of constants with ordinal < k".
        // (The matching-k case is supported in Phase 29 — see the FSM exploration group below.)
        [group: 'P27 non-int domains', name: 'Sets.boundedCount on Set<Enum> with non-matching k skipped',
         expect: 'outside fragment',
         src: tc('''class C {
                        enum Color { RED, BLUE, GREEN }
                        @Requires({ Sets.boundedCount(s, 2) == 2 })
                        @Ensures({ s.size() >= 0 })
                        static int f(Set<Color> s) { 0 }
                    }''')],
        // Regression: Sets.boundedBy over a Set<Integer> still verifies — the Int-domain path is
        // unchanged by the non-Int restriction added in step 8.
        [group: 'P27 non-int domains', name: 'Sets.boundedBy on Set<Integer> still verifies', ok: true,
         src: tc('''class C {
                        @Requires({ Sets.boundedBy(s, 5) })
                        @Ensures({ s.size() <= 5 })
                        static int f(Set<Integer> s) { 0 }
                    }''')],

        // ---------- Phase 27 step 9: counterexample rendering for non-Int parameters ----------
        // A String parameter pinned to "admin" by @Requires renders as `f("admin")` in `fails on:`.
        [group: 'P27 non-int domains', name: 'String param model value in repro',
         expect: 'fails on: f("admin")',
         src: tc('''class C {
                        @Requires({ s == "admin" })
                        @Ensures({ s == "guest" })
                        static int f(String s) { 0 }
                    }''')],
        // An Enum parameter pinned to Color.RED renders as `f(Color.RED)` in `fails on:`.
        [group: 'P27 non-int domains', name: 'Enum param model value in repro',
         expect: 'fails on: f(Color.RED)',
         src: tc('''class C {
                        enum Color { RED, BLUE, GREEN }
                        @Requires({ c == Color.RED })
                        @Ensures({ c == Color.BLUE })
                        static int f(Color c) { 0 }
                    }''')],

        // ---------- Phase 59: classic for-loops (desugared to while-shape) ----------
        // The headline win: an array-bounds obligation `a[i]` inside a for-loop body is
        // discharged from the loop @Invariant, exactly as for a while loop.
        [group: 'P59 for-loop', name: 'for-loop bounds verified from invariant', ok: true,
         src: tc('''class C {
                       @Requires({ 0 <= n && n <= a.length })
                       static int sumFor(int[] a, int n) {
                           int s = 0, i = 0
                           @Invariant({ 0 <= i && i <= n })
                           for (i = 0; i < n; i++) { s = s + a[i] }
                           return s
                       }
                   }''')],
        // Drop `n <= a.length` and the in-loop `a[i]` is refuted out of bounds — the for-loop
        // body's obligations are checked under the invariant, which no longer bounds the index.
        [group: 'P59 for-loop', name: 'for-loop bounds refuted (missing precondition)',
         expect: 'IndexOutOfBoundsException',
         src: tc('''class C {
                       @Requires({ 0 <= n })
                       static int sumFor(int[] a, int n) {
                           int s = 0, i = 0
                           @Invariant({ 0 <= i && i <= n })
                           for (i = 0; i < n; i++) { s = s + a[i] }
                           return s
                       }
                   }''')],
        // Postcondition + termination over a for-loop: all four loop VCs discharge, the
        // i++ update normalised to i = i + 1, the init `i = 0` threaded into the prefix.
        [group: 'P59 for-loop', name: 'for-loop postcondition + decreases verified', ok: true,
         src: tc('''class C {
                       @Requires({ n >= 0 })
                       @Ensures({ result == n })
                       static int countUp(int n) {
                           int i = 0
                           @Invariant({ 0 <= i && i <= n })
                           @Decreases({ n - i })
                           for (i = 0; i < n; i++) { }
                           return i
                       }
                   }''')],
        // A broken invariant (`i == 0`, falsified by the i++ update) fails preservation — a
        // loud refutation, not a silent pass: the for-loop rides the same inductive machinery.
        [group: 'P59 for-loop', name: 'for-loop broken invariant refuted',
         expect: 'invariant is preserved',
         src: tc('''class C {
                       @Requires({ n >= 0 })
                       @Ensures({ result == n })
                       static int countUp(int n) {
                           int i = 0
                           @Invariant({ i == 0 })
                           @Decreases({ n - i })
                           for (i = 0; i < n; i++) { }
                           return i
                       }
                   }''')],
        // The compound-assignment update form `i += 1` normalises the same way.
        [group: 'P59 for-loop', name: 'for-loop compound update (i += 1) verified', ok: true,
         src: tc('''class C {
                       @Requires({ n >= 0 })
                       @Ensures({ result == n })
                       static int countUp(int n) {
                           int i = 0
                           @Invariant({ 0 <= i && i <= n })
                           @Decreases({ n - i })
                           for (i = 0; i < n; i += 1) { }
                           return i
                       }
                   }''')],
        // ---------- Phase 63: for-in loops (synthesized hidden index, loop var retained) ----------
        // `for (x in xs)` desugars to an indexed while: a hidden index drives iteration, the loop
        // variable `x` is bound to xs[idx] each pass. Element reasoning comes from the body's
        // structure (preservation doesn't assume @Requires): |x| is provably >= 0, so a running
        // sum of absolute values stays >= 0 — verified, with auto-injected index bounds + termination.
        [group: 'P63 for-in', name: 'for-in sum-of-abs stays non-negative', ok: true,
         src: tc('''class C {
                       @Ensures({ result >= 0 })
                       static int sumAbs(List<Integer> xs) {
                           int s = 0
                           @Invariant({ s >= 0 })
                           for (x in xs) { s = s + (x < 0 ? -x : x) }
                           return s
                       }
                   }''')],
        // The Java-style colon syntax `for (T x : xs)` parses to the same ForStatement and verifies
        // identically to the `in` form.
        [group: 'P63 for-in', name: 'for-colon (Java-style) verified', ok: true,
         src: tc('''class C {
                       @Ensures({ result >= 0 })
                       static int sumAbs(List<Integer> xs) {
                           int s = 0
                           @Invariant({ s >= 0 })
                           for (int x : xs) { s = s + (x < 0 ? -x : x) }
                           return s
                       }
                   }''')],
        // Conditional accumulation over the loop variable: a count only ever grows, so c >= 0 holds.
        [group: 'P63 for-in', name: 'for-in conditional count stays non-negative', ok: true,
         src: tc('''class C {
                       @Ensures({ result >= 0 })
                       static int countEvens(List<Integer> xs) {
                           int c = 0
                           @Invariant({ c >= 0 })
                           for (x in xs) { if (x % 2 == 0) c = c + 1 }
                           return c
                       }
                   }''')],
        // Loud refutation, not a silent pass: `s == 0` isn't preserved by `s = s + x` (x may be
        // non-zero). The counterexample names the loop variable `x`, not the hidden index.
        [group: 'P63 for-in', name: 'for-in broken invariant refuted (preservation)',
         expect: 'invariant is preserved',
         src: tc('''class C {
                       @Ensures({ result == 0 })
                       static int sumIn(List<Integer> xs) {
                           int s = 0
                           @Invariant({ s == 0 })
                           for (x in xs) { s = s + x }
                           return s
                       }
                   }''')],
        // The synthetic index is hidden — the counterexample reads in terms of the loop variable,
        // never `__gvForInIdx`.
        [group: 'P63 for-in', name: 'for-in counterexample hides synthetic index',
         expect: 'invariant is preserved', refute: '__gvForInIdx',
         src: tc('''class C {
                       @Ensures({ result >= 0 })
                       static int sumIn(List<Integer> xs) {
                           int s = 0
                           @Invariant({ s >= 0 })
                           for (x in xs) { s = s + x }
                           return s
                       }
                   }''')],
        // A for-in over a literal (not a named collection) has no size oracle to index — skips loudly.
        [group: 'P63 for-in', name: 'for-in over a list literal skips', expect: 'Skipped',
         src: tc('''class C {
                       @Ensures({ result >= 0 })
                       static int f() {
                           int s = 0
                           @Invariant({ s >= 0 })
                           for (x in [1, 2, 3]) { s = s + x }
                           return s
                       }
                   }''')],

        // ---------- Phase 64: loop-stable @Requires (element reasoning from a precondition) ----------
        // The unlock: preservation may assume @Requires conjuncts the loop can't invalidate. The body
        // only reads xs, so `xs.every { it >= 0 }` is stable and instantiates at the current element —
        // a running total of non-negative elements is provably non-negative. (Previously refuted:
        // preservation had no way to know x >= 0.)
        [group: 'P64 loop-stable req', name: 'for-in total over non-negative verified', ok: true,
         src: tc('''class C {
                       @Requires({ xs.every { it >= 0 } })
                       @Ensures({ result >= 0 })
                       static int total(List<Integer> xs) {
                           int s = 0
                           @Invariant({ s >= 0 })
                           for (x in xs) { s = s + x }
                           return s
                       }
                   }''')],
        // The precondition is load-bearing: drop it and preservation refutes (x may be negative) —
        // confirming the verification above rests on the assumed element fact, not a vacuity.
        [group: 'P64 loop-stable req', name: 'for-in total without precondition refuted',
         expect: 'invariant is preserved',
         src: tc('''class C {
                       @Ensures({ result >= 0 })
                       static int total(List<Integer> xs) {
                           int s = 0
                           @Invariant({ s >= 0 })
                           for (x in xs) { s = s + x }
                           return s
                       }
                   }''')],
        // Soundness anchor: a precondition over state the loop *modifies* must NOT be assumed. Here the
        // loop decrements `cap`, so `@Requires({ cap >= 1000 })` is dropped — preservation of
        // `cap >= 0` correctly refutes (cap reaches -5). If the stale fact were assumed, this would
        // wrongly verify.
        [group: 'P64 loop-stable req', name: 'precondition over modified state dropped (sound)',
         expect: 'invariant is preserved',
         src: tc('''class C {
                       @Requires({ cap >= 1000 })
                       @Ensures({ result <= 0 })
                       static int drain(int cap) {
                           @Invariant({ cap >= 0 })
                           @Decreases({ cap + 5 })
                           while (cap > -5) { cap = cap - 1 }
                           return cap
                       }
                   }''')],
        // A precondition over an *unmodified* parameter is assumed in a plain while loop too: the
        // lower bound `lo` is never written, so `s >= lo` is preserved by `s = s + 1` given `lo <= 0`.
        [group: 'P64 loop-stable req', name: 'while-loop stable precondition assumed', ok: true,
         src: tc('''class C {
                       @Requires({ lo <= 0 && n >= 0 })
                       @Ensures({ result >= lo })
                       static int countFrom(int lo, int n) {
                           int s = lo
                           int i = 0
                           @Invariant({ 0 <= i && i <= n && s >= lo })
                           @Decreases({ n - i })
                           while (i < n) { s = s + 1; i = i + 1 }
                           return s
                       }
                   }''')],

        // ---------- Phase 65: for-in invariants over the loop variable (per-element checks) ----------
        // groovy-contracts checks a loop invariant at body-entry (x bound to the current element), so a
        // clause referencing the loop variable is a per-element check — not a loop-head invariant. With
        // a precondition over the elements, it verifies (was a false positive before: the loop-head
        // check havoced x and "failed" on the empty list, which the runtime never even reaches).
        [group: 'P65 per-element inv', name: 'for-in invariant over x verified from every', ok: true,
         src: tc('''class C {
                       @Requires({ xs.every { it >= 0 } })
                       static void m(List<Integer> xs) {
                           @groovy.contracts.Invariant({ x >= 0 })
                           for (x in xs) { }
                       }
                   }''')],
        // Without a precondition bounding the elements, the per-element invariant refutes — the
        // counterexample names the offending element value (and a non-empty collection), not the
        // spurious empty-list case the loop-head check used to report.
        [group: 'P65 per-element inv', name: 'for-in invariant over x refuted (no element bound)',
         expect: 'holds for every element', refute: 'xs.size() = 0',
         src: tc('''class C {
                       static void m(List<Integer> xs) {
                           @groovy.contracts.Invariant({ x < 5 })
                           for (x in xs) { }
                       }
                   }''')],
        // A mixed invariant: the accumulator clause `s >= 0` is inductive (loop-head), the element
        // clause `x >= 0` is per-element — both discharge, and together prove a non-negative total.
        [group: 'P65 per-element inv', name: 'for-in mixed accumulator + per-element invariant', ok: true,
         src: tc('''class C {
                       @Requires({ xs.every { it >= 0 } })
                       @Ensures({ result >= 0 })
                       static int total(List<Integer> xs) {
                           int s = 0
                           @Invariant({ s >= 0 && x >= 0 })
                           for (x in xs) { s += x }
                           s
                       }
                   }''')],
        // Empty-collection vacuity: a per-element invariant that would be unprovable on an arbitrary
        // element still verifies when the precondition forces the collection empty (the body, and so
        // the per-element check, is never reached).
        [group: 'P65 per-element inv', name: 'for-in per-element vacuous on empty collection', ok: true,
         src: tc('''class C {
                       @Requires({ xs.size() == 0 })
                       static void m(List<Integer> xs) {
                           @groovy.contracts.Invariant({ x > 999 })
                           for (x in xs) { }
                       }
                   }''')],

        // ---------- Phase 66: repeated @Requires / @Ensures are conjoined ----------
        // groovy-contracts is @Repeatable and enforces each at runtime, so multiple @Requires mean
        // their conjunction. Both are now captured: result = a + b >= 0 needs BOTH a >= 0 and b >= 0
        // (previously only the last was kept, so `a` was unconstrained and this refuted).
        [group: 'P66 repeated contracts', name: 'two @Requires both assumed', ok: true,
         src: tc('class C { @Requires({ a >= 0 }) @Requires({ b >= 0 }) @Ensures({ result >= 0 }) static int f(int a, int b) { a + b } }')],
        // Soundness: a method must satisfy EVERY @Ensures. Here the body returns 3 — it meets the
        // *last* postcondition (3 <= 100) but violates the *first* (3 >= 5), which used to be dropped
        // (silently "verifying" a method that breaks its own spec). Now correctly refuted.
        [group: 'P66 repeated contracts', name: 'two @Ensures both proven (violates first → refuted)',
         expect: 'Cannot prove postcondition',
         src: tc('class C { @Ensures({ result >= 5 }) @Ensures({ result <= 100 }) static int f() { 3 } }')],
        // A body satisfying both postconditions verifies.
        [group: 'P66 repeated contracts', name: 'two @Ensures both satisfied verified', ok: true,
         src: tc('class C { @Ensures({ result >= 5 }) @Ensures({ result <= 100 }) static int f() { 50 } }')],
        // Three @Requires conjoin too, and a precondition that rules out the unsafe input verifies the body.
        [group: 'P66 repeated contracts', name: 'three @Requires conjoined verify index', ok: true,
         src: tc('class C { @Requires({ a != null }) @Requires({ i >= 0 }) @Requires({ i < a.length }) static int f(int[] a, int i) { a[i] } }')],
        // @Modifies is @Repeatable too, but a frame is a *union* of locations (not a conjunction): two
        // @Modifies are merged, so a method writing both declared fields passes the frame check
        // (previously only the last was kept, wrongly flagging the write to the dropped field).
        [group: 'P66 repeated contracts', name: 'two @Modifies frames merged (both writes allowed)', ok: true,
         src: tc('class C { int a; int b; @Modifies({ this.a }) @Modifies({ this.b }) void setBoth() { a = 1; b = 2 } }')],
        // A write outside the merged frame is still caught — both declared locations are in scope, the
        // undeclared third field is the violation.
        [group: 'P66 repeated contracts', name: 'two @Modifies, undeclared write violates',
         expect: 'not in its @Modifies clause',
         src: tc('class C { int a; int b; int c; @Modifies({ this.a }) @Modifies({ this.b }) void m() { a = 1; b = 2; c = 3 } }')],

        // ---------- Phase 60: xs.max() / xs.min() as the witnessed-extremum spec ----------
        // The ergonomic win: `result == a.max()` means exactly the every/any spec the
        // maxElement example spells out by hand — and the same max-finding loop discharges it.
        [group: 'P60 max/min', name: 'result == a.max() verified', ok: true,
         src: tc('''class C {
                        @Requires({ a != null && a.length > 0 })
                        @Ensures({ result == a.max() })
                        static int maxOf(int[] a) {
                            int m = a[0]
                            int i = 1
                            @Invariant({ 1 <= i && i <= a.length &&
                                         (0..<i).every { a[it] <= m } &&
                                         (0..<i).any { a[it] == m } })
                            @Decreases({ a.length - i })
                            while (i < a.length) {
                                if (a[i] > m) m = a[i]
                                i = i + 1
                            }
                            return m
                        }
                    }''')],
        [group: 'P60 max/min', name: 'result == a.min() verified', ok: true,
         src: tc('''class C {
                        @Requires({ a != null && a.length > 0 })
                        @Ensures({ result == a.min() })
                        static int minOf(int[] a) {
                            int m = a[0]
                            int i = 1
                            @Invariant({ 1 <= i && i <= a.length &&
                                         (0..<i).every { m <= a[it] } &&
                                         (0..<i).any { a[it] == m } })
                            @Decreases({ a.length - i })
                            while (i < a.length) {
                                if (a[i] < m) m = a[i]
                                i = i + 1
                            }
                            return m
                        }
                    }''')],
        // Soundness anchor: returning the first element isn't the max — `result == a.max()` refutes
        // (a later element can exceed a[0], so result fails the bound half of the extremum spec).
        [group: 'P60 max/min', name: 'returning a[0] is not a.max() (refutes)',
         expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Requires({ a != null && a.length > 0 })
                        @Ensures({ result == a.max() })
                        static int firstOf(int[] a) { a[0] }
                    }''')],
        // Mint-once: two `a.max()` occurrences are the same term, so reflexive equality holds.
        [group: 'P60 max/min', name: 'a.max() == a.max() (mint-once)', ok: true,
         src: tc('class C { @Requires({ a != null }) @Ensures({ a.max() == a.max() }) static int f(int[] a) { 0 } }')],
        // Vacuity guard: on an empty array the extremum is unconstrained (Groovy's [].max() is
        // undefined), so a claim about it is NOT provable — the existential can't fire vacuously.
        [group: 'P60 max/min', name: 'empty-range max claim refuted (no vacuous pass)',
         expect: 'Cannot prove postcondition',
         src: tc('class C { @Requires({ a != null && a.length == 0 }) @Ensures({ a.max() == 5 }) static int f(int[] a) { 0 } }')],

        // ---------- Phase 61: Groovy-faithful BigDecimal division (Z3 Real sort) ----------
        // The headline Groovy surprise, now provable: `/` on integers is BigDecimal division, so
        // 5 / 2 is 2.5 — not 2. (A variable defeats the constant-folder so the `/` path is exercised.)
        [group: 'P61 decimal', name: 'a / 2 == 2.5 verified (BigDecimal division)', ok: true,
         src: tc('class C { @Requires({ a == 5 }) @Ensures({ a / 2 == 2.5 }) static int f(int a) { 0 } }')],
        // The lock-in that `/` is NOT integer division: 5 / 2 == 2 is false (it is 2.5).
        [group: 'P61 decimal', name: 'a / 2 == 2 refuted (/ is not intdiv)',
         expect: 'Cannot prove postcondition',
         src: tc('class C { @Requires({ a == 5 }) @Ensures({ a / 2 == 2 }) static int f(int a) { 0 } }')],
        // Contrast: intdiv still truncates toward zero, so 5.intdiv(2) == 2 verifies — the two
        // operators are modelled distinctly (Real division vs Euclidean intdiv).
        [group: 'P61 decimal', name: 'a.intdiv(2) == 2 verified (contrast)', ok: true,
         src: tc('class C { @Requires({ a == 5 }) @Ensures({ a.intdiv(2) == 2 }) static int f(int a) { 0 } }')],
        // The compelling example: a BigDecimal average is *exactly* (a + b) / 2 — int operands
        // coerced to Real, the result a decimal name, the spec proven (not just asserted).
        [group: 'P61 decimal', name: 'BigDecimal avg == (a+b)/2 verified', ok: true,
         src: tc('''class C {
                        @Ensures({ result == (a + b) / 2 })
                        static BigDecimal avg(int a, int b) { (a + b) / 2 }
                    }''')],
        // Soundness anchor: claiming the average is (a + b) / 3 refutes.
        [group: 'P61 decimal', name: 'BigDecimal avg wrong divisor refuted',
         expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Ensures({ result == (a + b) / 3 })
                        static BigDecimal avg(int a, int b) { (a + b) / 2 }
                    }''')],
        // A BigDecimal-typed parameter compared against a decimal literal: price >= 10.0 ⇒ price > 9.99.
        [group: 'P61 decimal', name: 'BigDecimal param decimal comparison verified', ok: true,
         src: tc('class C { @Requires({ price >= 10.0 }) @Ensures({ price > 9.99 }) static int f(BigDecimal price) { 0 } }')],
        // The divide-by-zero obligation still fires for `/` — guarded it verifies...
        [group: 'P61 decimal', name: 'decimal division guarded by b != 0 verified', ok: true,
         src: tc('class C { @Requires({ b != 0 }) static BigDecimal f(int a, int b) { a / b } }')],
        // ...and unguarded it refutes with the ArithmeticException diagnostic.
        [group: 'P61 decimal', name: 'unguarded decimal division refuted',
         expect: 'ArithmeticException: Division by zero',
         src: tc('class C { static BigDecimal f(int a, int b) { a / b } }')],

        // ---------- Phase 67: decimal negation (unary minus, negative literal) ----------
        // Unary minus on a BigDecimal is Real negation — previously it fell to the int path (int
        // shadow) and refuted a true postcondition.
        [group: 'P67 decimal negation', name: 'decimal unary minus verified', ok: true,
         src: tc('class C { @Requires({ a == 2.5 }) @Ensures({ result == -2.5 }) static BigDecimal f(BigDecimal a) { -a } }')],
        // Negating a negative is positive — composes with the comparison path.
        [group: 'P67 decimal negation', name: 'negate a negative is positive', ok: true,
         src: tc('class C { @Requires({ a < 0.0 }) @Ensures({ result > 0.0 }) static BigDecimal f(BigDecimal a) { -a } }')],
        // A negative decimal literal as the return value (was skipped — translate left it unmodelled).
        [group: 'P67 decimal negation', name: 'negative decimal literal verified', ok: true,
         src: tc('class C { @Ensures({ result < 0.0 }) static BigDecimal f() { -2.5 } }')],
        // Soundness anchor: a wrong negation refutes.
        [group: 'P67 decimal negation', name: 'wrong decimal negation refuted',
         expect: 'Cannot prove postcondition',
         src: tc('class C { @Requires({ a == 2.5 }) @Ensures({ result == 2.5 }) static BigDecimal f(BigDecimal a) { -a } }')],
        // (Decimal-list `sum()` is now modelled — Phase 70 — so the former "skips loudly" boundary test
        // moved to the P70 group below as a verifying example.)

        // ---------- Phase 68: financial conservation & no-cents-lost proofs ----------
        // "No money is lost in an account transfer": the total across two BigDecimal balances is
        // invariant. Z3's exact Real sort models BigDecimal +/- faithfully, so this is a real proof.
        [group: 'P68 financial', name: 'transfer conserves total (no money lost)', ok: true,
         src: tc('''class Bank {
                       BigDecimal alice
                       BigDecimal bob
                       @Requires({ amt >= 0.0 && amt <= alice })
                       @Ensures({ alice + bob == old.alice + old.bob })
                       void transfer(BigDecimal amt) { alice = alice - amt; bob = bob + amt }
                   }''')],
        // The proof is NOT vacuous: a transfer that skims a cent (the classic "salami slice") is
        // caught — the total drops by 0.01, so conservation refutes. (This needed the Phase 67
        // decimal-assignment fix: an int-shadowed field write used to hide the skim.)
        [group: 'P68 financial', name: 'salami-slice skim is caught (refutes)',
         expect: 'Cannot prove postcondition',
         src: tc('''class Bank {
                       BigDecimal alice
                       BigDecimal bob
                       @Requires({ amt >= 0.0 })
                       @Ensures({ alice + bob == old.alice + old.bob })
                       void transfer(BigDecimal amt) { alice = alice - amt; bob = bob + amt - 0.01 }
                   }''')],
        // "No fractional cents are syphoned in an interest calculation": modelling money as integer
        // cents, the credited (floored) amount plus the retained remainder equals the exact interest
        // — nothing vanishes. (Integer cents is the soundest money model; the framework is strongest here.)
        [group: 'P68 financial', name: 'interest credits every cent (round-trip)', ok: true,
         src: tc('''class C {
                       @Requires({ principal >= 0 && rateNum >= 0 && rateDen > 0 })
                       @Ensures({ result * rateDen + (principal * rateNum) % rateDen == principal * rateNum })
                       static int interestCents(int principal, int rateNum, int rateDen) {
                           (principal * rateNum).intdiv(rateDen)
                       }
                   }''')],
        // The retained remainder is a real, bounded fraction of a cent — accounted for, not pocketed.
        [group: 'P68 financial', name: 'interest remainder is bounded [0, den)', ok: true,
         src: tc('''class C {
                       @Requires({ principal >= 0 && rateNum >= 0 && rateDen > 0 })
                       @Ensures({ result >= 0 && result < rateDen })
                       static int leftoverCents(int principal, int rateNum, int rateDen) {
                           (principal * rateNum) % rateDen
                       }
                   }''')],
        // Soundness anchor: a calc claiming it credits the *exact* interest (no remainder) is refuted
        // whenever a remainder exists — the framework catches the lost fractional cents.
        [group: 'P68 financial', name: 'claiming exact credit (losing remainder) refutes',
         expect: 'Cannot prove postcondition',
         src: tc('''class C {
                       @Requires({ principal >= 0 && rateNum >= 0 && rateDen > 0 })
                       @Ensures({ result * rateDen == principal * rateNum })
                       static int interestCents(int principal, int rateNum, int rateDen) {
                           (principal * rateNum).intdiv(rateDen)
                       }
                   }''')],

        // ---------- Phase 69: sum-under-store law → N-account conservation ----------
        // "No money is lost across N accounts": a transfer between any two cells of an int[] of
        // balances (cents) conserves the total. The per-store sum law makes the two compensating
        // stores cancel, so `bal.sum()` is invariant — stated here against the entry total.
        [group: 'P69 sum-under-store', name: 'N-account transfer conserves total (precondition)', ok: true,
         src: tc('''class Bank {
                       int[] bal
                       @Requires({ 0 <= i && i < bal.length && 0 <= j && j < bal.length && i != j && bal.sum() == 100 })
                       @Ensures({ bal.sum() == 100 })
                       void transfer(int i, int j, int amt) { bal[i] = bal[i] - amt; bal[j] = bal[j] + amt }
                   }''')],
        // The natural "no money lost" form: the total after equals the total before, via old.bal.sum().
        [group: 'P69 sum-under-store', name: 'N-account conservation via old.bal.sum()', ok: true,
         src: tc('''class Bank {
                       int[] bal
                       @Requires({ 0 <= i && i < bal.length && 0 <= j && j < bal.length && i != j })
                       @Ensures({ bal.sum() == old.bal.sum() })
                       void transfer(int i, int j, int amt) { bal[i] = bal[i] - amt; bal[j] = bal[j] + amt }
                   }''')],
        // Not vacuous: a transfer that skims a cent is caught — the build still fails, though as a loud
        // "could not decide" rather than a witnessed counterexample. Refuting a sum-aggregated equality is
        // the weak direction (Z3 must construct a model of the quantified sum axioms → timeout), and the
        // integer-only PBT fallback can't evaluate the array. So the conservation VERIFIES cleanly while a
        // violation fails as UNKNOWN — honest (never a silent pass), if without a counterexample.
        [group: 'P69 sum-under-store', name: 'N-account skim fails the build (could not decide)',
         expect: 'Could not decide postcondition',
         src: tc('''class Bank {
                       int[] bal
                       @Requires({ 0 <= i && i < bal.length && 0 <= j && j < bal.length && i != j })
                       @Ensures({ bal.sum() == old.bal.sum() })
                       void transfer(int i, int j, int amt) { bal[i] = bal[i] - amt; bal[j] = bal[j] + amt - 1 }
                   }''')],

        // ---------- Phase 70: List<BigDecimal>.sum() via Real-element arrays ----------
        // A decimal list's contents are now an `Array Int Real` and `.sum()` a Real-codomain aggregation,
        // so its base/step axioms unfold: the sum of a 2-element list is the sum of its elements.
        [group: 'P70 decimal sum', name: 'List<BigDecimal> sum of two equals their sum', ok: true,
         src: tc('''class C {
                       @Requires({ xs.size() == 2 })
                       @Ensures({ xs.sum() == xs[0] + xs[1] })
                       static void check(List<BigDecimal> xs) { }
                   }''')],
        // The capstone: "no money is lost" over a *dynamic* list of BigDecimal balances — the decimal
        // analogue of the Phase 69 int-cents proof, via the Real sum-under-store law.
        [group: 'P70 decimal sum', name: 'List<BigDecimal> transfer conserves total', ok: true,
         src: tc('''class Fund {
                       List<BigDecimal> bal
                       @Requires({ 0 <= i && i < bal.size() && 0 <= j && j < bal.size() && i != j })
                       @Ensures({ bal.sum() == old.bal.sum() })
                       void transfer(int i, int j, BigDecimal amt) { bal[i] = bal[i] - amt; bal[j] = bal[j] + amt }
                   }''')],
        // Not vacuous: skimming a cent off the credited side breaks conservation. As with the int sum,
        // refuting a sum-aggregated equality is the weak direction, so it fails the build as a loud
        // "could not decide" rather than a witnessed counterexample — never a silent pass.
        [group: 'P70 decimal sum', name: 'List<BigDecimal> skim fails the build (could not decide)',
         expect: 'Could not decide postcondition',
         src: tc('''class Fund {
                       List<BigDecimal> bal
                       @Requires({ 0 <= i && i < bal.size() && 0 <= j && j < bal.size() && i != j })
                       @Ensures({ bal.sum() == old.bal.sum() })
                       void transfer(int i, int j, BigDecimal amt) { bal[i] = bal[i] - amt; bal[j] = bal[j] + amt - 0.01 }
                   }''')],

        // ---------- Phase 76: List<BigDecimal>.max() / .min() — the Real witnessed extremum ----------
        // The sort-generic maxMinOf now serves Real (BigDecimal) contents, not just Int (Phase 60): a fresh
        // `r` that bounds every element AND is achieved by one, with the order comparisons reused (le/ge are
        // arithmetic-polymorphic over Int and Real in Z3). Composes with the Phase-70 decimal `.sum()`.
        [group: 'P76 decimal max/min', name: 'decimal max bounds every element', ok: true,
         src: tc('''class C {
                       @Requires({ xs.size() > 0 })
                       @Ensures({ (0..<xs.size()).every { xs[it] <= xs.max() } })
                       static void check(List<BigDecimal> xs) { }
                   }''')],
        [group: 'P76 decimal max/min', name: 'decimal max is achieved by some element', ok: true,
         src: tc('''class C {
                       @Requires({ xs.size() > 0 })
                       @Ensures({ (0..<xs.size()).any { xs[it] == xs.max() } })
                       static void check(List<BigDecimal> xs) { }
                   }''')],
        [group: 'P76 decimal max/min', name: 'decimal min bounds every element (>=)', ok: true,
         src: tc('''class C {
                       @Requires({ xs.size() > 0 })
                       @Ensures({ (0..<xs.size()).every { xs[it] >= xs.min() } })
                       static void check(List<BigDecimal> xs) { }
                   }''')],
        // Both extrema compose: max >= min for any non-empty decimal list (min is achieved at some j, and
        // max bounds that same element).
        [group: 'P76 decimal max/min', name: 'decimal max >= min (non-empty)', ok: true,
         src: tc('''class C {
                       @Requires({ xs.size() > 0 })
                       @Ensures({ xs.max() >= xs.min() })
                       static void check(List<BigDecimal> xs) { }
                   }''')],
        // Concrete shape: over a 2-element list the max bounds both entries.
        [group: 'P76 decimal max/min', name: 'decimal max of pair bounds both', ok: true,
         src: tc('''class C {
                       @Requires({ xs.size() == 2 })
                       @Ensures({ xs.max() >= xs[0] && xs.max() >= xs[1] })
                       static void check(List<BigDecimal> xs) { }
                   }''')],

        // ---------- Phase 77: FP-element arrays (double[]) — element reads + predicates ----------
        // A `double[]`'s contents are now an `Array Int FP` (sortFor double → IEEE sort), so `xs[i]` reads
        // are FP and comparisons route to the FP theory. A bounded ∀ over the elements instantiates. (We use
        // `double[]` not `List<Double>` so the contract closures don't hit @TypeChecked generics erasure.)
        [group: 'P77 fp arrays', name: 'double[]: every >= 0 ⇒ xs[0] >= 0', ok: true,
         src: tc('''class C {
                       @Requires({ xs.length > 0 && (0..<xs.length).every { xs[it] >= 0.0d } })
                       @Ensures({ xs[0] >= 0.0d })
                       static void check(double[] xs) { }
                   }''')],
        [group: 'P77 fp arrays', name: 'double[]: every > 0 does not prove >= 1 (FP)', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                       @Requires({ xs.length > 0 && (0..<xs.length).every { xs[it] > 0.0d } })
                       @Ensures({ xs[0] >= 1.0d })
                       static void check(double[] xs) { }
                   }''')],
        // FP element comparison composes across two indices (no scalar literal needed).
        [group: 'P77 fp arrays', name: 'double[]: sorted-adjacent ⇒ xs[0] <= xs[1]', ok: true,
         src: tc('''class C {
                       @Requires({ xs.length >= 2 && xs[0] <= xs[1] })
                       @Ensures({ xs[1] >= xs[0] })
                       static void check(double[] xs) { }
                   }''')],
        // FP max/min: the witnessed extremum over double[] — but FP is not totally ordered, so the bound
        // holds only under a no-NaN guard. Under `!Double.isNaN`, max bounds every element and max >= min.
        [group: 'P77 fp arrays', name: 'double[] max bounds every element (no-NaN)', ok: true,
         src: tc('''class C {
                       @Requires({ xs.length > 0 && (0..<xs.length).every { !Double.isNaN(xs[it]) } })
                       @Ensures({ (0..<xs.length).every { xs[it] <= xs.max() } })
                       static void check(double[] xs) { }
                   }''')],
        [group: 'P77 fp arrays', name: 'double[] max >= min (no-NaN)', ok: true,
         src: tc('''class C {
                       @Requires({ xs.length > 0 && (0..<xs.length).every { !Double.isNaN(xs[it]) } })
                       @Ensures({ xs.max() >= xs.min() })
                       static void check(double[] xs) { }
                   }''')],
        // Soundness: WITHOUT the no-NaN guard, max does NOT bound every element — a NaN element refutes
        // (NaN <= max is false in IEEE). The verifier refuses it rather than assume well-orderedness.
        [group: 'P77 fp arrays', name: 'double[] max bound needs no-NaN (else refutes)', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                       @Requires({ xs.length > 0 })
                       @Ensures({ (0..<xs.length).every { xs[it] <= xs.max() } })
                       static void check(double[] xs) { }
                   }''')],

        // ---------- Phase 71: soundness hardening (boolean fields, vacuous preconditions) ----------
        // A boolean *field* write used to crash Z3 (intVar fresh handle vs a Bool rhs); now it's a
        // boolVar, so `b == old.b` after `b = !b` correctly refutes — and the correct claim verifies.
        [group: 'P71 soundness', name: 'boolean field write refutes (no crash)',
         expect: 'Cannot prove postcondition',
         src: tc('class C { boolean b; @Ensures({ b == old.b }) void f() { b = !b } }')],
        [group: 'P71 soundness', name: 'boolean field flip verified', ok: true,
         src: tc('class C { boolean b; @Ensures({ b == !old.b }) void f() { b = !b } }')],
        // A self-contradictory @Requires can never hold, so the @Ensures verifies vacuously — the silent
        // pass the project fears most. Now flagged loudly (asserting the precondition is UNSAT).
        [group: 'P71 soundness', name: 'vacuous precondition flagged', expect: 'Vacuous precondition',
         src: tc('class C { @Requires({ x > 5 }) @Requires({ x < 0 }) @Ensures({ result == 999 }) static int f(int x) { x } }')],
        // A satisfiable (even tight) precondition is NOT flagged — the check fires only on a definite UNSAT.
        [group: 'P71 soundness', name: 'satisfiable precondition not flagged', ok: true,
         src: tc('class C { @Requires({ x == 5 }) @Ensures({ result == 5 }) static int f(int x) { x } }')],

        // Soundness anchors from the systematic adversarial sweep — each MUST refute / flag (a clean
        // verify here would be a silent false-proof). They close the coverage blind spots that let the
        // boolean-field and decimal-assignment bugs exist: old-fidelity per kind, mutation/size laws,
        // overflow, string contents, recursion-without-measure, per-element loop reasoning, and vacuity
        // across sorts.
        [group: 'P71 soundness', name: 'anchor: int field old-fidelity', expect: 'Cannot prove postcondition',
         src: tc('class C { int n; @Ensures({ n == old.n }) void f() { n = n - 1 } }')],
        [group: 'P71 soundness', name: 'anchor: int[] element old-fidelity', expect: 'Cannot prove postcondition',
         src: tc('class C { int[] a; @Requires({ a.length > 0 }) @Ensures({ a[0] == old.a[0] }) void f() { a[0] = a[0] + 1 } }')],
        [group: 'P71 soundness', name: 'anchor: set remove non-member size', expect: 'Cannot prove postcondition',
         src: tc('class C { Set<Integer> s; @Requires({ !(7 in s) }) @Ensures({ s.size() == old.s.size() - 1 }) void f() { s.remove(7) } }')],
        [group: 'P71 soundness', name: 'anchor: map put grows size', expect: 'Cannot prove postcondition',
         src: tc('class C { Map<Integer,Integer> m; @Requires({ !(7 in m) }) @Ensures({ m.size() == old.m.size() }) void f() { m[7] = 1 } }')],
        [group: 'P71 soundness', name: 'anchor: overflow under @CheckOverflow', expect: 'overflow',
         src: tc('class C { @CheckOverflow @Ensures({ result == a + b }) static int f(int a, int b) { a + b } }')],
        [group: 'P71 soundness', name: 'anchor: substring length false', expect: 'Cannot prove postcondition',
         src: tc('class C { @Requires({ s != null && s.length() >= 3 }) @Ensures({ s.substring(0, 2).length() == 3 }) static int f(String s) { 0 } }')],
        // Without a @Decreases measure the recursive result is opaque — the postcondition is skipped
        // loudly (never silently trusted), so a false `result == 0` claim isn't proven.
        [group: 'P71 soundness', name: 'anchor: recursion without @Decreases skips', expect: 'Skipped verification of postcondition',
         src: tc('class C { @Ensures({ result == 0 }) static int f(int n) { if (n <= 0) return 0; return f(n - 1) } }')],
        [group: 'P71 soundness', name: 'anchor: for-in element not strengthened', expect: 'holds for every element',
         src: tc('class C { @Requires({ xs.every { it >= 0 } }) static void f(List<Integer> xs) { @groovy.contracts.Invariant({ x > 0 }) for (x in xs) { } } }')],
        [group: 'P71 soundness', name: 'anchor: decimal contradiction vacuous', expect: 'Vacuous precondition',
         src: tc('class C { @Requires({ x == 1.0 && x == 2.0 }) @Ensures({ result == 9 }) static int f(BigDecimal x) { 9 } }')],
        [group: 'P71 soundness', name: 'anchor: null contradiction vacuous', expect: 'Vacuous precondition',
         src: tc('class C { @Requires({ s == null && s != null }) @Ensures({ result == 1 }) static int f(String s) { 1 } }')],
        [group: 'P71 soundness', name: 'anchor: decimal conservation not vacuous', expect: 'Could not decide postcondition',
         src: tc('class C { List<BigDecimal> b; @Requires({ 0 <= i && i < b.size() }) @Ensures({ b.sum() == old.b.sum() }) void f(int i, BigDecimal amt) { b[i] = b[i] + amt } }')],
        // double is IEEE-754: `(a + b) - b == a` holds in exact Int/Real but NOT at runtime. Modelled
        // faithfully with Z3's FP theory (Phase 73), the verifier *refutes* it — proving the rounding
        // non-associativity rather than silently "proving" the false exact identity.
        [group: 'P71 soundness', name: 'anchor: FP non-associativity refuted', expect: 'Cannot prove postcondition',
         src: tc('class C { @Ensures({ result == a }) static double f(double a, double b) { (a + b) - b } }')],

        // ---------- Phase 73: IEEE-754 floating point (double/float via Z3's FP theory) ----------
        // The flagship pairing — the same expression, two number models, both proven:
        //   BigDecimal is exact decimal, so 0.1 + 0.2 IS 0.3;
        //   double is IEEE-754, so 0.1d + 0.2d is NOT 0.3d (it is 0.30000000000000004).
        [group: 'P73 floating point', name: 'BigDecimal: 0.1 + 0.2 == 0.3 (exact)', ok: true,
         src: tc('class C { @Ensures({ result == 0.3 }) static BigDecimal f() { 0.1 + 0.2 } }')],
        [group: 'P73 floating point', name: 'double: 0.1d + 0.2d != 0.3d (IEEE-754)', ok: true,
         src: tc('class C { @Ensures({ result != 0.3d }) static double f() { 0.1d + 0.2d } }')],
        // Soundness anchor: claiming the double sum IS 0.3 is refuted (it genuinely is not).
        [group: 'P73 floating point', name: 'double: claiming == 0.3d refutes', expect: 'Cannot prove postcondition',
         src: tc('class C { @Ensures({ result == 0.3d }) static double f() { 0.1d + 0.2d } }')],
        // FP exact cases still prove (powers of two are representable).
        [group: 'P73 floating point', name: 'double: 0.5d * 2.0d == 1.0d (exact)', ok: true,
         src: tc('class C { @Ensures({ result == 1.0d }) static double f() { 0.5d * 2.0d } }')],
        // No-NaN / finiteness — the highest-value FP safety class: a finite input stays non-NaN.
        [group: 'P73 floating point', name: 'double: finite input ⇒ result not NaN', ok: true,
         src: tc('class C { @Requires({ Double.isFinite(x) }) @Ensures({ !Double.isNaN(result) }) static double g(double x) { x + x } }')],
        // ...and an unconstrained input can be NaN, so the no-NaN claim refutes without the guard.
        [group: 'P73 floating point', name: 'double: no-NaN needs the finite guard', expect: 'Cannot prove postcondition',
         src: tc('class C { @Ensures({ !Double.isNaN(result) }) static double g(double x) { x + x } }')],
        // IEEE equality: NaN != NaN. `x == x` is false for a NaN, so claiming it holds for any x refutes.
        [group: 'P73 floating point', name: 'double: x == x not universal (NaN)', expect: 'Cannot prove postcondition',
         src: tc('class C { @Ensures({ x == x }) static double g(double x) { x } }')],
        // Math.sqrt / Math.abs (Z3 fp.sqrt / fp.abs): sqrt of a non-negative is non-negative and not NaN.
        [group: 'P73 floating point', name: 'Math.sqrt of non-negative is non-negative', ok: true,
         src: tc('class C { @Requires({ x >= 0.0d }) @Ensures({ result >= 0.0d }) static double f(double x) { Math.sqrt(x) } }')],
        [group: 'P73 floating point', name: 'Math.sqrt of non-negative is not NaN', ok: true,
         src: tc('class C { @Requires({ x >= 0.0d }) @Ensures({ !Double.isNaN(result) }) static double f(double x) { Math.sqrt(x) } }')],
        // ...but sqrt of a possibly-negative input CAN be NaN — the no-NaN claim refutes without the guard.
        [group: 'P73 floating point', name: 'Math.sqrt without guard can be NaN', expect: 'Cannot prove postcondition',
         src: tc('class C { @Ensures({ !Double.isNaN(result) }) static double f(double x) { Math.sqrt(x) } }')],
        // Math.abs is non-negative for any non-NaN input, and never negative (soundness anchor).
        [group: 'P73 floating point', name: 'Math.abs of non-NaN is non-negative', ok: true,
         src: tc('class C { @Requires({ !Double.isNaN(x) }) @Ensures({ result >= 0.0d }) static double f(double x) { Math.abs(x) } }')],
        [group: 'P73 floating point', name: 'Math.abs claiming negative refutes', expect: 'Cannot prove postcondition',
         src: tc('class C { @Requires({ !Double.isNaN(x) }) @Ensures({ result < 0.0d }) static double f(double x) { Math.abs(x) } }')],

        // ---------- Phase 74: Range.containsWithinBounds — bounds-only interval predicate ----------
        // The bounds-only test (ignores the step) lowers to min(lo,hi) <= v <= max(lo,hi) in v's sort.
        // Decimal bounds ride the exact-Real comparison path; the step is irrelevant (4 ∉ {1,3,5} as a
        // stepped member, but it IS within the [1,5] bounds — exactly what separates this from contains).
        [group: 'P74 range bounds', name: 'decimal range: 1.5..4 within-bounds 2', ok: true,
         src: tc('class C { @Ensures({ (1.5..4).containsWithinBounds(2) }) static void m() { } }')],
        [group: 'P74 range bounds', name: 'NumberRange(1,5,2) within-bounds 4 (step ignored)', ok: true,
         src: tc('class C { @Ensures({ new NumberRange(1, 5, 2).containsWithinBounds(4) }) static void m() { } }')],
        // Outside the interval refutes (7 > 5).
        [group: 'P74 range bounds', name: 'NumberRange(1,5,2) within-bounds 7 refutes', expect: 'Cannot prove postcondition',
         src: tc('class C { @Ensures({ new NumberRange(1, 5, 2).containsWithinBounds(7) }) static void m() { } }')],
        // Symbolic — not constant folding: a param constrained into [1,5] is provably within bounds.
        [group: 'P74 range bounds', name: 'symbolic: x in [1,5] ⇒ (1..5) within-bounds x', ok: true,
         src: tc('class C { @Requires({ x >= 1 && x <= 5 }) @Ensures({ (1..5).containsWithinBounds(x) }) static void m(int x) { } }')],
        // ...and only the lower guard is not enough — x could exceed 5, so it refutes.
        [group: 'P74 range bounds', name: 'symbolic: x >= 1 alone does not prove within-bounds', expect: 'Cannot prove postcondition',
         src: tc('class C { @Requires({ x >= 1 }) @Ensures({ (1..5).containsWithinBounds(x) }) static void m(int x) { } }')],
        // A character range needs String ordering (not modelled) — honest loud skip, not a crash.
        [group: 'P74 range bounds', name: 'char range within-bounds skips loudly', expect: 'outside fragment',
         src: tc("class C { @Ensures({ ('a'..'c').containsWithinBounds('b') }) static void m() { } }")],
        // --- All four delimited-range forms, with per-endpoint inclusivity (Groovy 4+ `<..` / `..<`). ---
        // The forms below all denote {2,3,4}, so each contains 2 within bounds; the endpoint forms differ
        // only at the boundary, which the discriminating cases pin down.
        [group: 'P74 range bounds', name: 'left-open 1<..4 within-bounds 2', ok: true,
         src: tc('class C { @Ensures({ (1<..4).containsWithinBounds(2) }) static void m() { } }')],
        [group: 'P74 range bounds', name: 'open 1<..<5 within-bounds 3', ok: true,
         src: tc('class C { @Ensures({ (1<..<5).containsWithinBounds(3) }) static void m() { } }')],
        [group: 'P74 range bounds', name: 'right-open 2..<5 includes left endpoint 2', ok: true,
         src: tc('class C { @Ensures({ (2..<5).containsWithinBounds(2) }) static void m() { } }')],
        // Boundary discrimination: left-exclusivity EXCLUDES the left endpoint, so this refutes...
        [group: 'P74 range bounds', name: 'left-open 1<..4 excludes 1 (refutes)', expect: 'Cannot prove postcondition',
         src: tc('class C { @Ensures({ (1<..4).containsWithinBounds(1) }) static void m() { } }')],
        // ...and right-exclusivity excludes the right endpoint.
        [group: 'P74 range bounds', name: 'right-open 2..<5 excludes 5 (refutes)', expect: 'Cannot prove postcondition',
         src: tc('class C { @Ensures({ (2..<5).containsWithinBounds(5) }) static void m() { } }')],
        [group: 'P74 range bounds', name: 'open 1<..<5 excludes both ends (refutes at 5)', expect: 'Cannot prove postcondition',
         src: tc('class C { @Ensures({ (1<..<5).containsWithinBounds(5) }) static void m() { } }')],
        // Symbolic + exclusivity: the strict lower guard `x > 1` is exactly what a left-open range needs.
        [group: 'P74 range bounds', name: 'symbolic: x in (1,4] ⇒ (1<..4) within-bounds x', ok: true,
         src: tc('class C { @Requires({ x > 1 && x <= 4 }) @Ensures({ (1<..4).containsWithinBounds(x) }) static void m(int x) { } }')],
        // ...and a non-strict `x >= 1` is NOT enough — x == 1 is excluded by the open left, so it refutes.
        [group: 'P74 range bounds', name: 'symbolic: x >= 1 does not prove left-open membership', expect: 'Cannot prove postcondition',
         src: tc('class C { @Requires({ x >= 1 && x <= 4 }) @Ensures({ (1<..4).containsWithinBounds(x) }) static void m(int x) { } }')],
        // Open decimal range (NumberRange) is pure-bounds, so any real value is exact.
        [group: 'P74 range bounds', name: 'decimal open 1.5<..<4.5 within-bounds 2', ok: true,
         src: tc('class C { @Ensures({ (1.5<..<4.5).containsWithinBounds(2) }) static void m() { } }')],
        // Pure bounds for every range kind (the documented `Range` contract): a non-integer value is
        // within the integer range's bounds, so it proves. (Stock IntRange.containsWithinBounds currently
        // delegates to `contains` and returns false here — a Groovy bug raised upstream; the verifier
        // models the documented pure-bounds semantics, consistent with NumberRange and the coming fix.)
        [group: 'P74 range bounds', name: 'int range within-bounds 2.5 (pure bounds, per contract)', ok: true,
         src: tc('class C { @Ensures({ (2..4).containsWithinBounds(2.5) }) static void m() { } }')],
        // The decimal-typed equivalent already agrees today — same interval, same answer (no type dependence).
        [group: 'P74 range bounds', name: 'decimal range within-bounds 2.5 agrees', ok: true,
         src: tc('class C { @Ensures({ (2.0..4.0).containsWithinBounds(2.5) }) static void m() { } }')],
        // Out of bounds still refutes regardless of integrality.
        [group: 'P74 range bounds', name: 'int range within-bounds 4.5 refutes', expect: 'Cannot prove postcondition',
         src: tc('class C { @Ensures({ (2..4).containsWithinBounds(4.5) }) static void m() { } }')],

        // ---------- GROOVY-12066: contracts on a *static nested* class (upstream fix) ----------
        // `@Invariant`/`@Requires`/`@Ensures` on a static nested class used to NPE at compile time in
        // groovy-contracts' DynamicSetterInjectionVisitor (upstream, independent of groovy-verify). Now
        // fixed; these confirm the class compiles AND the verifier engages on the nested class normally.
        [group: 'nested static (GROOVY-12066)', name: 'static nested @Invariant established by ctor verifies', ok: true,
         src: HDR + '''
            class Outer {
                @TypeChecked(extensions = 'verification.VerifyChecker')
                @Invariant({ balance >= 0 })
                static class Account {
                    int balance
                    @Requires({ b >= 0 })
                    Account(int b) { balance = b }
                }
            }
         '''.stripIndent()],
        // The same nested class without the precondition cannot establish the invariant (b may be < 0).
        [group: 'nested static (GROOVY-12066)', name: 'static nested @Invariant unestablished refutes', expect: 'invariant',
         src: HDR + '''
            class Outer {
                @TypeChecked(extensions = 'verification.VerifyChecker')
                @Invariant({ balance >= 0 })
                static class Account {
                    int balance
                    Account(int b) { balance = b }
                }
            }
         '''.stripIndent()],

        // ---------- Phase 75: infinite-stream every/any — bounded unroll + symbolic-limit induction --------
        // You cannot TEST a property of every element of an infinite stream (a true `every` over an unbounded
        // source never returns). DUAL runtime+verify needs a `.limit(n)`/`.take(n)` so the contract degrades
        // to a *terminating* runtime spot-check; the verifier proves far past that depth. A literal limit
        // unrolls (exact); a symbolic limit uses induction (base + preservation), proving it for all n.
        [group: 'P75 streams', name: 'bounded: limit(10) all even (unroll)', ok: true,
         src: tcs('class C { @Ensures({ Stream.iterate(0, { n -> n + 2 }).limit(10).every{ int v -> v % 2 == 0 } }) static void m() { } }')],
        [group: 'P75 streams', name: 'bounded: limit(10) all < 5 refutes (element 6)', expect: 'Cannot prove postcondition',
         src: tcs('class C { @Ensures({ Stream.iterate(0, { n -> n + 2 }).limit(10).every{ int v -> v < 5 } }) static void m() { } }')],
        [group: 'P75 streams', name: 'bounded: any element == 6 (witness in first 10)', ok: true,
         src: tcs('class C { @Ensures({ Stream.iterate(0, { n -> n + 2 }).limit(10).any{ int v -> v == 6 } }) static void m() { } }')],
        // The headline, made dual-safe: runtime spot-checks the first `n`, the verifier proves EVERY element
        // even by induction (reaching past the runtime's depth). `.limit(n)` keeps the runtime terminating.
        [group: 'P75 streams', name: 'limit(n): every element even (induction beyond n)', ok: true,
         src: tcs('class C { @Requires({ n >= 0 }) @Ensures({ Stream.iterate(0, { k -> k + 2 }).limit(n).every{ int v -> v % 2 == 0 } }) static void m(int n) { } }')],
        // No-overflow / boundedness forever: (k+1)%10 stays in [0,10) for ALL elements — runtime checks n,
        // verifier proves the unbounded invariant, so the `+1` provably never overflows.
        [group: 'P75 streams', name: 'limit(n): (k+1)%10 stays in [0,10) for all elements', ok: true,
         src: tcs('class C { @Requires({ n >= 0 }) @Ensures({ Stream.iterate(0, { k -> (k + 1) % 10 }).limit(n).every{ int v -> v >= 0 && v < 10 } }) static void m(int n) { } }')],
        // Honest negative: a monotone counter has no finite bound, so the claim is not inductive (and false
        // at the boundary) — the verifier refuses it rather than hand-wave.
        [group: 'P75 streams', name: 'limit(n): monotone counter < 1000000 not provable', expect: 'Cannot prove postcondition',
         src: tcs('class C { @Requires({ n >= 0 }) @Ensures({ Stream.iterate(0, { k -> k + 1 }).limit(n).every{ int v -> v < 1000000 } }) static void m(int n) { } }')],
        // DUAL-SAFETY GATE: an unbounded terminal `every` (no .limit/.take) would loop forever at runtime, so
        // it is NOT blessed as verified — it skips loudly, nudging the developer to add a bound.
        [group: 'P75 streams', name: 'no limit: unbounded every skips loudly (would hang at runtime)', expect: 'outside fragment',
         src: tcs('class C { @Ensures({ Stream.iterate(0, { n -> n + 2 }).every{ int v -> v % 2 == 0 } }) static void m() { } }')],
        // Soundness gate: the induction encoding is stronger than `every`, so it must NOT fire in negative
        // polarity. Under a negation it is not marked → the postcondition degrades to the runtime check only.
        [group: 'P75 streams', name: 'limit(n) every under negation skips loudly', expect: 'outside fragment',
         src: tcs('class C { @Requires({ n >= 0 }) @Ensures({ !(Stream.iterate(0, { k -> k + 1 }).limit(n).every{ int v -> v < 5 }) }) static void m(int n) { } }')],
        // Soundness anchor: the base case (the seed) matters — an odd seed refutes "every element even",
        // even though the step k*2 preserves evenness. Induction needs BOTH base and preservation.
        [group: 'P75 streams', name: 'limit(n): odd seed refutes evenness (base case)', expect: 'Cannot prove postcondition',
         src: tcs('class C { @Requires({ n >= 0 }) @Ensures({ Stream.iterate(1, { k -> k * 2 }).limit(n).every{ int v -> v % 2 == 0 } }) static void m(int n) { } }')],

        // ---------- Phase 62: bounded property-based refutation when the solver says UNKNOWN ----------
        // `result == Fib.of(n)` is the weak refutation direction (recurrence-axiom timeout → UNKNOWN);
        // bounded testing of the executable contract finds the concrete failing input f(2): the body
        // returns 2 but Fib.of(2) is 1. UNKNOWN becomes a runnable repro.
        [group: 'P62 pbt', name: 'Fib UNKNOWN refuted by testing (fails on f(2))',
         expect: 'fails on: f(2)',
         src: tc('class C { @Requires({ n >= 0 }) @Ensures({ result == Fib.of(n) }) static int f(int n) { n } }')],
        // The diagnostic is explicit that the counterexample came from testing, not a proof.
        [group: 'P62 pbt', name: 'Fib off-by-const UNKNOWN refuted by testing',
         expect: 'counterexample found by bounded testing',
         src: tc('class C { @Requires({ n >= 2 }) @Ensures({ result == Fib.of(n) + 1 }) static int f(int n) { n } }')],
        // Honest bail: an array-`sum()` postcondition is UNKNOWN (aggregation-axiom timeout), but the
        // concrete tester can't evaluate array contents, so it finds nothing and the diagnostic stays an
        // honest "could not decide" — bounded testing never fabricates a false refutation outside its
        // (integer-only) fragment.
        [group: 'P62 pbt', name: 'array-sum UNKNOWN stays could-not-decide (testing bails)',
         expect: 'Could not decide postcondition',
         src: tc('class C { @Requires({ a != null && a.length > 0 }) @Ensures({ result == a.sum() }) static int f(int[] a) { 0 } }')],

        // ---------- Dafny ports — canonical tutorial / VSComp examples (external corpus) ----------
        // SumMax (VSComp 2010, Problem 1; Leino): compute sum and max in one pass and prove the
        // NONLINEAR bound `sum <= N * max`. The whole proof rides on the NIA loop invariant
        // `sum <= i * max` (Phase 48). Dafny's `returns (sum, max)` is a NAMED tuple, so the faithful
        // Groovy is the map-as-named-tuple idiom (Phase 83): `return [sum: …, max: …]` with
        // `result.sum` / `result.max` — self-documenting where positional `result.v1` / `result.v2`
        // aren't. With the return type declared `Map<String, Integer>`, the map values read back as
        // `Integer` inside the @Ensures closure (GROOVY-12071 restored the closure's generic types), so the
        // arithmetic `n * max` and the `<=` type-check with NO cast. Different shape from below_zero (a sum
        // biconditional) and max_element (a witnessed extremum): an INEQUALITY relating two running aggregates.
        [group: 'Dafny port', name: 'SumMax (VSComp10 P1): sum <= n*max', ok: true,
         src: tc('''class C {
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
                   }''')],
        // A wrong bound (`sum <= (n-1)*max`) refutes — the NIA invariant proves only the true bound.
        [group: 'Dafny port', name: 'SumMax wrong bound refutes', expect: 'fails on: sumMax(new int[0], 0)',
         src: tc('''class C {
                       @Requires({ 0 <= n && a.length == n && (0..<n).every { a[it] >= 0 } })
                       @Ensures({ result.sum <= (n - 1) * result.max })
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
                   }''')],
        // Find (linear search, Dafny tutorial): the "not present => forall a[k] != key" spec — binary
        // search's postcondition WITHOUT sortedness, so it isolates exactly what binary search adds. The
        // in-loop early `return i` (Phase 49b) witnesses the found case; the invariant carries the
        // universal to the `return -1` path; preservation extends (0..<i) to (0..<i+1) in one
        // instantiation (no transitivity).
        [group: 'Dafny port', name: 'Find (linear search): index<0 => no element equals key', ok: true,
         src: tc('''class C {
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
                   }''')],
        // Claiming the found index holds a DIFFERENT key refutes (the early-return binds result = i with
        // a[i] == key, so a[result] != key is false on that path).
        [group: 'Dafny port', name: 'Find wrong found-claim refutes', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                       @Ensures({ result >= 0 ==> result < a.length && a[result] != key })
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
                   }''')],
        // BinarySearch (Dafny tutorial) — the VERBATIM textbook shape, `else return mid` inside the loop,
        // verifies END TO END: both postcondition directions, the excluded-region universal preserved
        // across the narrowing, every `a[mid]` bound, and termination. Sortedness is the NATIVE
        // `a.isSorted()` (Groovy 6 GDK; native int[]/long[] overloads) — it lowers to the same
        // flat multi-pattern axiom as `Sorted.ascending(a)`. Three fixes made it reachable: (1) that
        // multi-pattern axiom (deterministic gap fact), (2) a dischargeRegion fix so an obligation nested
        // in an `else if` keeps the `int mid = …` binding (the spurious mid=-1 IOOBE), and (3) Phase 49c —
        // lifting a `return` nested in a tail if/else chain into the top-level early-exit shape Phase 49b
        // handles. Matches Dafny's source structurally.
        [group: 'Dafny port', name: 'BinarySearch (textbook return mid): both directions + bounds + termination', ok: true,
         src: tc('''class C {
                       @Requires({ a.isSorted() })
                       @Ensures({ result < 0 ==> (0..<a.length).every { a[it] != value } })
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
                   }''')],
        // Drop the sortedness precondition and the proof genuinely fails — preservation refutes (without
        // `Sorted` the excluded-region invariant is not preserved by the narrowing). Confirms the proof
        // actually rests on sortedness, not luck.
        [group: 'Dafny port', name: 'BinarySearch without sortedness refutes',
         expect: 'Cannot prove loop invariant is preserved',
         src: tc('''class C {
                       @Ensures({ result < 0 ==> (0..<a.length).every { a[it] != value } })
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
                   }''')],
        // The in-loop `return mid` genuinely exits with a[mid]==value: claiming the found index holds a
        // DIFFERENT value refutes (the lifted early-exit's @Ensures is checked on its own path).
        [group: 'Dafny port', name: 'BinarySearch wrong found-claim refutes', expect: 'Cannot prove',
         src: tc('''class C {
                       @Requires({ a.isSorted() })
                       @Ensures({ result >= 0 ==> a[result] != value })
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
                   }''')],
        // Focused regression for the dischargeRegion nested-`else if` fix: an index obligation in the
        // else-if condition must see a `mid` declared before the if. Before the fix this false-positived
        // a spurious IndexOutOfBounds (mid havoced → mid=-1).
        [group: 'Dafny port', name: 'nested else-if index obligation sees prior mid (no false IOOBE)', ok: true,
         src: tc('''class C {
                       static int f(int[] a, int value) {
                           int low = 0, high = a.length
                           @Invariant({ 0 <= low && low <= high && high <= a.length })
                           @Decreases({ high - low })
                           while (low < high) {
                               int mid = low + (high - low).intdiv(2)
                               if (a[mid] < value) low = mid + 1
                               else if (value < a[mid]) high = mid
                               else low = high
                           }
                           return low
                       }
                   }''')],
        // Phase 49c boundary: a `return` nested in an if/else chain that is NOT in tail position (a
        // statement follows it in the body) is out of the slice's scope — it skips LOUDLY rather than
        // being mis-modelled. The desugar only lifts a tail-position chain.
        [group: 'Dafny port', name: 'non-tail nested return skips loudly (honest)',
         expect: 'unsupported statement ReturnStatement',
         src: tc('''class C {
                       @Ensures({ result >= -1 })
                       static int f(int[] a, int value) {
                           int i = 0
                           @Invariant({ 0 <= i && i <= a.length })
                           @Decreases({ a.length - i })
                           while (i < a.length) {
                               if (a[i] == value) { if (i >= 0) return i }
                               i = i + 1
                           }
                           return -1
                       }
                   }''')],

        // ---------- Sorted helper — the canonical sortedness precondition (flat 2-D, multi-pattern) ----------
        // The random-access GAP FACT: from `Sorted.ascending(a)`, an arbitrary i < j gives a[i] <= a[j] in
        // ONE deterministic instantiation (multi-pattern {a[i], a[j]}). This is the lemma binary search
        // needs from sortedness; the hand-nested `every` got it only via Z3's outer auto-pattern.
        [group: 'Sorted helper', name: 'ascending gives gap fact a[i] <= a[j] (i<j)', ok: true,
         src: tc('''class C {
                       @Requires({ Sorted.ascending(a) && 0 <= i && i < j && j < a.length })
                       @Ensures({ a[i] <= a[j] })
                       static int gap(int[] a, int i, int j) { 0 }
                   }''')],
        // Without sortedness the same claim refutes (so the helper is doing real work, not vacuous).
        [group: 'Sorted helper', name: 'no sortedness => gap fact refutes', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                       @Requires({ 0 <= i && i < j && j < a.length })
                       @Ensures({ a[i] <= a[j] })
                       static int gap(int[] a, int i, int j) { 0 }
                   }''')],
        // strictlyAscending gives the STRICT gap fact a[i] < a[j].
        [group: 'Sorted helper', name: 'strictlyAscending gives a[i] < a[j] (i<j)', ok: true,
         src: tc('''class C {
                       @Requires({ Sorted.strictlyAscending(a) && 0 <= i && i < j && j < a.length })
                       @Ensures({ a[i] < a[j] })
                       static int gap(int[] a, int i, int j) { 0 }
                   }''')],
        // ascending does NOT entail the STRICT fact (ties allowed) — refutes, keeping the helper honest.
        [group: 'Sorted helper', name: 'ascending does not give STRICT a[i] < a[j]', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                       @Requires({ Sorted.ascending(a) && 0 <= i && i < j && j < a.length })
                       @Ensures({ a[i] < a[j] })
                       static int gap(int[] a, int i, int j) { 0 }
                   }''')],
        // descending mirror: a[i] >= a[j] for i < j.
        [group: 'Sorted helper', name: 'descending gives a[i] >= a[j] (i<j)', ok: true,
         src: tc('''class C {
                       @Requires({ Sorted.descending(a) && 0 <= i && i < j && j < a.length })
                       @Ensures({ a[i] >= a[j] })
                       static int gap(int[] a, int i, int j) { 0 }
                   }''')],
        // List receiver works the same way (List<Integer> element sort is Int). `xs[i]`/`xs[j]` read back
        // as `Integer` inside the contract closure (GROOVY-12071 restored the closure's generic types), so
        // the `<=` type-checks with no cast — nothing to do with the Sorted helper, which type-checks plainly.
        [group: 'Sorted helper', name: 'ascending on List<Integer> gives gap fact', ok: true,
         src: tc('''class C {
                       @Requires({ Sorted.ascending(xs) && 0 <= i && i < j && j < xs.size() })
                       @Ensures({ xs[i] <= xs[j] })
                       static int gap(List<Integer> xs, int i, int j) { 0 }
                   }''')],

        // ---------- Native sortedness idiom — `a.isSorted()` / `a.sorted` (Groovy 6 GDK, native int[]/long[]) ----------
        // `a.isSorted()` is the native, ascending-with-ties GDK predicate (the primitive int[]/long[]
        // overloads are native in the GDK). It lowers to the SAME flat multi-pattern axiom as
        // `Sorted.ascending(a)`, so the gap fact discharges identically — preferred where a native spelling
        // exists. No `import verification.Sorted` needed.
        [group: 'Native isSorted', name: 'int[] a.isSorted() gives gap fact', ok: true,
         src: tc('''class C {
                       @Requires({ a.isSorted() && 0 <= i && i < j && j < a.length })
                       @Ensures({ a[i] <= a[j] })
                       static int gap(int[] a, int i, int j) { 0 }
                   }''')],
        // The boolean-getter property form `a.sorted` is the same predicate (Groovy maps `a.sorted` to the
        // `isSorted()` getter), recognised in the property-access path.
        [group: 'Native isSorted', name: 'int[] a.sorted (property form) gives gap fact', ok: true,
         src: tc('''class C {
                       @Requires({ a.sorted && 0 <= i && i < j && j < a.length })
                       @Ensures({ a[i] <= a[j] })
                       static int gap(int[] a, int i, int j) { 0 }
                   }''')],
        // List receiver, native method + property forms (stock GDK isSorted, no extension needed). The
        // element reads `xs[i]`/`xs[j]` need no cast — generics are restored in the closure (GROOVY-12071).
        [group: 'Native isSorted', name: 'List xs.isSorted() gives gap fact', ok: true,
         src: tc('''class C {
                       @Requires({ xs.isSorted() && 0 <= i && i < j && j < xs.size() })
                       @Ensures({ xs[i] <= xs[j] })
                       static int gap(List<Integer> xs, int i, int j) { 0 }
                   }''')],
        [group: 'Native isSorted', name: 'List xs.sorted (property form) gives gap fact', ok: true,
         src: tc('''class C {
                       @Requires({ xs.sorted && 0 <= i && i < j && j < xs.size() })
                       @Ensures({ xs[i] <= xs[j] })
                       static int gap(List<Integer> xs, int i, int j) { 0 }
                   }''')],
        // Without sortedness the same claim refutes — the native predicate is doing real work.
        [group: 'Native isSorted', name: 'no isSorted => gap fact refutes', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                       @Requires({ 0 <= i && i < j && j < a.length })
                       @Ensures({ a[i] <= a[j] })
                       static int gap(int[] a, int i, int j) { 0 }
                   }''')],

        // ---------- Generic types restored in @Ensures closures (GROOVY-12071) ----------
        // Before GROOVY-12071, a generic-typed accessor inside a re-parsed contract closure erased to
        // `Object`, so *arithmetic* / *ordering* on a tuple slot, map value, or generic-list element
        // wouldn't type-check — forcing `(int)` casts and the "compare in the contract, compute in the
        // body" idiom (and `double[]` instead of `List<Double>`). With the fix the closure keeps the
        // declared generics, so these all type-check bare AND verify. These cases guard that dependency.
        [group: 'GROOVY-12071', name: 'tuple param slot arithmetic (no cast)', ok: true,
         src: tc('''class C {
                       @Requires({ t.v1 == 10 && t.v2 == 20 })
                       @Ensures({ result == t.v1 + t.v2 })
                       static int f(Tuple2<Integer, Integer> t) { 30 }
                   }''')],
        [group: 'GROOVY-12071', name: 'map param value arithmetic (no cast)', ok: true,
         src: tc('''class C {
                       @Requires({ m.x == 3 && m.y == 4 })
                       @Ensures({ result == m.x + m.y })
                       static int f(Map<String, Integer> m) { 7 }
                   }''')],
        [group: 'GROOVY-12071', name: 'nested tuple access in contract (no cast)', ok: true,
         src: tc('''class C {
                       @Requires({ t.v1.v2 == 5 })
                       @Ensures({ result == t.v1.v2 })
                       static int f(Tuple2<Tuple2<Integer, Integer>, Integer> t) { 5 }
                   }''')],
        [group: 'GROOVY-12071', name: 'List<Double> element predicate (no double[] workaround)', ok: true,
         src: tc('''class C {
                       @Requires({ xs != null && xs.size() > 0 && xs[0] >= 0.0d })
                       @Ensures({ result >= 0.0d })
                       static double f(List<Double> xs) { xs[0] }
                   }''')],
        // A wrong slot-arithmetic claim still refutes — the no-cast spec carries real proof obligations.
        [group: 'GROOVY-12071', name: 'tuple param slot arithmetic: wrong claim refutes', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                       @Requires({ t.v1 == 10 && t.v2 == 20 })
                       @Ensures({ result == t.v1 + t.v2 + 1 })
                       static int f(Tuple2<Integer, Integer> t) { 30 }
                   }''')],
    ]

    /** Wrap a class body in the @TypeChecked verification extension + the standard imports. */
    static String tc(String classText) {
        HDR + "@TypeChecked(extensions = 'verification.VerifyChecker')\n" + classText.stripIndent()
    }

    /** Like {@link #tc} but also imports {@code java.util.stream.Stream} (Phase 75 infinite-stream cases). */
    static String tcs(String classText) {
        HDR + 'import java.util.stream.Stream\n' +
            "@TypeChecked(extensions = 'verification.VerifyChecker')\n" + classText.stripIndent()
    }

    static List<String> compile(String name, String src) {
        def gcl = new GroovyClassLoader(Thread.currentThread().contextClassLoader)
        try {
            gcl.parseClass(src, "${name}.groovy")
            return null   // compiled cleanly
        } catch (MultipleCompilationErrorsException e) {
            return e.errorCollector.errors.collect { err ->
                if (err instanceof SyntaxErrorMessage) return err.cause.message
                if (err instanceof ExceptionMessage) {
                    def ex = err.cause
                    def sw = new StringWriter()
                    ex.printStackTrace(new PrintWriter(sw))
                    return "${ex.class.simpleName}: ${ex.message}\n${sw}"
                }
                err.toString()
            }
        } finally {
            try { gcl.close() } catch (ignored) {}
        }
    }

    static void main(String[] args) {
        int passed = 0, failed = 0
        String currentGroup = null
        CASES.eachWithIndex { Map c, int i ->
            if (c.group != currentGroup) {
                currentGroup = c.group
                println "\n── ${currentGroup} ${'─' * (60 - currentGroup.size())}"
            }
            List<String> errors = compile("Case${i}", (String) c.src)
            boolean wantOk = c.ok == true
            boolean ok
            String detail
            if (wantOk) {
                ok = (errors == null)
                detail = ok ? '' : "expected clean compile, got:\n      ${errors?.join('\n      ')}"
            } else {
                String all = errors?.join('\n') ?: ''
                ok = errors != null && all.contains((String) c.expect)
                detail = ok ? '' : (errors == null
                    ? "expected error containing '${c.expect}', but compiled cleanly"
                    : "expected '${c.expect}', got:\n      ${all.replaceAll('\n', '\n      ')}")
                // Optional `refute`: assert a substring is ABSENT from the diagnostic (e.g. an
                // internal/synthetic name that must not leak into a user-facing counterexample).
                if (ok && c.refute && all.contains((String) c.refute)) {
                    ok = false
                    detail = "diagnostic should NOT contain '${c.refute}', but did:\n      ${all.replaceAll('\n', '\n      ')}"
                }
            }
            if (ok) {
                passed++
                println "  [PASS] ${c.name}"
                // VERIFY_VERBOSE=1 ./gradlew verify  → show the diagnostic text of refuted cases
                if (System.getenv('VERIFY_VERBOSE') && !wantOk && errors) {
                    println "         ${errors.join('\n').replaceAll('\n', '\n         ')}"
                }
            } else {
                failed++
                println "  [FAIL] ${c.name}\n      ${detail}"
            }
        }
        println "\n${'═' * 64}"
        println "${passed} passed, ${failed} failed, ${CASES.size()} total"
        if (System.getenv('VERIFY_CACHE_STATS') == '1') {
            long hits   = Z3Backend.vcCacheHits()
            long misses = Z3Backend.vcCacheMisses()
            long total  = hits + misses
            int  size   = Z3Backend.vcCacheSize()
            String pct  = total == 0 ? '—' : sprintf('%.1f%%', 100.0d * hits / total)
            println "VC cache: ${hits} hits / ${misses} misses (${pct} hit rate), ${size} entries"
        }
        if (failed > 0) System.exit(1)
    }
}
