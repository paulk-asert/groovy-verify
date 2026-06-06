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
        // The native idiom works in @Invariant too — no `verification.Forall.range` FQN, no typed
        // index param: the same zero-fill proof the Forall helper needed warts for, written plainly.
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
                           @Invariant({ 0 <= i && i <= n && verification.Forall.range(0, i, { int j -> a[j] == 0 }) })
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
                           @Invariant({ 0 <= i && i <= n && verification.Forall.range(0, i, { int j -> a[j] == 0 }) })
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

        // ---------- Regression: loops ----------
        [group: 'regression loop', name: 'countUp verified', ok: true,
         src: tc('''class C {
                       @Requires({ n >= 0 })
                       @Ensures({ result == n })
                       static int countUp(int n) {
                           int i = 0
                           @Invariant({ 0 <= i && i <= n })
                           @Decreases({ n - i })
                           while (i < n) { i = i + 1 }
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
        // Step 5 — an invariant whose body is outside the encoder fragment (a String method call
        // on a non-numeric receiver) is dropped with a single "Skipped class invariant" diagnostic
        // at the method level. Verification continues for everything else.
        [group: 'P15a class-invariant', name: 'unmodelled invariant skipped',
         expect: 'Skipped class invariant',
         src: tc('''@groovy.contracts.Invariant({ name.length() > 0 })
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
                        @Ensures({ !(Perm.WRITE in required) || Perm.WRITE in grants[Role.ADMIN] })
                        static int adminMayWrite(Map<Role, Set<Perm>> grants, Set<Perm> required) { 0 }
                    }''')],
        // Soundness anchor: without the containsAll precondition, the postcondition refutes.
        [group: 'P36 nested map<set>', name: 'README RBAC: refutes without containsAll',
         expect: 'Cannot prove postcondition',
         src: tc('''class Acl {
                        enum Role { ADMIN, USER, GUEST }
                        enum Perm { READ, WRITE, DELETE }
                        @Ensures({ !(Perm.WRITE in required) || Perm.WRITE in grants[Role.ADMIN] })
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

        // ---------- HumanEval port — filter_by_prefix (Verus task 029) ----------
        // The Verus original is spec-free (only implicit overflow). groovy-verify ports the same
        // body and adds the natural size-bound spec: result.size() <= xs.size(). startsWith routes
        // through the P46a uninterpreted predicate; the spec doesn't try to relate startsWith to
        // string content, just that the conditional filter doesn't add more than it iterates —
        // the same invariant shape as get_positive (Verus 030), with startsWith(xs[i], prefix)
        // substituted for xs[i] > 0.
        [group: 'HumanEval port', name: 'filter_by_prefix (Verus 029): result.size() <= xs.size()', ok: true,
         src: tc('''class C {
                        @Requires({ xs != null && prefix != null &&
                                    Forall.range(0, xs.size()) { i -> xs[i] != null } })
                        @Ensures({ result.size() <= xs.size() })
                        static List<String> filterByPrefix(List<String> xs, String prefix) {
                            List<String> result = []
                            int i = 0
                            @Invariant({ result != null && 0 <= i && i <= xs.size() && result.size() <= i })
                            @Decreases({ xs.size() - i })
                            while (i < xs.size()) {
                                if (xs[i].startsWith(prefix)) {
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
                        @Requires({ !(x in s) })
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
        // to `s` (the guard `!(x in s)` makes it fresh), so the measure `n - s.size()` strictly decreases —
        // a finite recursion over a bounded domain (the DFS-shaped termination argument), proved with no
        // quantifier. Termination + the recursion's own well-foundedness, end to end.
        [group: 'P16 sets', name: 'set-cardinality decreases measure', ok: true,
         src: tc('''class C { Set<Integer> s; int n
                        @Modifies({ this.s })
                        @Decreases({ n - s.size() })
                        void fill(int x) {
                            if (!(x in s) && s.size() < n) {
                                s.add(x)
                                fill(x + 1)
                            }
                        }
                    }''')],
        // Soundness: drop the freshness guard `!(x in s)` and the added element may already be present,
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
                        @Ensures({ (0..<n).every { !(it in old.visited) || (it in visited) } &&
                                   (fuel <= 0 || (u in visited)) })
                        void visit(int u, int fuel) {
                            if (fuel > 0 && !(u in visited)) {
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
                            if (fuel > 0 && !(u in visited)) {
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
                        @Ensures({ (0..<n).every { !(it in old.visited) || (it in visited) } })
                        void visit(int u) {
                            if (!(u in visited) && visited.size() < n) {
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
                        @Ensures({ (0..<n).every { !(it in old.visited) || (it in visited) } })
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
                        @Requires({ Sets.boundedBy(s, n) && 0 <= u && u < n && !(u in s) })
                        @Ensures({ s.size() < n })
                        static int f(Set<Integer> s, int n, int u) { 0 }
                    }''')],
        // Soundness: without the bound, a missing element says nothing about the (uninterpreted) size.
        [group: 'P19 cardinality', name: 'hole needs the bound (refuted)', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Requires({ 0 <= u && u < n && !(u in s) })
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
                        @Requires({ 0 <= u && u < k && !(u in s) })
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
                                   (0..<n).every { !(it in old.visited) || (it in visited) } })
                        void visit(int u) {
                            if (!(u in visited) && Sets.boundedCount(visited, n) < n) {
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
                            if (!(u in visited) && Sets.boundedCount(visited, n) < n) {
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
                                    (0..<n).every { !(it in visited) || (next[it] in visited) } })
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
                                    (0..<n).every { !(it in visited) || (next[it] in visited) } })
                        @Modifies({ this.visited })
                        @Ensures({ (0..<n).every { !(it in visited) || (next[it] in visited) } })
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
                                    (0..<n).every { !(it in visited) || (next[it] in visited) } })
                        @Modifies({ this.visited })
                        @Decreases({ n - Sets.boundedCount(visited, n) })
                        @Ensures({ (0..<n).every { !(it in visited) || (next[it] in visited) } })
                        void visit(int u) {
                            if (!(u in visited) && Sets.boundedCount(visited, n) < n) {
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
                                    (0..<n).every { !(it in visited) || (next[it] in visited) } })
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
                                    (0..<n).every { !(it in visited) || (it in onStack) || (next[it] in visited) } &&
                                    (0..<n).every { !(it in onStack) || (it in visited) } })
                        @Modifies({ [this.visited, this.onStack] })
                        @Decreases({ n - Sets.boundedCount(visited, n) })
                        @Ensures({ (u in visited) &&
                                   (0..<n).every { !(it in visited) || (it in onStack) || (next[it] in visited) } &&
                                   (0..<n).every { !(it in onStack) || (it in visited) } &&
                                   (0..<n).every { (it in onStack) == (it in old.onStack) } &&
                                   (0..<n).every { !(it in old.visited) || (it in visited) } })
                        void visit(int u) {
                            if (!(u in visited) && Sets.boundedCount(visited, n) < n) {
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
                                    (0..<n).every { !(it in visited) } &&
                                    (0..<n).every { !(it in onStack) } })
                        @Modifies({ [this.visited, this.onStack] })
                        @Ensures({ (0..<n).every { !(it in visited) || (next[it] in visited) } })
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
    ]

    /** Wrap a class body in the @TypeChecked verification extension + the standard imports. */
    static String tc(String classText) {
        HDR + "@TypeChecked(extensions = 'verification.VerifyChecker')\n" + classText.stripIndent()
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
                    def sw = new java.io.StringWriter()
                    ex.printStackTrace(new java.io.PrintWriter(sw))
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
            long hits   = verification.Z3Backend.vcCacheHits()
            long misses = verification.Z3Backend.vcCacheMisses()
            long total  = hits + misses
            int  size   = verification.Z3Backend.vcCacheSize()
            String pct  = total == 0 ? '—' : sprintf('%.1f%%', 100.0d * hits / total)
            println "VC cache: ${hits} hits / ${misses} misses (${pct} hit rate), ${size} entries"
        }
        if (failed > 0) System.exit(1)
    }
}
