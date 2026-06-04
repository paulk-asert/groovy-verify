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
        // ---------- Phase 14: the verified sort — sorted AND a permutation, soundly ----------
        // insert threads a ghost upper bound `hi` (the recursion passes the pivot a[m] as the new,
        // tight bound), a ghost count value `v` (permutation), and frames the suffix it doesn't touch.
        [group: 'P14 sort', name: 'insertion sort: sorted AND permutation', ok: true,
         src: tc('''class C {
                       int[] a
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
        // Sets.bounded(s, n) ≜ s ⊆ [0,n): |s| <= n, and full iff it covers the domain. This is the
        // bridge the uninterpreted cardinality (Phase 16) lacked — relating |s| to actual membership.
        // FULL ⟹ MEMBER: a bounded set of size n contains every node of the domain (pigeonhole).
        [group: 'P19 cardinality', name: 'full bounded set covers the domain', ok: true,
         src: tc('''class C {
                        @Requires({ Sets.bounded(s, n) && s.size() == n && 0 <= u && u < n })
                        @Ensures({ u in s })
                        static int f(Set<Integer> s, int n, int u) { 0 }
                    }''')],
        // Soundness: without Sets.bounded there is no link from size to membership → cannot conclude u in s.
        [group: 'P19 cardinality', name: 'coverage needs the bound (refuted)', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Requires({ s.size() == n && 0 <= u && u < n })
                        @Ensures({ u in s })
                        static int f(Set<Integer> s, int n, int u) { 0 }
                    }''')],
        // The size bound itself: a domain-bounded set has at most n elements.
        [group: 'P19 cardinality', name: 'bounded set size is at most n', ok: true,
         src: tc('''class C {
                        @Requires({ Sets.bounded(s, n) })
                        @Ensures({ s.size() <= n })
                        static int f(Set<Integer> s, int n) { 0 }
                    }''')],
        // HOLE ⟹ NOT FULL: a bounded set missing a domain element has size < n — exactly the fact a
        // cardinality-terminating DFS needs at its coverage branch (an unvisited in-domain node ⟹ room remains).
        [group: 'P19 cardinality', name: 'a hole means the set is not full', ok: true,
         src: tc('''class C {
                        @Requires({ Sets.bounded(s, n) && 0 <= u && u < n && !(u in s) })
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
        // count to actual membership (the direction `Sets.bounded`'s pigeonhole gives), proved by induction
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
                err instanceof SyntaxErrorMessage ? err.cause.message : err.toString()
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
        if (failed > 0) System.exit(1)
    }
}
