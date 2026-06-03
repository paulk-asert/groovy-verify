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
        import verification.Forall
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
