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
        [group: 'P1 bounds', name: 'unguarded index refuted', expect: 'array index in bounds',
         src: tc('class C { static int g(int[] a, int i) { a[i] } }')],
        [group: 'P1 bounds', name: 'guarded index verified', ok: true,
         src: tc('class C { static int g(int[] a, int i) { if (i >= 0 && i < a.length) return a[i]; return -1 } }')],

        // ---------- Phase 1: division ----------
        [group: 'P1 division', name: 'unguarded modulo refuted', expect: 'divisor is non-zero',
         src: tc('class C { static int d(int x, int y) { x % y } }')],
        [group: 'P1 division', name: 'guarded modulo verified', ok: true,
         src: tc('class C { static int d(int x, int y) { if (y != 0) return x % y; return 0 } }')],

        // ---------- Phase 1: null dereference ----------
        [group: 'P1 null', name: 'unguarded deref refuted', expect: 'non-null at this dereference',
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
        [group: 'P5a value-flow', name: 'unconstrained assignment index refuted', expect: 'array index in bounds',
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
        [group: 'P5b loop-fused', name: 'in-loop index unbounded refuted', expect: 'array index in bounds',
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
