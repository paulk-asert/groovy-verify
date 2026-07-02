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
package cases

import static cases.CaseDsl.*

/** 'P71 soundness' — 16 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G195_p71_soundness {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Soundness anchors: a boolean field write is tracked (no crash), a vacuous precondition is flagged.'

    static final List<Map> CASES = [

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
    ]
}
