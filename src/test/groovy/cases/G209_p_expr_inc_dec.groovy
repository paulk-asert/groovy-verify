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

/** 'P expr inc/dec' — 17 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G209_p_expr_inc_dec {

    static final List<Map> CASES = [

        // ---------- ++ / -- in expression position (variable target) ----------
        // `x = i++` / `a = i++` / `x = ++i`: the side-effecting inc/dec is hoisted out of the assignment
        // into an explicit sequence — post `[x = i, i = i+1]` (old value, then the side effect), pre
        // `[i = i+1, x = i]` (side effect first, then the new value). Operand may be a var, field, or
        // array element. (Array-INDEX position `a[i++]` stays out — its index obligation would need the
        // increment threaded through the obligation passes; it skips loudly.)
        [group: 'P expr inc/dec', name: 'x = i++ value is old i', ok: true,
         src: tc('class C { @Ensures({ result == 5 }) static int f() { int i = 5; int x = i++; return x } }')],
        [group: 'P expr inc/dec', name: 'i++ side effect increments i', ok: true,
         src: tc('class C { @Ensures({ result == 6 }) static int f() { int i = 5; int x = i++; return i } }')],
        [group: 'P expr inc/dec', name: 'x = ++i value is new i', ok: true,
         src: tc('class C { @Ensures({ result == 6 }) static int f() { int i = 5; int x = ++i; return x } }')],
        [group: 'P expr inc/dec', name: 'x = i-- value is old i', ok: true,
         src: tc('class C { @Ensures({ result == 5 }) static int f() { int i = 5; int x = i--; return x } }')],
        [group: 'P expr inc/dec', name: 'x = i++ in a loop body threads correctly', ok: true,
         src: tc('''class C {
                        @Requires({ n >= 0 })
                        @Ensures({ result == n })
                        static int countViaPost(int n) {
                            int i = 0, c = 0
                            @Invariant({ 0 <= i && i <= n && c == i })
                            @Decreases({ n - i })
                            while (i < n) { c = i++; c = c + 1 }
                            return c
                        }
                    }''')],
        // Soundness: x = i++ is the OLD value; claiming the new value refutes.
        [group: 'P expr inc/dec', name: 'x = i++ claims new value refutes', expect: 'Cannot prove postcondition',
         src: tc('class C { @Ensures({ result == 6 }) static int f() { int i = 5; int x = i++; return x } }')],

        // ---------- ++ / -- in array-index position (a[i++]) ----------
        // The index's bounds obligation is collected on the rewritten `a[i]`, and a later access sees the
        // bumped index through the havoc pass's `preceding` thread.
        [group: 'P expr inc/dec', name: 'a[i++] = v stores at old index', ok: true,
         src: tc('''class C {
                        @Requires({ a != null && a.length >= 1 })
                        @Ensures({ a[0] == 9 })
                        static void f(int[] a) { int i = 0; a[i++] = 9 }
                    }''')],
        [group: 'P expr inc/dec', name: 'x = a[i++] reads old index', ok: true,
         src: tc('''class C {
                        @Requires({ a != null && a.length >= 1 && a[0] == 7 })
                        @Ensures({ result == 7 })
                        static int f(int[] a) { int i = 0; int x = a[i++]; return x }
                    }''')],
        [group: 'P expr inc/dec', name: 'a[i++] sequence threads the index', ok: true,
         src: tc('''class C {
                        @Requires({ a != null && a.length >= 2 })
                        @Ensures({ a[0] == 8 && a[1] == 9 })
                        static void f(int[] a) { int i = 0; a[i++] = 8; a[i++] = 9 }
                    }''')],
        // The array-fill idiom `while (i < n) a[i++] = 0` verifies — the store's bounds discharge from the
        // invariant + guard, and the index increments correctly each iteration.
        [group: 'P expr inc/dec', name: 'a[i++] loop array-fill verifies', ok: true,
         src: tc('''class C {
                        @Requires({ a != null && n >= 0 && a.length >= n })
                        static void f(int[] a, int n) {
                            int i = 0
                            @Invariant({ 0 <= i && i <= n })
                            @Decreases({ n - i })
                            while (i < n) { a[i++] = 0 }
                        }
                    }''')],
        // Soundness: an a[i++] store past the length refutes — the bounds obligation sees the real index
        // (and its diagnostic is anchored to the rewritten `a[i]`'s source position, so it isn't dropped).
        [group: 'P expr inc/dec', name: 'a[i++] store out of bounds refutes', expect: 'IndexOutOfBounds',
         src: tc('class C { @Requires({ a != null }) static void f(int[] a) { int i = a.length; a[i++] = 9 } }')],

        // Multiple inc/decs on DISTINCT variables, each used once, hoist soundly (order-independent) — the
        // two-cursor copy `dst[j++] = src[i++]` is the README example (in the `README examples` group).
        // Soundness: when a variable appears TWICE (`i++ + i`), Java advances `i` mid-statement so the 2nd
        // `i` sees the new value (x == 1). The hoist refuses this case (the read comes *after* the inc), so
        // it skips *loudly* — a false `result == 0` is never proven (the old hoist did, unsoundly).
        [group: 'P expr inc/dec', name: 'i++ + i (read after inc) skips loudly, no false proof', expect: 'outside fragment',
         src: tc('class C { @Ensures({ result == 0 }) static int f() { int i = 0; int x = i++ + i; return x } }')],
        // Eval-order route: `dst[i] = src[i++]` — `i` appears twice, but the LHS-index read is evaluated
        // *before* the `i++`, so both read the old `i`. The single-index copy now verifies.
        [group: 'P expr inc/dec', name: 'single-index copy dst[i]=src[i++] verifies (eval-order)', ok: true,
         src: tc('''class C {
                        @Requires({ src != null && dst != null && src.length <= dst.length })
                        @Ensures({ (0..<src.length).every { result[it] == src[it] } })
                        static int[] copy(int[] src, int[] dst) {
                            int i = 0
                            @Invariant({ 0 <= i && i <= src.length && (0..<i).every { dst[it] == src[it] } })
                            @Decreases({ src.length - i })
                            while (i < src.length) { dst[i] = src[i++] }
                            return dst
                        }
                    }''')],
        // `a[i] = i++` — `i` in the LHS index (read, old) and the RHS post-inc (last occurrence): verifies.
        [group: 'P expr inc/dec', name: 'a[i] = i++ stores old value at old index', ok: true,
         src: tc('''class C { @Ensures({ result == 5 }) static int f() {
                        int[] a = new int[10]; int i = 5; a[i] = i++; return a[5] } }''')],
        // Clobber soundness: `i = i++` — Java's store wins, so `i` stays 0. The inc target equals the write
        // target, so the hoist refuses it (a hoisted `i = i+1` after would wrongly make it 1): skips loudly.
        [group: 'P expr inc/dec', name: 'i = i++ (self-assign clobber) skips loudly', expect: 'outside fragment',
         src: tc('class C { @Ensures({ result == 0 }) static int f() { int i = 0; i = i++; return i } }')],
        // Pre-increment in the RHS: `++i` hoists *before*, so every read sees the new value. `x = ++i + i`
        // (i: 5 -> 6, then 6 + 6) is sound because `++i` is the FIRST occurrence: verifies result == 12.
        [group: 'P expr inc/dec', name: 'x = ++i + i (pre, first occurrence) verifies', ok: true,
         src: tc('class C { @Ensures({ result == 12 }) static int f() { int i = 5; int x = ++i + i; return x } }')],
        // Pre-increment with the LHS index reading first: `dst[i] = src[++i]` — Java evaluates the LHS index
        // `i` (old) before the RHS `++i`. Phase 127 snapshots the index into a fresh local, so the store lands
        // at `dst[3]` while the read advances to `src[4]`; `dst[3] == src[4] == 99` verifies.
        [group: 'P expr inc/dec', name: 'dst[i] = src[++i] (read before pre) snapshots and verifies', ok: true,
         src: tc('''class C { @Ensures({ result == 99 }) static int f() {
                        int[] dst = new int[10]; int[] src = new int[10]; src[4] = 99; int i = 3
                        dst[i] = src[++i]; return dst[3] } }''')],
    ]
}
