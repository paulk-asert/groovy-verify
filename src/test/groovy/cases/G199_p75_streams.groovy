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

/** 'P75 streams' — 9 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G199_p75_streams {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Bounded infinite-stream every/any over Stream.iterate(...).limit(n): a literal limit unrolls, a property of every element proves by induction, a witness for any.'

    static final List<Map> CASES = [

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
    ]
}
