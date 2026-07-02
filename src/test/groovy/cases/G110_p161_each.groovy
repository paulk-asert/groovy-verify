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

/** 'P161 each' — 13 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G110_p161_each {

    static final List<Map> CASES = [

        // Inline intersection membership reads in a contract (the set-RETURN form is a separate gap).
        [group: 'P161 each', name: 'F each implicit `it` over a list verifies', ok: true,
         src: tc('''class C { @Requires({ a != null && (0..<a.size()).every { a[it] >= 0 } })
                        static void f(java.util.List<Integer> a) { a.each { assert it >= 0 } } }''')],
        [group: 'P161 each', name: 'G each implicit `it` over a list refutes without guard', expect: 'Assertion',
         src: tc('class C { @Requires({ a != null }) static void f(java.util.List<Integer> a) { a.each { assert it >= 0 } } }')],
        // GROOVY-12100 has LANDED (in the 6.0.0-SNAPSHOT this builds against): a *primitive array's* `.each` now
        // propagates its element type to the *implicit* `it`, so `int[].each { it >= 0 }` type-checks and the
        // verifier's implicit-`it` path (cases F/G) applies to arrays too — no verifier change was needed. Unguarded,
        // this refutes exactly like the list case G: `it` resolves to int, the auto bounds loop proves safety, and the
        // missing element guard yields a counterexample (a.size() = 1, a[0] = -1). Before the fix this was a stock
        // @TypeChecked `compareTo` error (`it` inferred as Object), pre-pinned so the case would flip the moment it shipped.
        [group: 'P161 each', name: 'H array implicit `it` refutes without guard (GROOVY-12100 fixed)', expect: 'Assertion',
         src: tc('class C { @Requires({ a != null }) static void f(int[] a) { a.each { assert it >= 0 } } }')],
        [group: 'P161 each', name: 'I eachWithIndex element+index property verifies', ok: true,
         src: tc('''class C { @Requires({ a != null && (0..<a.length).every { a[it] >= 0 } })
                        static void f(int[] a) { a.eachWithIndex { int x, int i -> assert x >= 0 && i >= 0 } } }''')],
        [group: 'P161 each', name: 'J eachWithIndex element refutes without guard', expect: 'Assertion',
         src: tc('class C { @Requires({ a != null }) static void f(int[] a) { a.eachWithIndex { int x, int i -> assert x >= 0 } } }')],
        // The user-named index drives the loop, so the element binds to a[i] and a false claim about the index
        // refutes against its 0 <= i < size bound — both read in counterexamples exactly as the developer wrote them.
        [group: 'P161 each', name: 'K eachWithIndex binds element to a[i]', ok: true,
         src: tc('class C { @Requires({ a != null }) static void f(int[] a) { a.eachWithIndex { int x, int i -> assert x == a[i] } } }')],
        // Unlike `.each`'s implicit `it` (GROOVY-12100), eachWithIndex's two-param closure infers cleanly on a
        // primitive array even *untyped* — STC types the element from the eachWithIndex signature, no annotation needed.
        [group: 'P161 each', name: 'L eachWithIndex untyped params on int[] refute (no GROOVY-12100)', expect: 'Assertion',
         src: tc('class C { @Requires({ a != null }) static void f(int[] a) { a.eachWithIndex { x, i -> assert x >= 0 } } }')],
        [group: 'P161 each', name: 'D each accumulation skips loudly', expect: 'Skipped loop verification',
         src: tc('''class C { @Ensures({ result == a.length })
                        static int f(int[] a) { int c = 0; a.each { int x -> c += 1 }; c } }''')],
        // Companion to D: the SAME accumulation the `.each` can't prove is provable as a classic `for`, because
        // its in-scope index lets you attach the inductive @Invariant (c == i) that frames the accumulator —
        // establishment/preservation/use close the postcondition, @Decreases adds termination. This is the edge
        // of internal iteration: per-element safety is free, but a functional/accumulation result needs an
        // @Invariant, which a `.each` statement can't carry (a statement annotation on a method call won't parse).
        [group: 'P161 each', name: 'D2 same accumulation proven as a for-loop', ok: true,
         src: tc('''class C {
             @Ensures({ result == a.length })
             static int count(int[] a) {
                 int c = 0
                 @Invariant({ c == i && i <= a.length })
                 @Decreases({ a.length - i })
                 for (int i = 0; i < a.length; i++) { c += 1 }
                 c
             }
         }''')],
        [group: 'P161 each', name: 'D3 for-loop accumulation wrong @Ensures refutes', expect: 'postcondition',
         src: tc('''class C {
             @Ensures({ result == a.length + 1 })
             static int count(int[] a) {
                 int c = 0
                 @Invariant({ c == i && i <= a.length })
                 @Decreases({ a.length - i })
                 for (int i = 0; i < a.length; i++) { c += 1 }
                 c
             }
         }''')],
        [group: 'P161 each', name: 'A each per-element property verifies', ok: true,
         src: tc('''class C { @Requires({ a != null && (0..<a.length).every { a[it] >= 0 } })
                        static void f(int[] a) { a.each { int x -> assert x >= 0 } } }''')],
        [group: 'P161 each', name: 'B each per-element refutes without guard', expect: 'Assertion',
         src: tc('class C { @Requires({ a != null }) static void f(int[] a) { a.each { int x -> assert x >= 0 } } }')],
        [group: 'P161 each', name: 'C for-in no-invariant now verifies (relaxation)', ok: true,
         src: tc('''class C { @Requires({ a != null && (0..<a.length).every { a[it] >= 0 } })
                        static void f(int[] a) { for (int x in a) { assert x >= 0 } } }''')],
    ]
}
