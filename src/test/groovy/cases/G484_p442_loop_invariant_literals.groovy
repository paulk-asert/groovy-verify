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

/**
 * 'P442 loop invariant literals' — a loop invariant is a re-parsed contract, so Phase 428 keeps its literals as written
 * where it fails on entry or isn't preserved. A for-in invariant's per-element clauses were shown by their bare
 * `.text`, unquoted: `@Invariant({ x != 'q' })` read `invariant: (x != q)`. They are quoted now, as written: each
 * clause split from the invariant keeps its source text.
 */
class G484_p442_loop_invariant_literals {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 442: a for-in invariant's per-element clause keeps its string literals as written (`invariant: (x != 'q')`), where it read as the bare value (`(x != q)`)."

    static final List<Map> CASES = [

        // It read `invariant: (x != q) && (x != r) && (x != s)`
        [group: "P442 loop invariant literals", name: "a per-element clause keeps each literal as written",
         expect: ["Cannot prove loop invariant holds for every element in f",
                  "invariant: (x != 'q') && (x != \"r\") && (x != /s/)"],
         src: tc('''class A {
                        static void f(List<String> xs) {
                            @Invariant({ x != 'q' && x != "r" && x != /s/ })
                            for (String x : xs) { }
                        }
                    }''')],

        // The x-free clause goes to the loop-head checks; the clause over the element is shown alone
        [group: "P442 loop invariant literals", name: "… split from an x-free clause",
         expect: ["Cannot prove loop invariant holds for every element in f", "invariant: (x != 'q')"],
         src: tc('''class A {
                        static void f(List<String> xs, int n) {
                            @Invariant({ n == n && x != 'q' })
                            for (String x : xs) { }
                        }
                    }''')],

        // Already as written (Phase 428): an invariant that fails on entry, or isn't preserved
        [group: "P442 loop invariant literals", name: "an invariant failing on entry reads as written",
         expect: ["Cannot prove loop invariant holds on entry in f",
                  "invariant: ((((s == 'x') && (s != \"y\")) && (s != /z/)) && (i >= 0))"],
         src: tc('''class A {
                        static int f(String s) {
                            int i = 0
                            @Invariant({ s == 'x' && s != "y" && s != /z/ && i >= 0 })
                            while (i < 3) { i++ }
                            i
                        }
                    }''')],

        [group: "P442 loop invariant literals", name: "… and one not preserved",
         expect: ["Cannot prove loop invariant is preserved by the loop body in f", "invariant: ((t == 'a') && (i >= 0))"],
         src: tc('''class A {
                        static String f() {
                            String t = 'a'
                            int i = 0
                            @Invariant({ t == 'a' && i >= 0 })
                            while (i < 3) { i++; t = "b" }
                            t
                        }
                    }''')],
    ]
}
