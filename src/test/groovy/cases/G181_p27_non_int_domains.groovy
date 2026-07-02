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

/** 'P27 non-int domains' — 33 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G181_p27_non_int_domains {

    static final List<Map> CASES = [

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
}
