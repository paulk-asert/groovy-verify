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

/** 'P-fizzbuzz' — 8 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G129_p_fizzbuzz {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Element-wise FizzBuzz array-fill correctness; an off-by-one surfaces the offending element value.'

    static final List<Map> CASES = [
        // The other-direction off-by-one (`spec(i)` not `spec(i+1)`): slot 0 gets spec(0) = FizzBuzz (0 is
        // divisible by everything), so the surfaced element renders the actual emoji — Z3 mangles a supplementary
        // char on the string round-trip; the renderer decodes the `\\u{…}` escapes and drops the artifact surrogates.
        [group: 'P-fizzbuzz', name: 'off-by-one surfaces the emoji element value', ok: false,
         // Build the expected emoji from code points (not a source literal): a supplementary char in a Groovy
         // string literal can carry a stray orphan surrogate, which made this assertion brittle against the
         // (now canonicalised) Z3 counterexample rendering. U+1F964 🥤, U+1F41D 🐝.
         expect: 'r[0] = "' + new String(Character.toChars(0x1F964)) + new String(Character.toChars(0x1F41D)) + '" — the spec requires "1"',
         src: tc('''class FizzBuzz {
                        @Ensures({ result == (n % 15 == 0 ? '🥤🐝' : (n % 3 == 0 ? '🥤' : (n % 5 == 0 ? '🐝' : n.toString()))) })
                        static String spec(int n) { n % 15 == 0 ? '🥤🐝' : (n % 3 == 0 ? '🥤' : (n % 5 == 0 ? '🐝' : n.toString())) }
                        @Requires({ upTo >= 1 })
                        @Ensures({ (0..<upTo).every { int k -> result[k] == FizzBuzz.spec(k + 1) } })
                        static String[] build(int upTo) {
                            String[] r = new String[upTo]
                            int i = 0
                            @Invariant({ 0 <= i && i <= upTo && r.length == upTo && (0..<i).every { int k -> r[k] == FizzBuzz.spec(k + 1) } })
                            @Decreases({ upTo - i })
                            while (i < upTo) { r[i] = FizzBuzz.spec(i); i = i + 1 }
                            return r
                        }
                    }''')],
        // ---------- Phases 122/123/124: FizzBuzz array-fill (a Dafny-style element-wise verification) ----------
        // The classic verified array-fill: a pure `spec(n)` function, an imperative loop that fills `r[i] = spec(i+1)`,
        // and an element-wise postcondition `forall k. r[k] == spec(k+1)`. groovy-verify proves the length, the
        // termination (@Decreases), and that EVERY element matches the spec — over a String-valued array (the
        // local `new String[upTo]` element-store needed the Phase-123 fix). `spec`'s @Ensures inlines equationally
        // (Phase 116) so body and invariant share one deterministic spec term; emoji literals are captured via
        // GROOVY-12085. The non-spec/buzz default outputs the NUMBER via `n.toString()` — Phase 124 models
        // `n.toString()` / `String.valueOf(n)` / `Integer.toString(n)` as Z3's deterministic intToString, and
        // lets such a conversion live in an equational-combiner `@Ensures` (so the helper still inlines into the
        // loop invariant). This is the full pretty FizzBuzz, numbers and all, machine-checked element by element:
        [group: 'P-fizzbuzz', name: 'FizzBuzz array-fill with number default (n.toString)', ok: true,
         src: tc('''class FizzBuzz {
                        @SelfEnsures   // the body *is* the spec — lifted into @Ensures({ result == <body> }), written once
                        static String spec(int n) { n % 15 == 0 ? '🥤🐝' : (n % 3 == 0 ? '🥤' : (n % 5 == 0 ? '🐝' : n.toString())) }
                        @Requires({ upTo >= 1 })
                        @Ensures({ result.length == upTo })   // exactly the size requested
                        @Ensures({ (0..<upTo).every { int k -> result[k] == FizzBuzz.spec(k + 1) } })   // every element provably correct
                        static String[] build(int upTo) {
                            String[] r = new String[upTo]
                            int i = 0
                            @Invariant({ 0 <= i && i <= upTo && r.length == upTo && (0..<i).every { int k -> r[k] == FizzBuzz.spec(k + 1) } })
                            @Decreases({ upTo - i })
                            while (i < upTo) { r[i] = FizzBuzz.spec(i + 1); i = i + 1 }
                            return r
                        }
                    }
                    // build(20) == [1, 2, 🥤, 4, 🐝, 🥤, 7, 8, 🥤, 🐝, 11, 🥤, 13, 14, 🥤🐝, 16, 17, 🥤, 19, 🐝]''')],
        // The same proof through String.valueOf(n) and Integer.toString(n) — all three forms route to intToString.
        [group: 'P-fizzbuzz', name: 'number default via String.valueOf', ok: true,
         src: tc('''class FizzBuzz {
                        @Ensures({ result == (n % 15 == 0 ? '🥤🐝' : (n % 3 == 0 ? '🥤' : (n % 5 == 0 ? '🐝' : String.valueOf(n)))) })
                        static String spec(int n) { n % 15 == 0 ? '🥤🐝' : (n % 3 == 0 ? '🥤' : (n % 5 == 0 ? '🐝' : String.valueOf(n))) }
                        @Requires({ upTo >= 1 })
                        @Ensures({ (0..<upTo).every { int k -> result[k] == FizzBuzz.spec(k + 1) } })
                        static String[] build(int upTo) {
                            String[] r = new String[upTo]
                            int i = 0
                            @Invariant({ 0 <= i && i <= upTo && r.length == upTo && (0..<i).every { int k -> r[k] == FizzBuzz.spec(k + 1) } })
                            @Decreases({ upTo - i })
                            while (i < upTo) { r[i] = FizzBuzz.spec(i + 1); i = i + 1 }
                            return r
                        }
                    }''')],
        // The off-by-one Dafny warns about: write `spec(i+2)` and the element-wise postcondition refutes.
        [group: 'P-fizzbuzz', name: 'FizzBuzz off-by-one (i+2) refutes, naming the wrong slot', ok: false, expect: 'r[0] = "2" — the spec requires "1"',
         src: tc('''class FizzBuzz {
                        @Ensures({ result == (n % 15 == 0 ? '🥤🐝' : (n % 3 == 0 ? '🥤' : (n % 5 == 0 ? '🐝' : n.toString()))) })
                        static String spec(int n) { n % 15 == 0 ? '🥤🐝' : (n % 3 == 0 ? '🥤' : (n % 5 == 0 ? '🐝' : n.toString())) }
                        @Requires({ upTo >= 1 })
                        @Ensures({ (0..<upTo).every { int k -> result[k] == FizzBuzz.spec(k + 1) } })
                        static String[] build(int upTo) {
                            String[] r = new String[upTo]
                            int i = 0
                            @Invariant({ 0 <= i && i <= upTo && r.length == upTo && (0..<i).every { int k -> r[k] == FizzBuzz.spec(k + 1) } })
                            @Decreases({ upTo - i })
                            while (i < upTo) { r[i] = FizzBuzz.spec(i + 2); i = i + 1 }
                            return r
                        }
                    }''')],
        // A loop-BOUND off-by-one (`i <= upTo`) overruns the array — caught as a bounds violation with a
        // self-explanatory counterexample (`i = 1, r.length = 1`), distinct from the value off-by-one above.
        [group: 'P-fizzbuzz', name: 'loop-bound off-by-one (i <= upTo) is an out-of-bounds write', ok: false, expect: 'IndexOutOfBoundsException',
         src: tc('''class FizzBuzz {
                        @Ensures({ result == (n % 15 == 0 ? '🥤🐝' : (n % 3 == 0 ? '🥤' : (n % 5 == 0 ? '🐝' : n.toString()))) })
                        static String spec(int n) { n % 15 == 0 ? '🥤🐝' : (n % 3 == 0 ? '🥤' : (n % 5 == 0 ? '🐝' : n.toString())) }
                        @Requires({ upTo >= 1 })
                        @Ensures({ result.length == upTo })
                        static String[] build(int upTo) {
                            String[] r = new String[upTo]
                            int i = 0
                            @Invariant({ 0 <= i && i <= upTo && r.length == upTo })
                            @Decreases({ upTo - i })
                            while (i <= upTo) { r[i] = FizzBuzz.spec(i + 1); i = i + 1 }
                            return r
                        }
                    }''')],
        // The number itself is checked, not just the emoji: a wrong number default ((n+1).toString) refutes.
        [group: 'P-fizzbuzz', name: 'wrong number default refutes', ok: false, expect: 'Cannot prove',
         src: tc('''class FizzBuzz {
                        @Ensures({ result == (n % 15 == 0 ? '🥤🐝' : (n % 3 == 0 ? '🥤' : (n % 5 == 0 ? '🐝' : n.toString()))) })
                        static String spec(int n) { n % 15 == 0 ? '🥤🐝' : (n % 3 == 0 ? '🥤' : (n % 5 == 0 ? '🐝' : (n + 1).toString())) }
                        @Requires({ upTo >= 1 })
                        @Ensures({ (0..<upTo).every { int k -> result[k] == FizzBuzz.spec(k + 1) } })
                        static String[] build(int upTo) {
                            String[] r = new String[upTo]
                            int i = 0
                            @Invariant({ 0 <= i && i <= upTo && r.length == upTo && (0..<i).every { int k -> r[k] == FizzBuzz.spec(k + 1) } })
                            @Decreases({ upTo - i })
                            while (i < upTo) { r[i] = FizzBuzz.spec(i + 1); i = i + 1 }
                            return r
                        }
                    }''')],
        // Phase 124 — the spurious null-deref on a primitive receiver (`int n`) is suppressed: n.toString() proves.
        [group: 'P-fizzbuzz', name: 'n.toString on a primitive receiver (no spurious null obligation)', ok: true,
         src: tc('''class T {
                        @Ensures({ result == n.toString() })
                        static String f(int n) { n.toString() }
                    }''')],
        // Phase 123 regression — a String store into a locally-`new`'d String[] (defaulted to Int sort before).
        [group: 'P-fizzbuzz', name: 'String[] local-array element store (Phase 123)', ok: true,
         src: tc('''class T {
                        @Requires({ n >= 1 })
                        @Ensures({ result == 'hi' })
                        static String make(int n) { String[] a = new String[n]; a[0] = 'hi'; return a[0] }
                    }''')],
    ]
}
