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
 * 'P347 a call is framed by its writes' — a same-class call used as a value dropped its side effects: a contract-free
 * method was a pure function merely for having no contract (PureEvaluator.resolve), and a contracted one with no
 * @Modifies was read as writing nothing, unchecked. The hybrid frame: a declared @Modifies wins (frame-checked, so
 * trusting it is sound; @Modifies({ [] }) is "nothing"), a method with a body and no @Modifies gets its frame
 * inferred from the body (VerifyChecker.calleeWrites, transitive through same-class calls), and a body whose writes
 * can't be bounded makes the call skip loudly. Calls in expressions, in loop bodies and as statements are all framed.
 */
class G391_p347_call_frames {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Phase 347 a call is framed by its writes: a declared @Modifies wins (@Modifies({ [] }) means nothing is written), a callee with a body and no @Modifies has its frame inferred from the body (fields it assigns, parameters it stores into or mutates, transitively through same-class calls), and a body whose writes cannot be bounded makes the call skip loudly. A contract-free method is a pure function only when its inferred frame is empty. Fixed (unsound before): a call used as a value dropped its writes, so `int s = bump()` kept count == 0 past `count = 99`, in straight-line code and loop bodies.'

    static final List<Map> CASES = [

        // twice(n) unfolds as before: the inferred frame is empty.
        [group: 'P347 a call is framed by its writes', name: 'a contract-free helper that writes nothing is still a function', ok: true,
         src: tc('''class C {
                        static int twice(int x) { x * 2 }
                        @Requires({ n >= 0 })
                        @Ensures({ result == 2 * n })
                        static int f(int n) {
                            int s = twice(n)
                            return s
                        }
                    }''')],
        // bump() writes `other`; its inferred frame is {other}, so count == 0 survives the call.
        [group: 'P347 a call is framed by its writes', name: 'a contract-free writer leaves the fields it does not write alone', ok: true,
         src: tc('''final class C {
                        int count = 0
                        int other = 0
                        int bump() { other = 99; return 1 }
                        @Requires({ count == 0 })
                        @Ensures({ count == 0 })
                        void f() {
                            int s = bump()
                        }
                    }''')],
        [group: 'P347 a call is framed by its writes', name: 'the same in a loop body', ok: true,
         src: tc('''final class C {
                        int count = 0
                        int other = 0
                        int bump() { other = other + 1; return 1 }
                        @Requires({ n >= 0 && count == 0 })
                        @Ensures({ count == 0 })
                        void f(int n) {
                            int s = 0
                            int i = 0
                            @Invariant({ 0 <= i && i <= n && count == 0 })
                            @Decreases({ n - i })
                            while (i < n) {
                                s = s + bump()
                                i = i + 1
                            }
                        }
                    }''')],
        // groovy-contracts rejects an empty closure (@Modifies({})), so the empty list is the spelling that compiles.
        [group: 'P347 a call is framed by its writes', name: '@Modifies({ [] }) declares that nothing is written', ok: true,
         src: tc('''class C {
                        int count = 0
                        @Modifies({ [] })
                        int peek() { count }
                        @Requires({ count == 0 })
                        @Ensures({ count == 0 && result >= 0 })
                        int f() {
                            int s = peek()
                            return s >= 0 ? s : 0
                        }
                    }''')],
        [group: 'P347 a call is framed by its writes', name: 'a @Requires-only helper as a value writes nothing, returns an opaque value', ok: true,
         src: tc('''class C {
                        @Requires({ x >= 0 })
                        static int half(int x) { x.intdiv(2) }
                        @Requires({ n >= 0 && a != null && a.length > 0 && a[0] == 7 })
                        @Ensures({ a[0] == 7 })
                        static void f(int n, int[] a) {
                            int s = half(n)
                        }
                    }''')],
        // Unsound before: a callee with no @Modifies was read as writing nothing, so `int s = bump()` kept count == 0 past `count = 99`.
        [group: 'P347 a call is framed by its writes', name: 'a contracted writer with no @Modifies is framed by its body', expect: ['Cannot prove postcondition', 'count (after a call)', 'fails on: f()'],
         src: tc('''final class C {
                        int count = 0
                        @Ensures({ result == 1 })
                        int bump() { count = 99; return 1 }
                        @Requires({ count == 0 })
                        @Ensures({ count == 0 })
                        void f() {
                            int s = bump()
                        }
                    }''')],
        [group: 'P347 a call is framed by its writes', name: 'the same as a statement', expect: ['Cannot prove postcondition', 'fails on: f()'],
         src: tc('''final class C {
                        int count = 0
                        @Ensures({ result == 1 })
                        int bump() { count = 99; return 1 }
                        @Requires({ count == 0 })
                        @Ensures({ count == 0 })
                        void f() {
                            bump()
                        }
                    }''')],
        // `int s = 2 + bump()`: the call is hoisted to a framed local, as a return expression's calls are.
        [group: 'P347 a call is framed by its writes', name: 'the same inside an expression', expect: ['Cannot prove postcondition', 'fails on: f()'],
         src: tc('''final class C {
                        int count = 0
                        @Ensures({ result == 1 })
                        int bump() { count = 99; return 1 }
                        @Requires({ count == 0 })
                        @Ensures({ count == 0 })
                        void f() {
                            int s = 2 + bump()
                        }
                    }''')],
        [group: 'P347 a call is framed by its writes', name: 'a reassignment whose right-hand side calls the writer', expect: ['Cannot prove postcondition', 'fails on: f()'],
         src: tc('''final class C {
                        int count = 0
                        int bump() { count = 99; return 1 }
                        @Requires({ count == 0 })
                        @Ensures({ count == 0 })
                        void f() {
                            int s = 0
                            s = s + bump()
                        }
                    }''')],
        // The frame is transitive: bump() calls reset(), which writes count.
        [group: 'P347 a call is framed by its writes', name: 'a write reached through a helper the callee calls', expect: ['Cannot prove postcondition', 'fails on: f()'],
         src: tc('''final class C {
                        int count = 0
                        private void reset() { count = 99 }
                        @Ensures({ result == 1 })
                        int bump() { reset(); return 1 }
                        @Requires({ count == 0 })
                        @Ensures({ count == 0 })
                        void f() {
                            int s = bump()
                        }
                    }''')],
        // Unsound before: clobber(a) was a pure function to the encoder, so a[0] == 0 survived a[0] = -1.
        [group: 'P347 a call is framed by its writes', name: 'a contract-free call that stores into an array parameter', expect: ['Cannot prove postcondition', 'fails on: f(new int[1])'],
         src: tc('''class C {
                        static int clobber(int[] a) { if (a.length > 0) a[0] = -1; return 0 }
                        @Requires({ a != null && a.length > 0 && a[0] == 0 })
                        @Ensures({ a[0] == 0 })
                        static void f(int[] a) {
                            int s = clobber(a)
                        }
                    }''')],
        [group: 'P347 a call is framed by its writes', name: 'a contracted one too', expect: ['Cannot prove postcondition', 'fails on: f(new int[1])'],
         src: tc('''class C {
                        @Requires({ a != null && a.length > 0 })
                        @Ensures({ result == 0 })
                        static int clobber(int[] a) { a[0] = -1; return 0 }
                        @Requires({ a != null && a.length > 0 && a[0] == 0 })
                        @Ensures({ a[0] == 0 })
                        static void f(int[] a) {
                            int s = clobber(a)
                        }
                    }''')],
        [group: 'P347 a call is framed by its writes', name: 'a declared @Modifies wins, and is framed as before', expect: ['Cannot prove postcondition', 'fails on: f()'],
         src: tc('''class C {
                        int count = 0
                        @Modifies({ this.count })
                        @Ensures({ result == 1 })
                        int bump() { count = 99; return 1 }
                        @Requires({ count == 0 })
                        @Ensures({ count == 0 })
                        void f() {
                            int s = bump()
                        }
                    }''')],
        [group: 'P347 a call is framed by its writes', name: 'a declared frame the body breaks is refused', expect: "writes 'count', which is not in its @Modifies clause []",
         src: tc('''class C {
                        int count = 0
                        @Modifies({ [] })
                        @Ensures({ result == 1 })
                        int bump() { count = 99; return 1 }
                    }''')],
        // Unsound before: `s = s + bump()` havocked s and nothing else, so count == 0 was preserved.
        [group: 'P347 a call is framed by its writes', name: 'a writer called as a value in a loop body', expect: ['Cannot prove loop invariant is preserved', 'fails on: f(1)'],
         src: tc('''final class C {
                        int count = 0
                        int bump() { count = 99; return 1 }
                        @Requires({ n >= 0 && count == 0 })
                        @Ensures({ count == 0 })
                        void f(int n) {
                            int s = 0
                            int i = 0
                            @Invariant({ 0 <= i && i <= n && count == 0 })
                            @Decreases({ n - i })
                            while (i < n) {
                                s = s + bump()
                                i = i + 1
                            }
                        }
                    }''')],
        [group: 'P347 a call is framed by its writes', name: 'a static writer in a loop body', expect: ['Cannot prove loop invariant is preserved', 'fails on: f(1, new int[0])'],
         src: tc('''class C {
                        static int count = 0
                        static int bump() { count = 99; return 1 }
                        @Requires({ n >= 0 })
                        @Ensures({ result >= 0 })
                        static int f(int n, int[] a) {
                            int s = 0
                            int i = 0
                            @Invariant({ 0 <= i && i <= n && s >= 0 })
                            @Decreases({ n - i })
                            while (i < n) {
                                s = s + bump()
                                i = i + 1
                            }
                            return s
                        }
                    }''')],
        [group: 'P347 a call is framed by its writes', name: 'an array parameter written by a call in a loop body', expect: ['Cannot prove loop invariant is preserved', 'fails on: f(1, new int[1])'],
         src: tc('''class C {
                        static int clobber(int[] a) { if (a.length > 0) a[0] = -1; return 0 }
                        @Requires({ a != null && a.length > 0 && a[0] == 0 && n >= 0 })
                        @Ensures({ a[0] == 0 })
                        static void f(int n, int[] a) {
                            int s = 0
                            int i = 0
                            @Invariant({ 0 <= i && i <= n && a[0] == 0 })
                            @Decreases({ n - i })
                            while (i < n) {
                                s = s + clobber(a)
                                i = i + 1
                            }
                        }
                    }''')],
        // A same-class static call statement is a StaticMethodCallExpression after STC; the loop engine took only the instance form.
        [group: 'P347 a call is framed by its writes', name: 'the same as a statement', expect: ['Cannot prove loop invariant is preserved', 'fails on: f(1, new int[1])'],
         src: tc('''class C {
                        static int clobber(int[] a) { if (a.length > 0) a[0] = -1; return 0 }
                        @Requires({ a != null && a.length > 0 && a[0] == 0 && n >= 0 })
                        @Ensures({ a[0] == 0 })
                        static void f(int n, int[] a) {
                            int i = 0
                            @Invariant({ 0 <= i && i <= n && a[0] == 0 })
                            @Decreases({ n - i })
                            while (i < n) {
                                clobber(a)
                                i = i + 1
                            }
                        }
                    }''')],
        // A multiple assignment is a construct the collector doesn't follow: it gives up, and the caller is told so rather
        // than given an opaque result (whose frame would be a guess). (Used `l << x` until Phase 349 bounded `<<`.)
        [group: 'P347 a call is framed by its writes', name: 'a callee whose writes can\'t be bounded skips loudly', expect: ["whose writes can't be bounded from its body: multiple assignment 'def (a, b) = [x, x]'", "declare @Modifies on weird"],
         src: tc('''class C {
                        static int count = 0
                        static int weird(int x) { def (a, b) = [x, x]; count = a + b; return x }
                        @Requires({ n >= 0 })
                        @Ensures({ result == n })
                        static int f(int n) {
                            int s = weird(n)
                            return s
                        }
                    }''')],
    ]
}
